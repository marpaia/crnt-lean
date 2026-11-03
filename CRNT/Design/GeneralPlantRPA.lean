import CRNT.Design.AntitheticMeanOutput
import CRNT.Stochastic.HarrisTheorem
import CRNT.Stochastic.FosterRecurrence
import CRNT.Stochastic.NetworkFosterErgodic
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# General-plant setpoints and conditional stability/ergodicity certificates

A linear plant and its integral/leaky feedback models yield equilibrium setpoint
identities. Lyapunov and Foster certificate transfers require the displayed
matrix, drift, nonnegativity and integrability data. This does not establish
stochastic ergodicity for an arbitrary plant solely from its interface. The
concrete production/degradation and molecular antithetic instances are separate
results.
-/

open Filter
open scoped BigOperators Topology Matrix

namespace CRNT
namespace Design
namespace GeneralPlant

/-! ## The general plant -/

/-- A finite-dimensional linear plant `ẋ = A x + B u`, `y = C x`. -/
structure LinearPlant (n : ℕ) where
  /-- The open-loop plant matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The actuation vector. -/
  B : Fin n → ℝ
  /-- The sensing vector. -/
  C : Fin n → ℝ

namespace LinearPlant

variable {n : ℕ} (P : LinearPlant n)

/-- The open-loop plant vector field `A x + B u`. -/
noncomputable def field (x : Fin n → ℝ) (u : ℝ) : Fin n → ℝ :=
  P.A *ᵥ x + u • P.B

/-- The sensed output `C x`. -/
noncomputable def output (x : Fin n → ℝ) : ℝ :=
  P.C ⬝ᵥ x

/-- The linear leaky integral closed loop `ẋ = A x + B u`, `u̇ = −ε (u − C x)`. -/
noncomputable def linearLoop (ε : ℝ) (z : (Fin n → ℝ) × ℝ) : (Fin n → ℝ) × ℝ :=
  (P.field z.1 z.2, -ε * (z.2 - P.output z.1))

/-- The antithetic internal-model closed loop `ẋ = A x + B u`, `u̇ = μ − θ (C x)`.

Here `u` is the controller charge `q = z₁ − z₂`; this is the linear internal-model form of the
antithetic integral feedback motif. -/
noncomputable def antitheticLoop (μ θ : ℝ) (z : (Fin n → ℝ) × ℝ) : (Fin n → ℝ) × ℝ :=
  (P.field z.1 z.2, μ - θ * P.output z.1)

/-! ## The setpoint -/

/-- **Setpoint of the leaky linear integral loop.**  At an equilibrium with `ε ≠ 0` the plant
equation `A x + B u = 0` holds and the controller state equals the sensed output, `u = C x`. -/
theorem linearLoop_equilibrium {ε : ℝ} (hε : ε ≠ 0) {z : (Fin n → ℝ) × ℝ}
    (h : P.linearLoop ε z = (0, 0)) :
    P.A *ᵥ z.1 + z.2 • P.B = 0 ∧ z.2 = P.output z.1 := by
  constructor
  · have h1 := congrArg Prod.fst h
    simpa [linearLoop, field] using h1
  · have h2 := congrArg Prod.snd h
    have hzero : -ε * (z.2 - P.output z.1) = 0 := by simpa [linearLoop] using h2
    have hsub : z.2 - P.output z.1 = 0 := by
      rcases mul_eq_zero.mp hzero with h | h
      · exact absurd (neg_eq_zero.mp h) hε
      · exact h
    linarith

/-- **The sensed output equals the controller state** at every equilibrium of the leaky loop. -/
theorem linearLoop_output_eq_controller {ε : ℝ} (hε : ε ≠ 0) {z : (Fin n → ℝ) × ℝ}
    (h : P.linearLoop ε z = (0, 0)) :
    P.output z.1 = z.2 :=
  (P.linearLoop_equilibrium hε h).2.symm

/-- Eliminating the controller state from the leaky-loop equilibrium gives the closed-loop
algebraic equation `A x + (C x) • B = 0`. -/
theorem linearLoop_closedLoop_equation {ε : ℝ} (hε : ε ≠ 0) {z : (Fin n → ℝ) × ℝ}
    (h : P.linearLoop ε z = (0, 0)) :
    P.A *ᵥ z.1 + (P.output z.1) • P.B = 0 := by
  obtain ⟨hplant, hu⟩ := P.linearLoop_equilibrium hε h
  rw [hu] at hplant
  exact hplant

/-- **Setpoint of the antithetic internal-model loop.**  At an equilibrium with `θ ≠ 0` the plant
equation `A x + B u = 0` holds and the sensed output is pinned at `μ/θ`. -/
theorem antitheticLoop_equilibrium {μ θ : ℝ} (hθ : θ ≠ 0) {z : (Fin n → ℝ) × ℝ}
    (h : P.antitheticLoop μ θ z = (0, 0)) :
    P.A *ᵥ z.1 + z.2 • P.B = 0 ∧ P.output z.1 = μ / θ := by
  constructor
  · have h1 := congrArg Prod.fst h
    simpa [antitheticLoop, field] using h1
  · have h2 := congrArg Prod.snd h
    have hzero : μ - θ * P.output z.1 = 0 := by simpa [antitheticLoop] using h2
    have hmul : θ * P.output z.1 = μ := by linarith
    rw [eq_div_iff hθ]
    linarith

/-- **General-plant RPA.**  Every equilibrium of the antithetic closed loop has output `μ/θ`,
independently of the plant matrix `A` and the actuation vector `B`. -/
theorem antitheticLoop_setpoint {μ θ : ℝ} (hθ : θ ≠ 0) {z : (Fin n → ℝ) × ℝ}
    (h : P.antitheticLoop μ θ z = (0, 0)) :
    P.output z.1 = μ / θ :=
  (P.antitheticLoop_equilibrium hθ h).2

/-- Two equilibria of the antithetic loop at the same controller rates have the same output. -/
theorem antitheticLoop_output_eq_of_two_equilibria {μ θ : ℝ} (hθ : θ ≠ 0)
    {z₁ z₂ : (Fin n → ℝ) × ℝ}
    (h₁ : P.antitheticLoop μ θ z₁ = (0, 0))
    (h₂ : P.antitheticLoop μ θ z₂ = (0, 0)) :
    P.output z₁.1 = P.output z₂.1 := by
  rw [P.antitheticLoop_setpoint hθ h₁, P.antitheticLoop_setpoint hθ h₂]

/-- The antithetic equilibrium equation for the plant state, with the controller variable kept. -/
theorem antitheticLoop_plant_equation {μ θ : ℝ} (hθ : θ ≠ 0) {z : (Fin n → ℝ) × ℝ}
    (h : P.antitheticLoop μ θ z = (0, 0)) :
    P.A *ᵥ z.1 + z.2 • P.B = 0 :=
  (P.antitheticLoop_equilibrium hθ h).1

end LinearPlant

/-! ## The scalar production–degradation plant -/

/-- The `1 × 1` matrix with entry `a`. -/
abbrev scalarMatrix (a : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => a

/-- The scalar plant matrix `(−γ)`. -/
abbrev scalarA (γ : ℝ) : Matrix (Fin 1) (Fin 1) ℝ := scalarMatrix (-γ)

/-- The scalar actuation vector `(k)`. -/
abbrev scalarB (k : ℝ) : Fin 1 → ℝ := fun _ => k

/-- The scalar sensing vector `(1)`. -/
abbrev scalarC : Fin 1 → ℝ := fun _ => 1

/-- The scalar production–degradation plant `ẋ = −γ x + k u`, `y = x`. -/
def productionDegradation (γ k : ℝ) : LinearPlant 1 where
  A := scalarA γ
  B := scalarB k
  C := scalarC

namespace ProductionDegradation

variable {γ k : ℝ}

@[simp] theorem A_apply (i j : Fin 1) :
    (productionDegradation γ k).A i j = -γ := rfl

@[simp] theorem B_apply (i : Fin 1) :
    (productionDegradation γ k).B i = k := rfl

@[simp] theorem C_apply (i : Fin 1) :
    (productionDegradation γ k).C i = 1 := rfl

/-- The scalar plant field. -/
theorem field_apply (x : Fin 1 → ℝ) (u : ℝ) :
    (productionDegradation γ k).field x u = fun _ => -γ * x 0 + k * u := by
  funext i
  fin_cases i
  simp [LinearPlant.field, productionDegradation, Matrix.mulVec, dotProduct]
  ring

/-- The scalar output is the state itself. -/
theorem output_apply (x : Fin 1 → ℝ) :
    (productionDegradation γ k).output x = x 0 := by
  simp [LinearPlant.output, productionDegradation, dotProduct]

/-- **Scalar antithetic setpoint.**  At an equilibrium the state is `μ/θ`. -/
theorem antithetic_setpoint {μ θ : ℝ} (hθ : θ ≠ 0) {z : (Fin 1 → ℝ) × ℝ}
    (h : (productionDegradation γ k).antitheticLoop μ θ z = (0, 0)) :
    z.1 0 = μ / θ := by
  simpa [output_apply] using (productionDegradation γ k).antitheticLoop_setpoint hθ h

/-- **Scalar leaky-loop setpoint.**  At an equilibrium the state equals the controller state. -/
theorem linear_setpoint {ε : ℝ} (hε : ε ≠ 0) {z : (Fin 1 → ℝ) × ℝ}
    (h : (productionDegradation γ k).linearLoop ε z = (0, 0)) :
    z.1 0 = z.2 := by
  have := (productionDegradation γ k).linearLoop_output_eq_controller hε h
  simpa [output_apply] using this

/-- The scalar equilibrium balance `−γ x + k u = 0`. -/
theorem antithetic_balance {μ θ : ℝ} (hθ : θ ≠ 0) {z : (Fin 1 → ℝ) × ℝ}
    (h : (productionDegradation γ k).antitheticLoop μ θ z = (0, 0)) :
    -γ * z.1 0 + k * z.2 = 0 := by
  have h' := (productionDegradation γ k).antitheticLoop_plant_equation hθ h
  have h0 := congrFun h' 0
  simp [productionDegradation, Matrix.mulVec, dotProduct, smul_eq_mul] at h0
  linarith

end ProductionDegradation

/-! ## Quadratic Lyapunov functions -/

/-- The quadratic form `xᵀ M x`, written as an explicit finite sum. -/
noncomputable def quadForm {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : ℝ :=
  ∑ i, x i * (M *ᵥ x) i

/-- The linear-quadratic Lyapunov function around an equilibrium `(x*, u*)`. -/
noncomputable def lqLyap {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (xStar : Fin n → ℝ) (uStar : ℝ) (z : (Fin n → ℝ) × ℝ) : ℝ :=
  quadForm P (z.1 - xStar) + (z.2 - uStar) ^ 2

/-- A quadratic Lyapunov function with a positive-semidefinite shape matrix is nonnegative. -/
theorem lqLyap_nonneg {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hP : ∀ x, 0 ≤ quadForm P x) (xStar : Fin n → ℝ) (uStar : ℝ)
    (z : (Fin n → ℝ) × ℝ) :
    0 ≤ lqLyap P xStar uStar z := by
  unfold lqLyap
  have h := hP (z.1 - xStar)
  nlinarith [sq_nonneg (z.2 - uStar)]

/-- The Lie derivative of the LQ Lyapunov function along the leaky loop, in deviation
coordinates `e = x − x*`, `v = u − u*`. -/
noncomputable def linearLieDeriv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B C : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (ε : ℝ) (e : Fin n → ℝ) (v : ℝ) : ℝ :=
  2 * ∑ i, (P *ᵥ e) i * (A *ᵥ e + v • B) i + 2 * v * (-ε * (v - C ⬝ᵥ e))

/-- The Lie derivative of the LQ Lyapunov function along the antithetic internal-model loop. -/
noncomputable def antitheticLieDeriv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (B C : Fin n → ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) (e : Fin n → ℝ) (v : ℝ) : ℝ :=
  2 * ∑ i, (P *ᵥ e) i * (A *ᵥ e + v • B) i + 2 * v * (-(θ * (C ⬝ᵥ e)))

/-- **The Lyapunov equation in quadratic form.**  The matrix `P` is a Lyapunov function shape
matrix for `A` with decrease matrix `Q`. -/
def LyapunovEquation {n : ℕ} (A P Q : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ e : Fin n → ℝ, 2 * ∑ i, (P *ᵥ e) i * (A *ᵥ e) i = -quadForm Q e

/-- **The actuation/sensing matching condition** `(P e)ᵀ B = gain · (C e)`. -/
def ActuationSensingMatch {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (B C : Fin n → ℝ)
    (gain : ℝ) : Prop :=
  ∀ e : Fin n → ℝ, ∑ i, (P *ᵥ e) i * B i = gain * (C ⬝ᵥ e)

/-- A packaged LQ Lyapunov certificate: a positive-semidefinite `P`, a nonnegative `Q`, the
Lyapunov equation and the actuation/sensing matching condition. -/
structure LyapunovCertificate (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (B C : Fin n → ℝ) where
  /-- Shape matrix of the state quadratic form. -/
  P : Matrix (Fin n) (Fin n) ℝ
  /-- Decrease matrix of the Lyapunov equation. -/
  Q : Matrix (Fin n) (Fin n) ℝ
  /-- The actuation/sensing gain. -/
  gain : ℝ
  /-- `P` is positive semidefinite. -/
  P_nonneg : ∀ e, 0 ≤ quadForm P e
  /-- `Q` is positive semidefinite. -/
  Q_nonneg : ∀ e, 0 ≤ quadForm Q e
  /-- `P` solves the Lyapunov equation for `A` with decrease `Q`. -/
  lyapunov : LyapunovEquation A P Q
  /-- The actuation/sensing matching condition. -/
  match_actuation : ActuationSensingMatch P B C gain

namespace LyapunovCertificate

variable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} {B C : Fin n → ℝ}
  (L : LyapunovCertificate n A B C)

theorem quadForm_P_nonneg (e : Fin n → ℝ) : 0 ≤ quadForm L.P e :=
  L.P_nonneg e

theorem quadForm_Q_nonneg (e : Fin n → ℝ) : 0 ≤ quadForm L.Q e :=
  L.Q_nonneg e

/-- Splitting the Lie-derivative cross term using the Lyapunov equation and the matching
condition. -/
theorem lieDeriv_split (e : Fin n → ℝ) (v : ℝ) :
    2 * ∑ i, (L.P *ᵥ e) i * (A *ᵥ e + v • B) i =
      -quadForm L.Q e + 2 * v * (L.gain * (C ⬝ᵥ e)) := by
  have hsum : ∑ i, (L.P *ᵥ e) i * (A *ᵥ e + v • B) i =
      ∑ i, (L.P *ᵥ e) i * (A *ᵥ e) i +
        v * ∑ i, (L.P *ᵥ e) i * B i := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.add_apply, Pi.smul_apply]
    ring
  rw [hsum, L.match_actuation e]
  have hlyap := L.lyapunov e
  linarith

/-- **Leaky-loop LQ drift.**  If `Q` dominates `((gain+ε)²/ε) CᵀC`, then the Lie derivative along
the leaky loop is at most `−ε v²`. -/
theorem linearLieDeriv_le {ε : ℝ} (hε : 0 < ε)
    (hQC : ∀ e : Fin n → ℝ, (L.gain + ε) ^ 2 / ε * (C ⬝ᵥ e) ^ 2 ≤ quadForm L.Q e)
    (e : Fin n → ℝ) (v : ℝ) :
    linearLieDeriv A B C L.P ε e v ≤ -ε * v ^ 2 := by
  have hsplit := L.lieDeriv_split e v
  have hrepr : linearLieDeriv A B C L.P ε e v =
      -quadForm L.Q e + 2 * (L.gain + ε) * v * (C ⬝ᵥ e) - 2 * ε * v ^ 2 := by
    unfold linearLieDeriv
    rw [hsplit]
    ring
  rw [hrepr]
  have hyoung : 2 * (L.gain + ε) * v * (C ⬝ᵥ e) ≤
      ε * v ^ 2 + (L.gain + ε) ^ 2 / ε * (C ⬝ᵥ e) ^ 2 := by
    have hsq : 0 ≤ (ε * v - (L.gain + ε) * (C ⬝ᵥ e)) ^ 2 / ε :=
      div_nonneg (sq_nonneg _) hε.le
    have heq : (ε * v - (L.gain + ε) * (C ⬝ᵥ e)) ^ 2 / ε =
        ε * v ^ 2 + (L.gain + ε) ^ 2 / ε * (C ⬝ᵥ e) ^ 2 -
          2 * (L.gain + ε) * v * (C ⬝ᵥ e) := by
      field_simp
      ring
    linarith
  have hq := hQC e
  nlinarith

/-- **Antithetic-loop LQ drift.**  If the actuation/sensing gain equals the sensing rate `θ`, the
Lie derivative along the antithetic internal-model loop is `−eᵀQe ≤ 0`. -/
theorem antitheticLieDeriv_nonpos {θ : ℝ} (hθ : L.gain = θ) (e : Fin n → ℝ) (v : ℝ) :
    antitheticLieDeriv A B C L.P θ e v ≤ 0 := by
  have hsplit := L.lieDeriv_split e v
  have hrepr : antitheticLieDeriv A B C L.P θ e v =
      -quadForm L.Q e + 2 * (L.gain - θ) * v * (C ⬝ᵥ e) := by
    unfold antitheticLieDeriv
    rw [hsplit]
    ring
  rw [hrepr, hθ]
  have h := L.Q_nonneg e
  nlinarith

/-- **Strict antithetic-loop LQ decay.**  If additionally `Q` is positive definite, the Lie
derivative is strictly negative for every nonzero state deviation. -/
theorem antitheticLieDeriv_neg {θ : ℝ} (hθ : L.gain = θ)
    (hQpos : ∀ e : Fin n → ℝ, e ≠ 0 → 0 < quadForm L.Q e)
    {e : Fin n → ℝ} (he : e ≠ 0) (v : ℝ) :
    antitheticLieDeriv A B C L.P θ e v < 0 := by
  have hsplit := L.lieDeriv_split e v
  have hrepr : antitheticLieDeriv A B C L.P θ e v =
      -quadForm L.Q e + 2 * (L.gain - θ) * v * (C ⬝ᵥ e) := by
    unfold antitheticLieDeriv
    rw [hsplit]
    ring
  rw [hrepr, hθ]
  have h := hQpos e he
  nlinarith

end LyapunovCertificate

/-! ## The scalar Lyapunov certificate -/

/-- The quadratic form of a scalar matrix is `a x²`. -/
theorem quadForm_scalarMatrix (a : ℝ) (x : Fin 1 → ℝ) :
    quadForm (scalarMatrix a) x = a * x 0 ^ 2 := by
  simp [quadForm, scalarMatrix, Matrix.mulVec, dotProduct]
  ring

/-- **A scalar Lyapunov certificate.**  For the scalar plant `A = −γ`, `B = k`, `C = 1`, the
choice `P = p`, `Q = 2pγ`, `gain = pk` solves the Lyapunov equation and the matching condition. -/
abbrev scalarCertificate (p γ k : ℝ) (hp : 0 < p) (hγ : 0 < γ) :
    LyapunovCertificate 1 (scalarA γ) (scalarB k) scalarC where
  P := scalarMatrix p
  Q := scalarMatrix (2 * p * γ)
  gain := p * k
  P_nonneg := by
    intro e
    rw [quadForm_scalarMatrix]
    positivity
  Q_nonneg := by
    intro e
    rw [quadForm_scalarMatrix]
    positivity
  lyapunov := by
    intro e
    rw [quadForm_scalarMatrix]
    simp [scalarA, scalarMatrix, Matrix.mulVec, dotProduct]
    ring
  match_actuation := by
    intro e
    simp [scalarB, scalarC, scalarMatrix, Matrix.mulVec, dotProduct]
    ring

/-- The scalar certificate's decrease matrix dominates the leaky-loop Young term when
`(pk + ε)²/ε ≤ 2pγ`. -/
theorem scalarCertificate_leaky_condition (p γ k ε : ℝ) (hp : 0 < p) (hγ : 0 < γ)
    (hcond : (p * k + ε) ^ 2 / ε ≤ 2 * p * γ) (e : Fin 1 → ℝ) :
    ((scalarCertificate p γ k hp hγ).gain + ε) ^ 2 / ε * (scalarC ⬝ᵥ e) ^ 2 ≤
      quadForm (scalarCertificate p γ k hp hγ).Q e := by
  have hgain : (scalarCertificate p γ k hp hγ).gain = p * k := rfl
  have hQ : (scalarCertificate p γ k hp hγ).Q = scalarMatrix (2 * p * γ) := rfl
  have hdot : scalarC ⬝ᵥ e = e 0 := by
    simp [scalarC, dotProduct]
  rw [hgain, hQ, hdot, quadForm_scalarMatrix]
  have hmul := mul_le_mul_of_nonneg_right hcond (sq_nonneg (e 0))
  linarith [hmul]

/-! ## General Foster–Lyapunov ergodicity -/

/-- The data of a Foster–Lyapunov drift condition for a jump system: a nonnegative Lyapunov
function `V`, a nonnegative norm-like function `f` with finite sublevel sets, and a constant `K`
such that `QV ≤ −f + K`. -/
structure FosterDrift {α : Type*} (J : JumpSystem α) (V f : α → ℝ) where
  /-- `V` is nonnegative. -/
  V_nonneg : ∀ x, 0 ≤ V x
  /-- `f` is nonnegative. -/
  f_nonneg : ∀ x, 0 ≤ f x
  /-- `f` has finite sublevel sets. -/
  f_finite : ∀ R : ℝ, {x | f x ≤ R}.Finite
  /-- The additive constant in the drift bound. -/
  K : ℝ
  /-- The additive constant is nonnegative. -/
  K_nonneg : 0 ≤ K
  /-- The Foster–Lyapunov drift bound `QV ≤ −f + K`. -/
  drift_le : ∀ x, J.drift V x ≤ -f x + K

namespace FosterDrift

variable {α : Type*} {J : JumpSystem α} {V f : α → ℝ} (H : FosterDrift J V f)

/-- The drift is strictly negative outside the compact set `{f ≤ K + 1}`. -/
theorem drift_neg_outside {x : α} (hx : H.K + 1 ≤ f x) : J.drift V x ≤ -1 := by
  have h := H.drift_le x
  linarith

/-- The drift is negative outside every superlevel set `{f ≤ c}` with `c > K`. -/
theorem drift_neg_outside_of_lt {c : ℝ} (hc : H.K < c) {x : α} (hx : c ≤ f x) :
    J.drift V x < 0 := by
  have h := H.drift_le x
  linarith

end FosterDrift

/-- **Positive recurrence / ergodicity from a Foster–Lyapunov drift.**  A countable, irreducible,
non-explosive jump system satisfying the drift condition (H) has a unique stationary probability
law, charges every state, and converges in total variation from every state. -/
theorem ergodic_of_fosterDrift {α : Type*} [Countable α] [Nonempty α] [DecidableEq α]
    (J : JumpSystem α) (V f : α → ℝ) (H : FosterDrift J V f)
    (hstoch : ∀ t, 0 ≤ t → ∀ x, HasSum (fun b => J.Pmin t x b) 1)
    (hirr : ∀ a b, J.ReachPos a b) :
    ∃ π : α → ℝ, (∀ b, 0 < π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * J.Pmin s x b = π b) ∧
      (∀ a, Tendsto (fun t => ∑' b, |J.Pmin t a b - π b|) atTop (𝓝 0)) ∧
      (∀ μ : α → ℝ, (∀ b, 0 ≤ μ b) → HasSum μ 1 →
        (∀ s, 0 ≤ s → ∀ b, ∑' x, μ x * J.Pmin s x b = μ b) → μ = π) := by
  classical
  obtain ⟨π, hπ0, hπ1, hinv, -, hpos, hconv, huniq⟩ :=
    J.foster_lyapunov_ergodic V f H.V_nonneg H.f_nonneg H.f_finite (K := H.K) H.K_nonneg
      H.drift_le hstoch (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
      (fun a _ b _ => hirr a b) (Set.mem_univ (Classical.choice ‹Nonempty α›))
  exact ⟨π, fun b => hpos b (Set.mem_univ b), hπ1, hinv,
    fun a => hconv a (Set.mem_univ a),
    fun μ hμ0 hμ1 hμinv =>
      huniq μ hμ0 (fun b hb => absurd (Set.mem_univ b) hb) hμ1 hμinv⟩

/-- **Geometric ergodicity from a Foster–Lyapunov drift on a set.**  This is the Meyn–Tweedie
`(CD4)` conclusion: the drift may be positive only on `C`, and `C` is finite (here arbitrary, since
the statement is an immediate consequence of `geometric_ergodic_of_drift_on`). -/
theorem geometric_ergodic_of_fosterDrift {α : Type*} [Countable α] [Nonempty α] [DecidableEq α]
    (J : JumpSystem α) (V : α → ℝ) (hV0 : ∀ x, 0 ≤ V x)
    (hfinV : ∀ R : ℝ, {x | V x ≤ R}.Finite) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (C : Set α) (hdrift : ∀ x, J.drift V x ≤ -c * V x + K * C.indicator 1 x)
    (hstoch : ∀ t, 0 ≤ t → ∀ x, HasSum (fun b => J.Pmin t x b) 1)
    (hirr : ∀ a b, J.ReachPos a b) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * J.Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |J.Pmin t a b - π b| * (1 + β * V b) ≤ C₀ * (1 + V a) * ρ ^ ⌊t⌋₊ := by
  classical
  exact J.geometric_ergodic_of_drift_on V hV0 hfinV hc hK C hdrift hstoch hirr

/-! ## Specialization: the production–degradation closed loop -/

namespace ProductionDegradationNetwork

open CRNT.Antithetic

/-- The Foster–Lyapunov drift hypothesis (H) for the production–degradation antithetic loop,
discharged by the existing `CRNT.Antithetic.drift_lyap_le`. -/
noncomputable def fosterDrift (κ : closedLoop.RateConstants) :
    FosterDrift (closedLoop.jumpSystem κ) (lyap κ) (fLyap κ) where
  V_nonneg := lyap_nonneg κ
  f_nonneg := fLyap_nonneg κ
  f_finite := fLyap_finite κ
  K := cK κ
  K_nonneg := cK_nonneg κ
  drift_le := drift_lyap_le κ

/-- Non-explosion of the production–degradation closed loop, from the affine drift bound. -/
theorem hasSum_Pmin_one (κ : closedLoop.RateConstants) :
    ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (closedLoop.jumpSystem κ).Pmin t n m) 1 := by
  intro t ht n
  exact (closedLoop.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (lyap κ)
    (lyap_nonneg κ) (lyap_finite κ) le_rfl (cK_nonneg κ)
    (fun a => by
      have h1 := drift_lyap_le κ a
      have h2 := fLyap_nonneg κ a
      linarith) ht n

/-- **Ergodicity of the production–degradation closed loop, derived from the general Foster
transfer theorem.**  This is the specialization of `ergodic_of_fosterDrift` with `(H)` discharged
by `drift_lyap_le`. -/
theorem closedLoop_ergodic_via_general (κ : closedLoop.RateConstants) :
    ∃ π : (Fin 3 → ℕ) → ℝ, (∀ n, 0 < π n) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' n, π n * closedLoop.transition κ t n m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |closedLoop.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      (∀ ν : (Fin 3 → ℕ) → ℝ, (∀ n, 0 ≤ ν n) → HasSum ν 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' n, ν n * closedLoop.transition κ t n m = ν m) → ν = π) := by
  have h := ergodic_of_fosterDrift (closedLoop.jumpSystem κ) (lyap κ) (fLyap κ)
    (fosterDrift κ) (hasSum_Pmin_one κ) (irreducible κ)
  simpa [Network.transition] using h

/-- The full statement of `CRNT.Antithetic.closedLoop_ergodic`, recovered as the specialization of
the general framework.  The moment bound and the setpoint are the existing stochastic arguments,
which are independent of the Foster transfer step. -/
theorem closedLoop_ergodic_full_via_general (κ : closedLoop.RateConstants) :
    ∃ π : (Fin 3 → ℕ) → ℝ, (∀ n, 0 < π n) ∧ HasSum π 1 ∧
      (∀ t, 0 ≤ t → ∀ m, ∑' n, π n * closedLoop.transition κ t n m = π m) ∧
      (∀ n, Tendsto (fun t => ∑' m, |closedLoop.transition κ t n m - π m|) atTop (𝓝 0)) ∧
      (∀ ν : (Fin 3 → ℕ) → ℝ, (∀ n, 0 ≤ ν n) → HasSum ν 1 →
        (∀ t, 0 ≤ t → ∀ m, ∑' n, ν n * closedLoop.transition κ t n m = ν m) → ν = π) ∧
      ∑' n, π n * fLyap κ n ≤ cK κ ∧
      ∑' n, π n * (n 2 : ℝ) = κ.k rRef / κ.k rSense :=
  closedLoop_ergodic κ

/-- **Convergence of the mean output to the setpoint**, recovered from the existing
`CRNT.Antithetic.closedLoop_mean_output_tendsto`. -/
theorem closedLoop_mean_output_tendsto_via_general (κ : closedLoop.RateConstants)
    (n : Fin 3 → ℕ) :
    Tendsto (fun t => ∑' m, closedLoop.transition κ t n m * (m 2 : ℝ)) atTop
      (𝓝 (κ.k rRef / κ.k rSense)) :=
  closedLoop_mean_output_tendsto κ n

/-- The general scalar setpoint `μ/θ` agrees with the network setpoint `κ_ref/κ_sense` under the
identification `μ = κ_ref`, `θ = κ_sense`. -/
theorem productionDegradation_setpoint_eq_network (κ : closedLoop.RateConstants)
    {γ k μ θ : ℝ} (hθ : θ ≠ 0) {z : (Fin 1 → ℝ) × ℝ}
    (href : κ.k rRef = μ) (hsense : κ.k rSense = θ)
    (h : (productionDegradation γ k).antitheticLoop μ θ z = (0, 0)) :
    z.1 0 = κ.k rRef / κ.k rSense := by
  rw [ProductionDegradation.antithetic_setpoint (γ := γ) (k := k) hθ h, href, hsense]

/-! ## Deterministic trajectories and Lyapunov decrease

The results so far are algebraic: they identify the derivative of the LQ Lyapunov function along
the vector field.  Here we connect them to honest ODE trajectories.  For a curve `s ↦ (e s, v s)`
in deviation coordinates, `HasDerivAt` hypotheses encode the scalar closed-loop equations, and the
Lyapunov function `s ↦ p e(s)² + v(s)²` has the stated derivative.  The final theorems restate
this for the actual state variables `s ↦ (x s, u s)`, eliminating the equilibrium coordinates
using the balance and reference equations. -/

/-- The scalar LQ Lyapunov function around `(xStar, uStar)`. -/
noncomputable def scalarLQ (p xStar uStar x u : ℝ) : ℝ :=
  p * (x - xStar) ^ 2 + (u - uStar) ^ 2

/-- `scalarLQ` is the general `lqLyap` with `P = (p)` on the one-dimensional state space. -/
theorem scalarLQ_eq_lqLyap (p xStar uStar x u : ℝ) :
    scalarLQ p xStar uStar x u =
      lqLyap (scalarMatrix p) (fun _ : Fin 1 => xStar) uStar
        ((fun _ : Fin 1 => x), u) := by
  simp [scalarLQ, lqLyap, quadForm_scalarMatrix]

namespace ScalarTrajectories

variable {p γ k ε θ μ xStar uStar : ℝ}

/-- **Lyapunov decrease along antithetic trajectories.**  In deviation coordinates the scalar
antithetic loop is `ė = −γ e + k v`, `v̇ = −θ e`.  If the certificate gain matches the sensing
rate, `p k = θ`, then `d/dt (p e² + v²) = −2 p γ e²`. -/
theorem antithetic_trajectory (hgain : p * k = θ)
    {e v : ℝ → ℝ} {t : ℝ}
    (he : HasDerivAt e (-γ * e t + k * v t) t)
    (hv : HasDerivAt v (-(θ * e t)) t) :
    HasDerivAt (fun s => p * e s ^ 2 + v s ^ 2) (-(2 * p * γ) * e t ^ 2) t := by
  have h1 : HasDerivAt (fun s => e s ^ 2) (2 * e t * (-γ * e t + k * v t)) t := by
    convert he.pow 2 using 1
    ring
  have h2 := h1.const_mul p
  have h3 : HasDerivAt (fun s => v s ^ 2) (2 * v t * (-(θ * e t))) t := by
    convert hv.pow 2 using 1
    ring
  have h := h2.add h3
  convert h using 1
  linear_combination (-2 * e t * v t) * hgain

/-- **Lyapunov derivative along leaky-loop trajectories.**  In deviation coordinates the scalar
leaky loop is `ė = −γ e + k v`, `v̇ = −ε (v − e)`.  The derivative of `p e² + v²` is the displayed
quadratic form. -/
theorem leaky_trajectory
    {e v : ℝ → ℝ} {t : ℝ}
    (he : HasDerivAt e (-γ * e t + k * v t) t)
    (hv : HasDerivAt v (-ε * (v t - e t)) t) :
    HasDerivAt (fun s => p * e s ^ 2 + v s ^ 2)
      (-2 * p * γ * e t ^ 2 + 2 * (p * k + ε) * e t * v t - 2 * ε * v t ^ 2) t := by
  have h1 : HasDerivAt (fun s => e s ^ 2) (2 * e t * (-γ * e t + k * v t)) t := by
    convert he.pow 2 using 1
    ring
  have h2 := h1.const_mul p
  have h3 : HasDerivAt (fun s => v s ^ 2) (2 * v t * (-ε * (v t - e t))) t := by
    convert hv.pow 2 using 1
    ring
  have h := h2.add h3
  convert h using 1
  ring

/-- **Leaky-loop trajectory decrease.**  Under the Young condition
`(pk + ε)²/ε ≤ 2pγ`, the derivative in `leaky_trajectory` is at most `−ε v²`. -/
theorem leaky_trajectory_decay (hε : 0 < ε)
    (hcond : (p * k + ε) ^ 2 / ε ≤ 2 * p * γ)
    {e v : ℝ → ℝ} {t : ℝ}
    (he : HasDerivAt e (-γ * e t + k * v t) t)
    (hv : HasDerivAt v (-ε * (v t - e t)) t) :
    HasDerivAt (fun s => p * e s ^ 2 + v s ^ 2)
      (-2 * p * γ * e t ^ 2 + 2 * (p * k + ε) * e t * v t - 2 * ε * v t ^ 2) t ∧
    (-2 * p * γ * e t ^ 2 + 2 * (p * k + ε) * e t * v t - 2 * ε * v t ^ 2)
      ≤ -ε * v t ^ 2 := by
  constructor
  · exact leaky_trajectory he hv
  · have hyoung : 2 * (p * k + ε) * e t * v t ≤
        ε * v t ^ 2 + (p * k + ε) ^ 2 / ε * (e t) ^ 2 := by
      have hsq : 0 ≤ (ε * v t - (p * k + ε) * e t) ^ 2 / ε :=
        div_nonneg (sq_nonneg _) hε.le
      have heq : (ε * v t - (p * k + ε) * e t) ^ 2 / ε =
          ε * v t ^ 2 + (p * k + ε) ^ 2 / ε * (e t) ^ 2 -
            2 * (p * k + ε) * e t * v t := by
        field_simp
        ring
      linarith
    have hmul := mul_le_mul_of_nonneg_right hcond (sq_nonneg (e t))
    nlinarith

/-- **Antithetic Lyapunov decrease for the actual scalar plant.**  For `ẋ = −γx + ku`,
`u̇ = μ − θx`, equilibrium balance `−γx* + ku* = 0` and reference `μ = θx*`, the Lyapunov
function `p (x−x*)² + (u−u*)²` has derivative `−2pγ (x−x*)²`. -/
theorem antithetic_plant_trajectory (hbal : -γ * xStar + k * uStar = 0)
    (href : μ = θ * xStar) (hgain : p * k = θ)
    {x u : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (-γ * x t + k * u t) t)
    (hu : HasDerivAt u (μ - θ * x t) t) :
    HasDerivAt (fun s => scalarLQ p xStar uStar (x s) (u s))
      (-(2 * p * γ) * (x t - xStar) ^ 2) t := by
  have he : HasDerivAt (fun s => x s - xStar)
      (-γ * (x t - xStar) + k * (u t - uStar)) t := by
    have h := hx.sub_const xStar
    have hdiff : -γ * x t + k * u t =
        -γ * (x t - xStar) + k * (u t - uStar) := by
      linarith
    rwa [hdiff] at h
  have hv : HasDerivAt (fun s => u s - uStar) (-(θ * (x t - xStar))) t := by
    have h := hu.sub_const uStar
    have hdiff : μ - θ * x t = -(θ * (x t - xStar)) := by
      linarith
    rwa [hdiff] at h
  have h := antithetic_trajectory (p := p) (γ := γ) (k := k) (θ := θ) hgain
    (e := fun s => x s - xStar) (v := fun s => u s - uStar) he hv
  simpa [scalarLQ] using h

/-- **Leaky-loop Lyapunov derivative for the actual scalar plant.**  For `ẋ = −γx + ku`,
`u̇ = −ε(u−x)`, equilibrium balance `−γx* + ku* = 0` and leaky setpoint `u* = x*`, the derivative
of `p (x−x*)² + (u−u*)²` is the displayed quadratic form. -/
theorem leaky_plant_trajectory (hbal : -γ * xStar + k * uStar = 0)
    (hset : uStar = xStar)
    {x u : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (-γ * x t + k * u t) t)
    (hu : HasDerivAt u (-ε * (u t - x t)) t) :
    HasDerivAt (fun s => scalarLQ p xStar uStar (x s) (u s))
      (-2 * p * γ * (x t - xStar) ^ 2 +
        2 * (p * k + ε) * (x t - xStar) * (u t - uStar) -
        2 * ε * (u t - uStar) ^ 2) t := by
  have he : HasDerivAt (fun s => x s - xStar)
      (-γ * (x t - xStar) + k * (u t - uStar)) t := by
    have h := hx.sub_const xStar
    have hdiff : -γ * x t + k * u t =
        -γ * (x t - xStar) + k * (u t - uStar) := by
      linarith
    rwa [hdiff] at h
  have hv : HasDerivAt (fun s => u s - uStar)
      (-ε * ((u t - uStar) - (x t - xStar))) t := by
    have h := hu.sub_const uStar
    have hdiff : u t - x t = (u t - uStar) - (x t - xStar) := by
      linarith
    rwa [hdiff] at h
  have h := leaky_trajectory (p := p) (γ := γ) (k := k) (ε := ε)
    (e := fun s => x s - xStar) (v := fun s => u s - uStar) he hv
  simpa [scalarLQ] using h

end ScalarTrajectories

/-! ## A concrete numerical instance

The plant `ẋ = −10 x + u`, `y = x` with reference rate `μ = 2` and sensing rate `θ = 1`.  The
setpoint is `2`, the antithetic equilibrium is `(x, u) = (2, 20)`, and the LQ certificate
`P = 1`, `Q = 20`, `gain = 1` satisfies every hypothesis of the general theory. -/

namespace ConcreteInstance

/-- The concrete plant `ẋ = −10 x + u`, `y = x`. -/
def plant : LinearPlant 1 := productionDegradation 10 1

/-- The reference rate. -/
def muRef : ℝ := 2

/-- The sensing rate. -/
def thetaSense : ℝ := 1

/-- The setpoint `μ/θ`. -/
noncomputable def setpoint : ℝ := muRef / thetaSense

/-- The equilibrium state. -/
def xStar : Fin 1 → ℝ := fun _ => 2

/-- The equilibrium controller state. -/
def uStar : ℝ := 20

theorem muRef_pos : 0 < muRef := by norm_num [muRef]

theorem thetaSense_pos : 0 < thetaSense := by norm_num [thetaSense]

theorem setpoint_eq_two : setpoint = 2 := by norm_num [setpoint, muRef, thetaSense]

/-- The antithetic closed loop has the equilibrium `(2, 20)`. -/
theorem antithetic_equilibrium :
    plant.antitheticLoop muRef thetaSense (xStar, uStar) = (0, 0) := by
  apply Prod.ext
  · funext i
    fin_cases i
    simp [plant, xStar, uStar, muRef, thetaSense, productionDegradation,
      LinearPlant.antitheticLoop, LinearPlant.field, LinearPlant.output, Matrix.mulVec,
      dotProduct]
    norm_num
  · simp [plant, xStar, uStar, muRef, thetaSense, productionDegradation,
      LinearPlant.antitheticLoop, LinearPlant.output, dotProduct]

/-- The output at the equilibrium equals the setpoint. -/
theorem output_eq_setpoint : plant.output xStar = setpoint := by
  have h := plant.antitheticLoop_setpoint thetaSense_pos.ne' antithetic_equilibrium
  simpa [setpoint] using h

/-- The equilibrium output is the number `2`. -/
theorem output_eq_two : plant.output xStar = 2 := by
  rw [output_eq_setpoint, setpoint_eq_two]

/-- The plant balance `A x* + B u* = 0` at the equilibrium. -/
theorem plant_balance : plant.A *ᵥ xStar + uStar • plant.B = 0 := by
  funext i
  fin_cases i
  simp [plant, xStar, uStar, productionDegradation, Matrix.mulVec, dotProduct]
  norm_num

/-- The equilibrium also satisfies the leaky-loop equation: with `ε = 1` and `(x, u) = (2, 20)`,
the controller state is not equal to the output, so this is *not* an equilibrium of the leaky
loop; the latter has the trivial equilibrium `(0, 0)`. -/
theorem leaky_equilibrium :
    plant.linearLoop 1 (0, 0) = (0, 0) := by
  apply Prod.ext
  · funext i
    fin_cases i
    simp [plant, productionDegradation, LinearPlant.linearLoop, LinearPlant.field]
  · simp [plant, productionDegradation, LinearPlant.linearLoop, LinearPlant.output]

/-- The point `(2, 20)` is *not* an equilibrium of the leaky loop with `ε = 1`: the controller
derivative there is `−18`, not zero. -/
theorem leaky_not_equilibrium :
    plant.linearLoop 1 (xStar, uStar) ≠ (0, 0) := by
  intro h
  have h2 := congrArg Prod.snd h
  simp [plant, productionDegradation, LinearPlant.linearLoop, LinearPlant.output,
    xStar, uStar, dotProduct] at h2
  norm_num at h2

/-- The scalar LQ certificate with `p = 1`, `γ = 10`, `k = 1`. -/
abbrev cert : LyapunovCertificate 1 plant.A plant.B plant.C :=
  scalarCertificate 1 10 1 (by norm_num) (by norm_num)

/-- The certificate gain is `1`, matching the sensing rate `θ = 1`. -/
theorem cert_gain : cert.gain = 1 := by
  norm_num [cert, scalarCertificate]

/-- The leaky-loop Young condition `(gain + ε)²/ε = 4 ≤ 2pγ = 20`. -/
theorem cert_leaky_condition (e : Fin 1 → ℝ) :
    (cert.gain + 1) ^ 2 / 1 * (plant.C ⬝ᵥ e) ^ 2 ≤ quadForm cert.Q e := by
  have h := scalarCertificate_leaky_condition 1 10 1 1 (by norm_num) (by norm_num)
    (by norm_num) e
  simpa [cert, plant, productionDegradation] using h

/-- **Concrete antithetic trajectory.**  For the numerical plant `ẋ = −10x + u`, `u̇ = 2 − x`,
the LQ Lyapunov function `(x−2)² + (u−20)²` has derivative `−20 (x−2)²`. -/
theorem antithetic_trajectory_concrete {x u : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (-10 * x t + u t) t)
    (hu : HasDerivAt u (2 - x t) t) :
    HasDerivAt (fun s => scalarLQ 1 2 20 (x s) (u s)) (-20 * (x t - 2) ^ 2) t := by
  have hx' : HasDerivAt x (-10 * x t + 1 * u t) t := by simpa using hx
  have hu' : HasDerivAt u (2 - 1 * x t) t := by simpa using hu
  have h := ScalarTrajectories.antithetic_plant_trajectory
    (p := 1) (γ := 10) (k := 1) (μ := 2) (θ := 1)
    (xStar := 2) (uStar := 20) (by norm_num) (by norm_num) (by norm_num) hx' hu'
  convert h using 1
  ring

/-- **Concrete leaky-loop trajectory.**  For `ẋ = −10x + u`, `u̇ = −(u−x)`, the derivative of
`x² + u²` is `−20x² + 4xu − 2u²`. -/
theorem leaky_trajectory_concrete {x u : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (-10 * x t + u t) t)
    (hu : HasDerivAt u (-1 * (u t - x t)) t) :
    HasDerivAt (fun s => scalarLQ 1 0 0 (x s) (u s))
      (-20 * (x t) ^ 2 + 4 * x t * u t - 2 * (u t) ^ 2) t := by
  have hx' : HasDerivAt x (-10 * x t + 1 * u t) t := by simpa using hx
  have h := ScalarTrajectories.leaky_plant_trajectory
    (p := 1) (γ := 10) (k := 1) (ε := 1) (xStar := 0) (uStar := 0)
    (by norm_num) (by norm_num) hx' hu
  convert h using 1
  ring

/-- **Concrete leaky-loop trajectory decrease.**  The same trajectory satisfies the Young
condition `(1·1 + 1)²/1 = 4 ≤ 2·1·10 = 20`, hence its Lyapunov derivative is at most `−u²`. -/
theorem leaky_trajectory_concrete_decay {x u : ℝ → ℝ} {t : ℝ}
    (hx : HasDerivAt x (-10 * x t + u t) t)
    (hu : HasDerivAt u (-1 * (u t - x t)) t) :
    HasDerivAt (fun s => scalarLQ 1 0 0 (x s) (u s))
        (-20 * (x t) ^ 2 + 4 * x t * u t - 2 * (u t) ^ 2) t ∧
      (-20 * (x t) ^ 2 + 4 * x t * u t - 2 * (u t) ^ 2) ≤ -(u t) ^ 2 := by
  have hx' : HasDerivAt x (-10 * x t + 1 * u t) t := by simpa using hx
  have h := ScalarTrajectories.leaky_trajectory_decay
    (p := 1) (γ := 10) (k := 1) (ε := 1) (by norm_num) (by norm_num)
    (e := x) (v := u) hx' hu
  constructor
  · convert h.1 using 1
    · ext s
      simp [scalarLQ]
    · ring
  · nlinarith [sq_nonneg (10 * x t - u t), sq_nonneg (u t)]

/-- **Leaky-loop Lyapunov decrease for the concrete instance.** -/
theorem leaky_drift (e : Fin 1 → ℝ) (v : ℝ) :
    linearLieDeriv plant.A plant.B plant.C cert.P 1 e v ≤ -1 * v ^ 2 :=
  cert.linearLieDeriv_le (ε := 1) (by norm_num) (cert_leaky_condition) e v

/-- **Antithetic-loop Lyapunov non-increase for the concrete instance.** -/
theorem antithetic_drift (e : Fin 1 → ℝ) (v : ℝ) :
    antitheticLieDeriv plant.A plant.B plant.C cert.P 1 e v ≤ 0 :=
  cert.antitheticLieDeriv_nonpos (θ := 1) cert_gain e v

/-- **Strict antithetic-loop Lyapunov decay** away from the equilibrium. -/
theorem antithetic_drift_strict {e : Fin 1 → ℝ} (he : e ≠ 0) (v : ℝ) :
    antitheticLieDeriv plant.A plant.B plant.C cert.P 1 e v < 0 := by
  refine cert.antitheticLieDeriv_neg (θ := 1) cert_gain ?_ he v
  intro e he
  have hQ : cert.Q = scalarMatrix (2 * 1 * 10) := rfl
  rw [hQ, quadForm_scalarMatrix]
  have h0 : e 0 ≠ 0 := by
    intro h
    apply he
    funext i
    fin_cases i
    simpa using h
  have hpos : 0 < e 0 ^ 2 := sq_pos_of_ne_zero h0
  nlinarith

end ConcreteInstance

end ProductionDegradationNetwork

end GeneralPlant
end Design
end CRNT
