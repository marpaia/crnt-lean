import CRNT.Oscillation.StructuralCore
import CRNT.Equilibria.SteadyState
import CRNT.Kinetics.MassActionJacobian
import CRNT.Deficiency.Consistent

/-!
# Flux-form structural Hopf criteria

This module fixes the CRN-side objects used in the 2025 mass-action Hopf criteria in a form that is
faithful to the steady-state-flux formulation.

For a positive steady state `x` with rate constants `κ`, the reaction flux

`v_r = κ_r * x^(source_r)`

is strictly positive and lies in the stoichiometric kernel.  The associated square matrix

`B(v)_{ij} = sum_r v_r * source_r(j) * reactionVector_r(i)`

is the concentration-rescaled Jacobian core.  At a positive concentration the mass-action
Jacobian satisfies `J(x) * diag(x) = B(v)`; equivalently `J(x) = B(v) * diag(1/x)`.

The file proves the elementary flux positivity/kernel facts and packages the matrix criteria.  The
paper-level global-Hopf realization implication is deliberately exposed as a theorem target rather
than postulated as an axiom.
-/

namespace CRNT

open scoped BigOperators

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reaction flux induced by positive mass-action rate constants at a concentration. -/
def steadyStateFlux (N : Network S) (κ : N.RateConstants) (x : Concentration S) : N.R → ℝ :=
  fun r => N.massActionRate κ r x

/-- A strictly positive reaction-flux vector lying in the stoichiometric kernel. -/
structure PositiveSteadyStateFlux (N : Network S) (v : N.R → ℝ) : Prop where
  positive : ∀ r, 0 < v r
  stationary : ∀ s : S, (∑ r : N.R, v r * N.reactionVector r s) = 0

/-- A positive mass-action steady state induces a positive stoichiometrically stationary flux. -/
theorem steadyStateFlux_isPositiveSteadyStateFlux (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (hss : N.IsMassActionSteadyState κ x) :
    N.PositiveSteadyStateFlux (N.steadyStateFlux κ x) := by
  constructor
  · intro r
    exact N.massActionRate_pos κ r hx
  · intro s
    exact (N.isMassActionSteadyState_iff κ x).mp hss s

/-- A positive stationary flux is exactly the positive dependence appearing in CRN consistency. -/
theorem exists_positiveSteadyStateFlux_iff_isConsistent (N : Network S) :
    (∃ v : N.R → ℝ, N.PositiveSteadyStateFlux v) ↔ N.IsConsistent := by
  constructor
  · rintro ⟨v, hv⟩
    refine ⟨v, hv.positive, ?_⟩
    funext s
    have hs := hv.stationary s
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs
  · rintro ⟨v, hvpos, hvzero⟩
    refine ⟨v, ?_⟩
    constructor
    · exact hvpos
    · intro s
      have hs := congrFun hvzero s
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs

/-- Realize a prescribed positive stationary reaction flux at a prescribed positive concentration.
The rate constant is `v_r / x^(source_r)`, whose denominator is positive. -/
noncomputable def rateConstantsOfPositiveSteadyStateFlux (N : Network S)
    {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v)
    {x : Concentration S} (hx : x.Positive) : N.RateConstants where
  k := fun r => v r / (N.reaction r).source.massActionMonomial x
  positive := fun r => div_pos (hv.positive r) (Complex.massActionMonomial_pos hx _)

/-- The rate constants constructed from `(v,x)` realize exactly the requested reaction flux. -/
theorem massActionRate_rateConstantsOfPositiveSteadyStateFlux (N : Network S)
    {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v)
    {x : Concentration S} (hx : x.Positive) (r : N.R) :
    N.massActionRate (N.rateConstantsOfPositiveSteadyStateFlux hv hx) r x = v r := by
  unfold massActionRate rateConstantsOfPositiveSteadyStateFlux
  dsimp
  exact div_mul_cancel₀ (v r) (Complex.massActionMonomial_pos hx _).ne'

/-- The prescribed positive concentration is a mass-action steady state for the rate constants
realizing a positive stationary flux. -/
theorem isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux (N : Network S)
    {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v)
    {x : Concentration S} (hx : x.Positive) :
    N.IsMassActionSteadyState (N.rateConstantsOfPositiveSteadyStateFlux hv hx) x := by
  rw [N.isMassActionSteadyState_iff]
  intro s
  simp_rw [N.massActionRate_rateConstantsOfPositiveSteadyStateFlux hv hx]
  exact hv.stationary s

/-- Consistency is sufficient to realize a positive mass-action steady state at every prescribed
positive concentration.  The rate constants are allowed to depend on that concentration. -/
theorem exists_rateConstants_isMassActionSteadyState_of_isConsistent (N : Network S)
    (hcons : N.IsConsistent) {x : Concentration S} (hx : x.Positive) :
    ∃ κ : N.RateConstants, N.IsMassActionSteadyState κ x := by
  obtain ⟨v, hv⟩ := (N.exists_positiveSteadyStateFlux_iff_isConsistent).2 hcons
  exact ⟨N.rateConstantsOfPositiveSteadyStateFlux hv hx,
    N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux hv hx⟩

/-- The flux-Jacobian core `B(v)` used in the mass-action structural Hopf criteria. -/
def fluxJacobianCore (N : Network S) (v : N.R → ℝ) : Matrix S S ℝ :=
  fun i j => ∑ r : N.R, v r * ((N.reaction r).source j : ℝ) * N.reactionVector r i

/-- The reaction-by-species derivative matrix naturally associated with mass action at `x`.
Its `(r,j)` entry is `κ_r ∂_j x^(source_r)`. -/
def massActionReactivity (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    N.ReactivityMatrix :=
  fun r j => κ.k r * massActionMonomialGrad (N.reaction r).source x j

/-- The parameter-rich symbolic Jacobian specializes exactly to the ordinary mass-action Jacobian
when supplied with `massActionReactivity`. -/
theorem symbolicJacobian_massActionReactivity (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    N.symbolicJacobian (N.massActionReactivity κ x) = N.massActionJacobian κ x := by
  ext i j
  simp only [symbolicJacobian, massActionReactivity, massActionJacobian]
  apply Finset.sum_congr rfl
  intro r _
  ring

-- `massActionMonomialGrad_mul_coord` now lives in `Kinetics/MassActionJacobian.lean`,
-- next to the definition of `massActionMonomialGrad`, so the `Equilibria/*` stability
-- modules can use it without importing `Oscillation/*`.
/-- At a positive concentration, the mass-action reactivity matrix has exactly the admissible
reactant-support sign pattern required by `IsReactivityMatrix`. -/
theorem massActionReactivity_isReactivityMatrix (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    N.IsReactivityMatrix (N.massActionReactivity κ x) := by
  constructor
  · intro r j hrj
    have hyj : 0 < (((N.reaction r).source j : ℕ) : ℝ) := by
      exact_mod_cast hrj
    have hmon : 0 < (N.reaction r).source.massActionMonomial x :=
      Complex.massActionMonomial_pos hx _
    have hgradEq := massActionMonomialGrad_mul_coord (N.reaction r).source x j
    have hgrad : 0 < massActionMonomialGrad (N.reaction r).source x j := by
      nlinarith [hx j, mul_pos hyj hmon]
    exact mul_pos (κ.positive r) hgrad
  · intro r j hrj
    simp [massActionReactivity, massActionMonomialGrad, hrj]

/-- Reactivity matrix obtained directly from a reaction flux `v` at a positive state `x`: each
source sensitivity is `v_r * source_r(j) / x_j`.  This is the local derivative form underlying
`B(v) * diag(1/x)`. -/
noncomputable def fluxReactivityAt (N : Network S) (v : N.R → ℝ) (x : Concentration S) :
    N.ReactivityMatrix :=
  fun r j => v r * ((N.reaction r).source j : ℝ) * (x j)⁻¹

/-- A positive flux at a positive state gives an admissible reactivity sign/support pattern.  The
stationarity equation is not needed for this local statement. -/
theorem fluxReactivityAt_isReactivityMatrix (N : Network S) {v : N.R → ℝ}
    (hv : ∀ r, 0 < v r) {x : Concentration S} (hx : x.Positive) :
    N.IsReactivityMatrix (N.fluxReactivityAt v x) := by
  constructor
  · intro r j hrj
    have hyj : 0 < (((N.reaction r).source j : ℕ) : ℝ) := by
      exact_mod_cast hrj
    exact mul_pos (mul_pos (hv r) hyj) (inv_pos.mpr (hx j))
  · intro r j hrj
    simp [fluxReactivityAt, hrj]

/-- The symbolic Jacobian of `fluxReactivityAt` is exactly the flux core followed by the positive
right diagonal scaling `diag(1/x)`. -/
theorem symbolicJacobian_fluxReactivityAt (N : Network S) (v : N.R → ℝ)
    (x : Concentration S) :
    N.symbolicJacobian (N.fluxReactivityAt v x) =
      N.fluxJacobianCore v * Matrix.diagonal (fun s => (x s)⁻¹) := by
  classical
  ext i j
  -- `Matrix.mul_diagonal` collapses the right factor in one step.  Going through
  -- `mul_ite`/`Finset.sum_ite_eq'` instead leaves the else-branch as `_ * 0` rather than a
  -- syntactic `0`, so no `sum_ite_eq` variant can fire.
  rw [Matrix.mul_diagonal]
  simp only [symbolicJacobian, fluxReactivityAt, fluxJacobianCore, Finset.sum_mul]
  exact Finset.sum_congr rfl fun r _ => by ring

/-- At a positive state, the derivative-defined mass-action reactivity matrix is exactly the
flux-defined reactivity matrix evaluated at the induced mass-action reaction rates. -/
theorem massActionReactivity_eq_fluxReactivityAt (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    N.massActionReactivity κ x = N.fluxReactivityAt (N.steadyStateFlux κ x) x := by
  funext r j
  have hxj : x j ≠ 0 := ne_of_gt (hx j)
  have hgrad := massActionMonomialGrad_mul_coord (N.reaction r).source x j
  have hgrad' : massActionMonomialGrad (N.reaction r).source x j =
      (((N.reaction r).source j : ℝ) * (N.reaction r).source.massActionMonomial x) / x j :=
    (eq_div_iff hxj).2 hgrad
  rw [massActionReactivity, fluxReactivityAt, steadyStateFlux, massActionRate, hgrad', div_eq_mul_inv]
  ring

/-- **Mass-action Jacobian / flux-core factorization, cross-multiplied form.**

For every concentration (positivity is not needed for this identity), multiplying the Jacobian on
the right by `diag(x)` gives the flux core evaluated at the induced reaction rates. -/
theorem massActionJacobian_mul_diagonal_eq_fluxJacobianCore
    (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    N.massActionJacobian κ x * Matrix.diagonal x =
      N.fluxJacobianCore (N.steadyStateFlux κ x) := by
  classical
  ext i j
  rw [Matrix.mul_diagonal]
  simp only [massActionJacobian, fluxJacobianCore, steadyStateFlux, massActionRate,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  -- `rw [massActionMonomialGrad_mul_coord]` cannot fire: the product `grad * x j` is not
  -- syntactically present in the term.  Scale the identity instead.
  linear_combination (κ.k r * N.reactionVector r i) *
    massActionMonomialGrad_mul_coord (N.reaction r).source x j

/-- At a positive concentration, the Jacobian is the flux core times `diag(1/x)`.  This is the
right-diagonal scaling used by the structural Hopf criteria. -/
theorem massActionJacobian_eq_fluxJacobianCore_mul_invDiagonal
    (N : Network S) (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    N.massActionJacobian κ x =
      N.fluxJacobianCore (N.steadyStateFlux κ x) * Matrix.diagonal (fun s => (x s)⁻¹) := by
  classical
  -- Derive this from the cross-multiplied form rather than re-deriving entrywise: cancel
  -- `diag(x) * diag(1/x) = 1` on the right.
  rw [← N.massActionJacobian_mul_diagonal_eq_fluxJacobianCore κ x, Matrix.mul_assoc,
    Matrix.diagonal_mul_diagonal]
  have hcancel : (fun s => x s * (x s)⁻¹) = fun _ : S => (1 : ℝ) := by
    funext s
    exact mul_inv_cancel₀ (ne_of_gt (hx s))
  rw [hcancel, Matrix.diagonal_one, Matrix.mul_one]

/-- The Jacobian of the canonical realization of a prescribed flux `v` at `x` has exactly the
right-diagonal factorization `B(v) * diag(1/x)`. -/
theorem massActionJacobian_rateConstantsOfPositiveSteadyStateFlux
    (N : Network S) {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v)
    {x : Concentration S} (hx : x.Positive) :
    N.massActionJacobian (N.rateConstantsOfPositiveSteadyStateFlux hv hx) x =
      N.fluxJacobianCore v * Matrix.diagonal (fun s => (x s)⁻¹) := by
  rw [N.massActionJacobian_eq_fluxJacobianCore_mul_invDiagonal
    (N.rateConstantsOfPositiveSteadyStateFlux hv hx) hx]
  have hflux :
      N.steadyStateFlux (N.rateConstantsOfPositiveSteadyStateFlux hv hx) x = v := by
    funext r
    exact N.massActionRate_rateConstantsOfPositiveSteadyStateFlux hv hx r
  rw [hflux]

/-- The all-ones concentration, used as a canonical realization point for stationary fluxes. -/
def unitConcentration (S : Type) : S → ℝ := fun _ => 1

@[simp] theorem unitConcentration_apply (s : S) : unitConcentration S s = 1 := rfl

/-- The all-ones concentration is strictly positive. -/
theorem unitConcentration_positive : Concentration.Positive (unitConcentration S) := by
  intro s
  simp [unitConcentration]

/-- At the canonical all-ones realization, the mass-action Jacobian is exactly the flux core `B(v)`
with no residual diagonal scaling. -/
theorem massActionJacobian_rateConstantsOfPositiveSteadyStateFlux_unit
    (N : Network S) {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v) :
    N.massActionJacobian
        (N.rateConstantsOfPositiveSteadyStateFlux hv (unitConcentration_positive (S := S)))
        (unitConcentration S) = N.fluxJacobianCore v := by
  rw [N.massActionJacobian_rateConstantsOfPositiveSteadyStateFlux hv
    (unitConcentration_positive (S := S))]
  have hdiag : Matrix.diagonal (fun s : S => (unitConcentration S s)⁻¹) =
      (1 : Matrix S S ℝ) := by
    ext i j
    simp [unitConcentration, Matrix.diagonal_apply, Matrix.one_apply]
  rw [hdiag, Matrix.mul_one]

/-- Positive concentration corresponding to a positive right-diagonal scaling `d`: `x_i = 1/d_i`.
Under the mass-action flux realization this makes the Jacobian scaling exactly `diag(d)`. -/
noncomputable def concentrationOfPositiveDiagonal (d : S → ℝ) : Concentration S :=
  fun s => (d s)⁻¹

/-- A strictly positive diagonal gives a strictly positive reciprocal concentration. -/
theorem concentrationOfPositiveDiagonal_positive {d : S → ℝ} (hd : ∀ s, 0 < d s) :
    Concentration.Positive (concentrationOfPositiveDiagonal d) := by
  intro s
  exact inv_pos.mpr (hd s)

/-- **Every positive right-diagonal scaling of `B(v)` is an actual mass-action steady-state
Jacobian.**  Given stationary positive flux `v` and `d > 0`, realize `v` at `x_i = 1/d_i`.
The constructed positive rate constants make `x` a steady state and its Jacobian is exactly
`B(v) * diag(d)`.  This is the concrete CRN realization bridge needed by diagonal-stability and
Hopf arguments. -/
theorem exists_positiveSteadyState_jacobian_eq_fluxCore_mul_diagonal
    (N : Network S) {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v)
    (d : S → ℝ) (hd : ∀ s, 0 < d s) :
    ∃ (κ : N.RateConstants) (x : Concentration S),
      x.Positive ∧ N.IsMassActionSteadyState κ x ∧
      N.steadyStateFlux κ x = v ∧
      N.massActionJacobian κ x = N.fluxJacobianCore v * Matrix.diagonal d := by
  let x : Concentration S := concentrationOfPositiveDiagonal d
  have hx : x.Positive := concentrationOfPositiveDiagonal_positive hd
  let κ : N.RateConstants := N.rateConstantsOfPositiveSteadyStateFlux hv hx
  refine ⟨κ, x, hx, ?_, ?_, ?_⟩
  · exact N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux hv hx
  · funext r
    exact N.massActionRate_rateConstantsOfPositiveSteadyStateFlux hv hx r
  · rw [N.massActionJacobian_rateConstantsOfPositiveSteadyStateFlux hv hx]
    have hdiag :
        Matrix.diagonal (fun s => (x s)⁻¹) = Matrix.diagonal d := by
      ext i j
      simp [x, concentrationOfPositiveDiagonal, Matrix.diagonal_apply]
    rw [hdiag]

/-- Pointwise version of the preceding realization: the canonical rates at `x_i = 1/d_i` have
Jacobian `B(v) * diag(d)`. -/
theorem massActionJacobian_reciprocalDiagonalRealization
    (N : Network S) {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v)
    (d : S → ℝ) (hd : ∀ s, 0 < d s) :
    N.massActionJacobian
        (N.rateConstantsOfPositiveSteadyStateFlux hv
          (concentrationOfPositiveDiagonal_positive hd))
        (concentrationOfPositiveDiagonal d) =
      N.fluxJacobianCore v * Matrix.diagonal d := by
  rw [N.massActionJacobian_rateConstantsOfPositiveSteadyStateFlux hv
    (concentrationOfPositiveDiagonal_positive hd)]
  have hdiag :
      Matrix.diagonal (fun s => (concentrationOfPositiveDiagonal d s)⁻¹) =
        Matrix.diagonal d := by
    ext i j
    simp [concentrationOfPositiveDiagonal, Matrix.diagonal_apply]
  rw [hdiag]

/-- **`D`-stability has an exact CRN semantics at fixed stationary flux.**  The flux core `B(v)`
is right-`D`-stable iff every canonical reciprocal-diagonal mass-action realization of that same
stationary flux has a Hurwitz Jacobian.  Thus `D`-stability is not merely an auxiliary matrix notion:
it quantifies exactly over a concrete family of positive CRN steady states. -/
theorem fluxJacobianCore_isDStable_iff_reciprocalRealizations_hurwitz
    (N : Network S) {v : N.R → ℝ} (hv : N.PositiveSteadyStateFlux v) :
    Matrix.IsDStable (N.fluxJacobianCore v) ↔
      ∀ (d : S → ℝ) (hd : ∀ s, 0 < d s),
        Matrix.IsHurwitzReal
          (N.massActionJacobian
            (N.rateConstantsOfPositiveSteadyStateFlux hv
              (concentrationOfPositiveDiagonal_positive hd))
            (concentrationOfPositiveDiagonal d)) := by
  constructor
  · intro hD d hd
    rw [N.massActionJacobian_reciprocalDiagonalRealization hv d hd]
    exact hD d hd
  · intro hreal d hd
    rw [← N.massActionJacobian_reciprocalDiagonalRealization hv d hd]
    exact hreal d hd


/-! ## A concrete positive-diagonal continuation family -/

/-- Affine segment joining two diagonal scalings.  On `μ ∈ [0,1]` it is their convex combination. -/
def positiveDiagonalSegment (d₀ d₁ : S → ℝ) (μ : ℝ) : S → ℝ :=
  fun s => (1 - μ) * d₀ s + μ * d₁ s

@[simp] theorem positiveDiagonalSegment_zero (d₀ d₁ : S → ℝ) :
    positiveDiagonalSegment d₀ d₁ 0 = d₀ := by
  funext s
  simp [positiveDiagonalSegment]

@[simp] theorem positiveDiagonalSegment_one (d₀ d₁ : S → ℝ) :
    positiveDiagonalSegment d₀ d₁ 1 = d₁ := by
  funext s
  simp [positiveDiagonalSegment]

/-- Convex interpolation preserves strict positivity of every diagonal entry. -/
theorem positiveDiagonalSegment_positive {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    ∀ s, 0 < positiveDiagonalSegment d₀ d₁ μ s := by
  intro s
  by_cases hμ0 : μ = 0
  · subst μ
    simpa using hd₀ s
  · have hμpos : 0 < μ := lt_of_le_of_ne hμ.1 (Ne.symm hμ0)
    have hleft : 0 ≤ (1 - μ) * d₀ s :=
      mul_nonneg (sub_nonneg.mpr hμ.2) (hd₀ s).le
    have hright : 0 < μ * d₁ s := mul_pos hμpos (hd₁ s)
    exact add_pos_of_nonneg_of_pos hleft hright

/-- Reciprocal concentration along a positive diagonal continuation. -/
noncomputable def diagonalSegmentState (d₀ d₁ : S → ℝ) (μ : ℝ) : Concentration S :=
  concentrationOfPositiveDiagonal (positiveDiagonalSegment d₀ d₁ μ)

/-- The diagonal-segment state is positive throughout `[0,1]`. -/
theorem diagonalSegmentState_positive {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    Concentration.Positive (diagonalSegmentState d₀ d₁ μ) :=
  concentrationOfPositiveDiagonal_positive
    (positiveDiagonalSegment_positive hd₀ hd₁ hμ)

/-- Positive mass-action rate constants realizing a fixed stationary flux along the diagonal
continuation. -/
noncomputable def diagonalSegmentRates (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) : N.RateConstants :=
  N.rateConstantsOfPositiveSteadyStateFlux hv
    (diagonalSegmentState_positive hd₀ hd₁ hμ)

/-- Every point of the positive-diagonal segment is an actual positive mass-action steady state
with the same reaction flux `v`. -/
theorem diagonalSegment_isSteady (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    N.IsMassActionSteadyState
      (N.diagonalSegmentRates hv hd₀ hd₁ hμ)
      (diagonalSegmentState d₀ d₁ μ) :=
  N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux hv
    (diagonalSegmentState_positive hd₀ hd₁ hμ)

/-- The reaction flux is constant along the entire positive-diagonal realization path. -/
theorem steadyStateFlux_diagonalSegment (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    N.steadyStateFlux
      (N.diagonalSegmentRates hv hd₀ hd₁ hμ)
      (diagonalSegmentState d₀ d₁ μ) = v := by
  funext r
  exact N.massActionRate_rateConstantsOfPositiveSteadyStateFlux hv
    (diagonalSegmentState_positive hd₀ hd₁ hμ) r

/-- **Exact Jacobian path.** Along the canonical steady-state continuation at fixed flux `v`, the
mass-action Jacobian is precisely `B(v) * diag(D(μ))`.  This closes the CRN realization side of the
continuation argument used by structural Hopf criteria. -/
theorem massActionJacobian_diagonalSegment (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s)
    {μ : ℝ} (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    N.massActionJacobian
      (N.diagonalSegmentRates hv hd₀ hd₁ hμ)
      (diagonalSegmentState d₀ d₁ μ) =
        N.fluxJacobianCore v * Matrix.diagonal (positiveDiagonalSegment d₀ d₁ μ) := by
  unfold diagonalSegmentRates diagonalSegmentState
  exact N.massActionJacobian_reciprocalDiagonalRealization hv
    (positiveDiagonalSegment d₀ d₁ μ)
    (positiveDiagonalSegment_positive hd₀ hd₁ hμ)

/-- Endpoint `μ=0` of the continuation realizes `B(v) * diag(d₀)`. -/
theorem massActionJacobian_diagonalSegment_zero (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s) :
    N.massActionJacobian
      (N.diagonalSegmentRates hv hd₀ hd₁ (by exact ⟨le_rfl, zero_le_one⟩))
      (diagonalSegmentState d₀ d₁ 0) =
        N.fluxJacobianCore v * Matrix.diagonal d₀ := by
  simpa using N.massActionJacobian_diagonalSegment hv hd₀ hd₁
    (μ := 0) (by exact ⟨le_rfl, zero_le_one⟩)

/-- Endpoint `μ=1` of the continuation realizes `B(v) * diag(d₁)`. -/
theorem massActionJacobian_diagonalSegment_one (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s) :
    N.massActionJacobian
      (N.diagonalSegmentRates hv hd₀ hd₁ (by exact ⟨zero_le_one, le_rfl⟩))
      (diagonalSegmentState d₀ d₁ 1) =
        N.fluxJacobianCore v * Matrix.diagonal d₁ := by
  simpa using N.massActionJacobian_diagonalSegment hv hd₀ hd₁
    (μ := 1) (by exact ⟨zero_le_one, le_rfl⟩)

/-- Flux-side witness for Vassena Criterion I: a strictly positive stationary reaction flux whose
core matrix is Hurwitz stable but not `P^-_0`. -/
structure FluxCriterionIWitness (N : Network S) : Type where
  flux : N.R → ℝ
  steady : N.PositiveSteadyStateFlux flux
  criterion : Matrix.CriterionI (N.fluxJacobianCore flux)

/-- Flux-side witness for Vassena Criterion II: a strictly positive stationary reaction flux whose
core matrix is unstable and Fisher--Fuller `P^-_{FF}`. -/
structure FluxCriterionIIWitness (N : Network S) : Type where
  flux : N.R → ℝ
  steady : N.PositiveSteadyStateFlux flux
  criterion : Matrix.CriterionII (N.fluxJacobianCore flux)

namespace FluxCriterionIWitness

variable {N : Network S}

/-- The canonical all-ones realization of a Criterion-I flux witness is a positive mass-action
steady state. -/
theorem unit_isSteady (w : FluxCriterionIWitness N) :
    N.IsMassActionSteadyState
      (N.rateConstantsOfPositiveSteadyStateFlux w.steady
        (unitConcentration_positive (S := S)))
      (unitConcentration S) :=
  N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux w.steady
    (unitConcentration_positive (S := S))

/-- At that canonical realization, Criterion I supplies an actually Hurwitz mass-action Jacobian. -/
theorem unit_jacobian_hurwitz (w : FluxCriterionIWitness N) :
    Matrix.IsHurwitzReal
      (N.massActionJacobian
        (N.rateConstantsOfPositiveSteadyStateFlux w.steady
          (unitConcentration_positive (S := S)))
        (unitConcentration S)) := by
  rw [N.massActionJacobian_rateConstantsOfPositiveSteadyStateFlux_unit w.steady]
  exact w.criterion.stable

end FluxCriterionIWitness

namespace FluxCriterionIIWitness

variable {N : Network S}

/-- The canonical all-ones realization of a Criterion-II flux witness is a positive mass-action
steady state. -/
theorem unit_isSteady (w : FluxCriterionIIWitness N) :
    N.IsMassActionSteadyState
      (N.rateConstantsOfPositiveSteadyStateFlux w.steady
        (unitConcentration_positive (S := S)))
      (unitConcentration S) :=
  N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux w.steady
    (unitConcentration_positive (S := S))

/-- At that canonical realization, Criterion II supplies an actually unstable mass-action Jacobian. -/
theorem unit_jacobian_unstable (w : FluxCriterionIIWitness N) :
    Matrix.HasUnstableEigenvalue
      (N.massActionJacobian
        (N.rateConstantsOfPositiveSteadyStateFlux w.steady
          (unitConcentration_positive (S := S)))
        (unitConcentration S)) := by
  rw [N.massActionJacobian_rateConstantsOfPositiveSteadyStateFlux_unit w.steady]
  exact w.criterion.unstable

end FluxCriterionIIWitness

/-- Criterion-I witness on a principal species block.  This is the form needed in the presence of
linear conservation laws, where the full `B(v)` necessarily carries trivial zero eigenvalues. -/
structure PrincipalFluxCriterionIWitness (N : Network S) : Type where
  flux : N.R → ℝ
  steady : N.PositiveSteadyStateFlux flux
  species : Finset S
  nonempty : species.Nonempty
  criterion : Matrix.CriterionI ((N.fluxJacobianCore flux).principalSubmatrix species)

/-- Criterion-II witness on a principal species block, for conserved systems/reduced dynamics. -/
structure PrincipalFluxCriterionIIWitness (N : Network S) : Type where
  flux : N.R → ℝ
  steady : N.PositiveSteadyStateFlux flux
  species : Finset S
  nonempty : species.Nonempty
  criterion : Matrix.CriterionII ((N.fluxJacobianCore flux).principalSubmatrix species)

/-- Actual positive-steady-state realization of Criterion I. -/
structure RealizedCriterionIWitness (N : Network S) : Type where
  rates : N.RateConstants
  state : Concentration S
  positive : state.Positive
  steady : N.IsMassActionSteadyState rates state
  criterion : Matrix.CriterionI (N.fluxJacobianCore (N.steadyStateFlux rates state))

/-- Actual positive-steady-state realization of Criterion II. -/
structure RealizedCriterionIIWitness (N : Network S) : Type where
  rates : N.RateConstants
  state : Concentration S
  positive : state.Positive
  steady : N.IsMassActionSteadyState rates state
  criterion : Matrix.CriterionII (N.fluxJacobianCore (N.steadyStateFlux rates state))

/-- Realize a flux-side Criterion-I witness at any prescribed positive concentration. -/
noncomputable def FluxCriterionIWitness.toRealizedAt {N : Network S}
    (w : FluxCriterionIWitness N) (x : Concentration S) (hx : x.Positive) :
    RealizedCriterionIWitness N where
  rates := N.rateConstantsOfPositiveSteadyStateFlux w.steady hx
  state := x
  positive := hx
  steady := N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux w.steady hx
  criterion := by
    have hflux :
        N.steadyStateFlux (N.rateConstantsOfPositiveSteadyStateFlux w.steady hx) x = w.flux := by
      funext r
      exact N.massActionRate_rateConstantsOfPositiveSteadyStateFlux w.steady hx r
    rw [hflux]
    exact w.criterion

/-- Realize a flux-side Criterion-II witness at any prescribed positive concentration. -/
noncomputable def FluxCriterionIIWitness.toRealizedAt {N : Network S}
    (w : FluxCriterionIIWitness N) (x : Concentration S) (hx : x.Positive) :
    RealizedCriterionIIWitness N where
  rates := N.rateConstantsOfPositiveSteadyStateFlux w.steady hx
  state := x
  positive := hx
  steady := N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux w.steady hx
  criterion := by
    have hflux :
        N.steadyStateFlux (N.rateConstantsOfPositiveSteadyStateFlux w.steady hx) x = w.flux := by
      funext r
      exact N.massActionRate_rateConstantsOfPositiveSteadyStateFlux w.steady hx r
    rw [hflux]
    exact w.criterion

/-- A realized Criterion-I witness forgets to a stationary-flux witness. -/
def RealizedCriterionIWitness.toFlux {N : Network S} (w : RealizedCriterionIWitness N) :
    FluxCriterionIWitness N where
  flux := N.steadyStateFlux w.rates w.state
  steady := N.steadyStateFlux_isPositiveSteadyStateFlux w.rates w.positive w.steady
  criterion := w.criterion

/-- A realized Criterion-II witness forgets to a stationary-flux witness. -/
def RealizedCriterionIIWitness.toFlux {N : Network S} (w : RealizedCriterionIIWitness N) :
    FluxCriterionIIWitness N where
  flux := N.steadyStateFlux w.rates w.state
  steady := N.steadyStateFlux_isPositiveSteadyStateFlux w.rates w.positive w.steady
  criterion := w.criterion

/-- Exact proof frontier for the mass-action realization theorem behind the two 2025 flux criteria.

The proposition is intentionally separate from the finite matrix checks.  Proving it requires the
bifurcation/continuation argument that turns the diagonal-scaling instability transition into a
nonstationary periodic solution. -/
def VassenaFluxCriteriaRealizationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T),
    (Nonempty (FluxCriterionIWitness N) ∨ Nonempty (FluxCriterionIIWitness N)) →
      N.OscillatoryCapacity

/-- Conserved-system extension of the Vassena frontier, using a principal block of `B(v)` as in
Remark 5.4 of the 2025 paper.  The perturbation/reduced-system argument remains part of the analytic
frontier rather than being silently identified with the full-matrix criterion. -/
def VassenaPrincipalFluxCriteriaRealizationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T),
    (Nonempty (PrincipalFluxCriterionIWitness N) ∨
      Nonempty (PrincipalFluxCriterionIIWitness N)) → N.OscillatoryCapacity

/-- Consume a proved Vassena realization theorem using Criterion I. -/
theorem FluxCriterionIWitness.oscillatoryCapacity
    {N : Network S} (hRealize : VassenaFluxCriteriaRealizationTarget)
    (w : FluxCriterionIWitness N) : N.OscillatoryCapacity :=
  hRealize N (Or.inl ⟨w⟩)

/-- Consume a proved Vassena realization theorem using Criterion II. -/
theorem FluxCriterionIIWitness.oscillatoryCapacity
    {N : Network S} (hRealize : VassenaFluxCriteriaRealizationTarget)
    (w : FluxCriterionIIWitness N) : N.OscillatoryCapacity :=
  hRealize N (Or.inr ⟨w⟩)


/-- Consume a proved principal-block realization theorem using Criterion I. -/
theorem PrincipalFluxCriterionIWitness.oscillatoryCapacity
    {N : Network S} (hRealize : VassenaPrincipalFluxCriteriaRealizationTarget)
    (w : PrincipalFluxCriterionIWitness N) : N.OscillatoryCapacity :=
  hRealize N (Or.inl ⟨w⟩)

/-- Consume a proved principal-block realization theorem using Criterion II. -/
theorem PrincipalFluxCriterionIIWitness.oscillatoryCapacity
    {N : Network S} (hRealize : VassenaPrincipalFluxCriteriaRealizationTarget)
    (w : PrincipalFluxCriterionIIWitness N) : N.OscillatoryCapacity :=
  hRealize N (Or.inr ⟨w⟩)

end Network

end CRNT
