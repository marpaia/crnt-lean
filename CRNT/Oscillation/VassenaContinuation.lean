import CRNT.Oscillation.VassenaCriteria

/-!
# Diagonal-scaling continuation behind the Vassena criteria

The CRN-specific realization `J = B(v) D` is already proved in `VassenaCriteria`.  This module
separates the remaining finite-matrix ingredients from the genuinely dynamical global-Hopf theorem.

The two matrix ingredients are stated in the form actually used by the 2025 criterion:

* if `A` is not `P^-_0`, some positive right diagonal scaling `A D` has a strict
  right-half-plane eigenvalue;
* if `A` is Fisher--Fuller `P^-_{FF}`, some positive right diagonal scaling `A D` is Hurwitz
  (the classical theorem in fact gives simple negative real eigenvalues).

Given those ingredients, Criterion I and Criterion II each produce an explicit pair of positive
diagonal scalings with a Hurwitz endpoint and an unstable endpoint.  The reciprocal-state theorem
then realizes both endpoints as genuine positive mass-action steady-state Jacobians with the *same*
stationary reaction flux.

The final Fiedler/Alexander--Yorke global-Hopf theorem is isolated only after additionally recording
invertibility of the fixed core `B(v)`, which guarantees invertibility along every positive diagonal
scaling.  No mere "not Hurwitz" endpoint is treated as a Hopf crossing.
-/

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Matrix ingredient behind the positive-feedback criterion: failure of `P^-_0` produces a
strictly unstable positive right-diagonal scaling. -/
def NotPMinusZeroImpliesUnstableScalingTarget : Prop :=
  ∀ {m : Type u} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ),
    ¬ M.IsPMinusZeroMatrix →
    ∃ d : m → ℝ, (∀ i, 0 < d i) ∧
      (M * Matrix.diagonal d).HasUnstableEigenvalue

/-- Fisher--Fuller diagonal-stabilization ingredient used in the negative-feedback criterion. -/
def FisherFullerStabilizingScalingTarget : Prop :=
  ∀ {m : Type u} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ),
    M.IsFisherFullerPMinusMatrix →
    ∃ d : m → ℝ, (∀ i, 0 < d i) ∧
      IsHurwitzReal (M * Matrix.diagonal d)

/-- Criterion I has an unstable positive scaling once the `P^-_0` matrix theorem is supplied. -/
theorem CriterionI.exists_positive_scaling_unstable
    (hP0 : NotPMinusZeroImpliesUnstableScalingTarget.{u})
    {M : Matrix n n ℝ} (h : CriterionI M) :
    ∃ d : n → ℝ, (∀ i, 0 < d i) ∧
      (M * Matrix.diagonal d).HasUnstableEigenvalue :=
  hP0 M h.notPMinusZero

/-- Criterion II has a Hurwitz positive scaling once Fisher--Fuller stabilizability is supplied. -/
theorem CriterionII.exists_positive_scaling_hurwitz
    (hFF : FisherFullerStabilizingScalingTarget.{u})
    {M : Matrix n n ℝ} (h : CriterionII M) :
    ∃ d : n → ℝ, (∀ i, 0 < d i) ∧
      IsHurwitzReal (M * Matrix.diagonal d) :=
  hFF M h.fisherFuller

/-- A finite matrix certificate of a strict stability transition under positive right-diagonal
scaling: one endpoint is Hurwitz and one has a strict right-half-plane eigenvalue. -/
structure PositiveDiagonalStabilityTransition (M : Matrix n n ℝ) : Type u where
  stableDiagonal : n → ℝ
  stablePositive : ∀ i, 0 < stableDiagonal i
  unstableDiagonal : n → ℝ
  unstablePositive : ∀ i, 0 < unstableDiagonal i
  stable : IsHurwitzReal (M * Matrix.diagonal stableDiagonal)
  unstable : (M * Matrix.diagonal unstableDiagonal).HasUnstableEigenvalue

namespace PositiveDiagonalStabilityTransition

/-- The unstable endpoint is, in particular, not Hurwitz. -/
theorem unstable_not_hurwitz {M : Matrix n n ℝ}
    (T : PositiveDiagonalStabilityTransition M) :
    ¬ IsHurwitzReal (M * Matrix.diagonal T.unstableDiagonal) :=
  not_isHurwitzReal_of_hasUnstableEigenvalue T.unstable

end PositiveDiagonalStabilityTransition

/-- Criterion I yields a diagonal stability transition: identity is stable and a certified positive
scaling is unstable. -/
noncomputable def CriterionI.stabilityTransition
    (hP0 : NotPMinusZeroImpliesUnstableScalingTarget.{u})
    {M : Matrix n n ℝ} (h : CriterionI M) : PositiveDiagonalStabilityTransition M := by
  let hex := h.exists_positive_scaling_unstable hP0
  let d := Classical.choose hex
  have hdhu := Classical.choose_spec hex
  exact
    { stableDiagonal := fun _ => 1
      stablePositive := fun _ => zero_lt_one
      unstableDiagonal := d
      unstablePositive := hdhu.1
      stable := by
        have hdiag : Matrix.diagonal (fun _ : n => (1 : ℝ)) = (1 : Matrix n n ℝ) :=
          Matrix.diagonal_one
        simpa [hdiag] using h.stable
      unstable := hdhu.2 }

/-- Criterion II yields the reverse transition: Fisher--Fuller gives a stable scaling while the
identity scaling retains the original strict instability. -/
noncomputable def CriterionII.stabilityTransition
    (hFF : FisherFullerStabilizingScalingTarget.{u})
    {M : Matrix n n ℝ} (h : CriterionII M) : PositiveDiagonalStabilityTransition M := by
  let hex := h.exists_positive_scaling_hurwitz hFF
  let d := Classical.choose hex
  have hdhs := Classical.choose_spec hex
  exact
    { stableDiagonal := d
      stablePositive := hdhs.1
      unstableDiagonal := fun _ => 1
      unstablePositive := fun _ => zero_lt_one
      stable := hdhs.2
      unstable := by
        have hdiag : Matrix.diagonal (fun _ : n => (1 : ℝ)) = (1 : Matrix n n ℝ) :=
          Matrix.diagonal_one
        simpa [hdiag] using h.unstable }

end Matrix

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## A globally positive smooth diagonal continuation -/

/-- Exponential interpolation between positive diagonal scalings.  Unlike the affine segment, this
path stays strictly positive for every real parameter and is therefore convenient for global-Hopf
continuation arguments. -/
noncomputable def exponentialDiagonalPath (d₀ d₁ : S → ℝ) (μ : ℝ) : S → ℝ :=
  fun s => d₀ s * Real.exp (μ * Real.log (d₁ s / d₀ s))

@[simp] theorem exponentialDiagonalPath_zero (d₀ d₁ : S → ℝ) :
    exponentialDiagonalPath d₀ d₁ 0 = d₀ := by
  funext s
  simp [exponentialDiagonalPath]

/-- The exponential path reaches the second endpoint at parameter `1`. -/
theorem exponentialDiagonalPath_one {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (hd₁ : ∀ s, 0 < d₁ s) :
    exponentialDiagonalPath d₀ d₁ 1 = d₁ := by
  funext s
  have hratio : 0 < d₁ s / d₀ s := div_pos (hd₁ s) (hd₀ s)
  simp only [exponentialDiagonalPath, one_mul]
  rw [Real.exp_log hratio]
  field_simp [ne_of_gt (hd₀ s)]

/-- The exponential diagonal path is strictly positive for every real parameter. -/
theorem exponentialDiagonalPath_positive {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (μ : ℝ) :
    ∀ s, 0 < exponentialDiagonalPath d₀ d₁ μ s := by
  intro s
  exact mul_pos (hd₀ s) (Real.exp_pos _)

/-- Reciprocal positive steady-state concentration along the globally positive path. -/
noncomputable def exponentialDiagonalState (d₀ d₁ : S → ℝ) (μ : ℝ) : Concentration S :=
  concentrationOfPositiveDiagonal (exponentialDiagonalPath d₀ d₁ μ)

/-- The reciprocal state is positive at every real parameter. -/
theorem exponentialDiagonalState_positive {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (μ : ℝ) :
    Concentration.Positive (exponentialDiagonalState d₀ d₁ μ) :=
  concentrationOfPositiveDiagonal_positive (exponentialDiagonalPath_positive hd₀ μ)

/-- Canonical positive rates realizing a fixed positive stationary flux along the exponential path. -/
noncomputable def exponentialDiagonalRates (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (μ : ℝ) : N.RateConstants :=
  N.rateConstantsOfPositiveSteadyStateFlux hv
    (exponentialDiagonalState_positive (d₁ := d₁) hd₀ μ)

/-- Every point of the global path is an actual mass-action steady state with the prescribed flux. -/
theorem exponentialDiagonal_isSteady (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (μ : ℝ) :
    N.IsMassActionSteadyState
      (N.exponentialDiagonalRates (d₁ := d₁) hv hd₀ μ)
      (exponentialDiagonalState d₀ d₁ μ) :=
  N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux hv
    (exponentialDiagonalState_positive (d₁ := d₁) hd₀ μ)

/-- The Jacobian along the globally positive continuation is exactly `B(v) D(μ)`. -/
theorem massActionJacobian_exponentialDiagonal (N : Network S) {v : N.R → ℝ}
    (hv : N.PositiveSteadyStateFlux v) {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) (μ : ℝ) :
    N.massActionJacobian
      (N.exponentialDiagonalRates (d₁ := d₁) hv hd₀ μ)
      (exponentialDiagonalState d₀ d₁ μ) =
      N.fluxJacobianCore v * Matrix.diagonal (exponentialDiagonalPath d₀ d₁ μ) := by
  unfold exponentialDiagonalRates exponentialDiagonalState
  exact N.massActionJacobian_reciprocalDiagonalRealization hv
    (exponentialDiagonalPath d₀ d₁ μ)
    (exponentialDiagonalPath_positive hd₀ μ)

/-- Component functions of the exponential diagonal path are smooth in the continuation parameter. -/
theorem exponentialDiagonalPath_contDiff_apply {d₀ d₁ : S → ℝ}
    (s : S) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun μ : ℝ => exponentialDiagonalPath d₀ d₁ μ s) := by
  unfold exponentialDiagonalPath
  exact contDiff_const.mul
    (Real.contDiff_exp.comp (contDiff_id.mul contDiff_const))

/-- The reciprocal steady-state path is smooth whenever the first endpoint is positive. -/
theorem exponentialDiagonalState_contDiff {d₀ d₁ : S → ℝ}
    (hd₀ : ∀ s, 0 < d₀ s) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun μ : ℝ => exponentialDiagonalState d₀ d₁ μ) := by
  rw [contDiff_pi]
  intro s
  change ContDiff ℝ n (fun μ : ℝ => (exponentialDiagonalPath d₀ d₁ μ s)⁻¹)
  exact (exponentialDiagonalPath_contDiff_apply s).inv
    (fun μ => ne_of_gt (exponentialDiagonalPath_positive hd₀ μ s))


variable {S : Type} [DecidableEq S] [Fintype S]

/-- A strict diagonal-scaling stability transition for `B(v)` together with proof that `v` is a
positive stationary flux.  Every endpoint is therefore an actual positive mass-action steady-state
Jacobian by `massActionJacobian_reciprocalDiagonalRealization`. -/
structure FluxJacobianStabilityTransition (N : Network S) : Type where
  flux : N.R → ℝ
  steady : N.PositiveSteadyStateFlux flux
  transition : Matrix.PositiveDiagonalStabilityTransition (N.fluxJacobianCore flux)

namespace FluxJacobianStabilityTransition

variable {N : Network S}

/-- The globally positive exponential path associated with the certified stable/unstable endpoints. -/
noncomputable def continuationDiagonal (w : FluxJacobianStabilityTransition N) (μ : ℝ) : S → ℝ :=
  exponentialDiagonalPath w.transition.stableDiagonal w.transition.unstableDiagonal μ

/-- Positive steady-state path realizing `continuationDiagonal`. -/
noncomputable def continuationState (w : FluxJacobianStabilityTransition N) (μ : ℝ) : Concentration S :=
  exponentialDiagonalState w.transition.stableDiagonal w.transition.unstableDiagonal μ

/-- Positive rate path realizing the fixed stationary flux along the global continuation. -/
noncomputable def continuationRates (w : FluxJacobianStabilityTransition N) (μ : ℝ) : N.RateConstants :=
  N.exponentialDiagonalRates (d₁ := w.transition.unstableDiagonal)
    w.steady w.transition.stablePositive μ

/-- The continuation diagonal is positive for every real parameter. -/
theorem continuationDiagonal_positive (w : FluxJacobianStabilityTransition N) (μ : ℝ) :
    ∀ s, 0 < w.continuationDiagonal μ s :=
  exponentialDiagonalPath_positive w.transition.stablePositive μ

/-- Every point on the continuation is an actual positive steady state. -/
theorem continuation_isSteady (w : FluxJacobianStabilityTransition N) (μ : ℝ) :
    N.IsMassActionSteadyState (w.continuationRates μ) (w.continuationState μ) :=
  N.exponentialDiagonal_isSteady w.steady w.transition.stablePositive μ

/-- The Jacobian along the continuation is exactly the right-diagonal family `B(v)D(μ)`. -/
theorem continuation_jacobian (w : FluxJacobianStabilityTransition N) (μ : ℝ) :
    N.massActionJacobian (w.continuationRates μ) (w.continuationState μ) =
      N.fluxJacobianCore w.flux * Matrix.diagonal (w.continuationDiagonal μ) := by
  exact N.massActionJacobian_exponentialDiagonal w.steady w.transition.stablePositive μ

/-- Scalar rate-value path with proof fields erased.  This is definitionally the `k` field of
`continuationRates`, but unlike the structure-valued rate path it lives in an ordinary finite real
vector space and can be differentiated. -/
noncomputable def continuationRateValue (w : FluxJacobianStabilityTransition N) (μ : ℝ) (r : N.R) : ℝ :=
  w.flux r /
    (N.reaction r).source.massActionMonomial (w.continuationState μ)

@[simp] theorem continuationRates_k (w : FluxJacobianStabilityTransition N)
    (μ : ℝ) (r : N.R) :
    (w.continuationRates μ).k r = w.continuationRateValue μ r := by
  rfl

/-- Each scalar rate coefficient varies smoothly along the exponential continuation. -/
theorem continuationRateValue_contDiff (w : FluxJacobianStabilityTransition N)
    (r : N.R) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun μ : ℝ => w.continuationRateValue μ r) := by
  have hcoord : ∀ s : S, ContDiff ℝ n (fun μ : ℝ => w.continuationState μ s) := by
    intro s
    exact (contDiff_apply ℝ ℝ s).comp
      (exponentialDiagonalState_contDiff w.transition.stablePositive)
  have hmon : ContDiff ℝ n (fun μ : ℝ =>
      (N.reaction r).source.massActionMonomial (w.continuationState μ)) := by
    show ContDiff ℝ n (fun μ : ℝ =>
      ∏ s : S, (w.continuationState μ s) ^ (N.reaction r).source s)
    exact contDiff_prod fun s _ => (hcoord s).pow _
  have hne : ∀ μ : ℝ,
      (N.reaction r).source.massActionMonomial (w.continuationState μ) ≠ 0 := by
    intro μ
    exact (Complex.massActionMonomial_pos
      (exponentialDiagonalState_positive w.transition.stablePositive μ) _).ne'
  unfold continuationRateValue
  exact contDiff_const.div hmon hne

/-- Proof-erased smooth vector-field family along the global diagonal continuation. -/
noncomputable def continuationField (w : FluxJacobianStabilityTransition N)
    (μ : ℝ) (x : Concentration S) : Concentration S :=
  fun s => ∑ r : N.R,
    w.continuationRateValue μ r *
      (N.reaction r).source.massActionMonomial x * N.reactionVector r s

/-- The smooth proof-erased family is exactly the ordinary mass-action vector field for the
constructed positive rates. -/
theorem continuationField_eq_massAction (w : FluxJacobianStabilityTransition N)
    (μ : ℝ) (x : Concentration S) :
    w.continuationField μ x = N.massActionVectorField (w.continuationRates μ) x := by
  funext s
  simp only [continuationField, massActionVectorField_apply, massActionRate]
  apply Finset.sum_congr rfl
  intro r _
  rw [w.continuationRates_k]

/-- The continuation defines a jointly smooth ODE family in `(parameter,state)`. -/
theorem continuationField_contDiff (w : FluxJacobianStabilityTransition N)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : ℝ × Concentration S => w.continuationField p.1 p.2) := by
  rw [contDiff_pi]
  intro s
  unfold continuationField
  refine ContDiff.sum fun r _ => ?_
  have hk : ContDiff ℝ n (fun p : ℝ × Concentration S => w.continuationRateValue p.1 r) :=
    (w.continuationRateValue_contDiff r).comp contDiff_fst
  have hmon : ContDiff ℝ n (fun p : ℝ × Concentration S =>
      (N.reaction r).source.massActionMonomial p.2) := by
    show ContDiff ℝ n (fun p : ℝ × Concentration S =>
      ∏ j : S, p.2 j ^ (N.reaction r).source j)
    exact contDiff_prod fun j _ => (((contDiff_apply ℝ ℝ j).comp contDiff_snd).pow _)
  exact (hk.mul hmon).mul contDiff_const

/-- At parameter zero the continuation Jacobian is the certified Hurwitz endpoint. -/
theorem continuation_jacobian_zero_hurwitz (w : FluxJacobianStabilityTransition N) :
    Matrix.IsHurwitzReal
      (N.massActionJacobian (w.continuationRates 0) (w.continuationState 0)) := by
  rw [w.continuation_jacobian]
  simpa [continuationDiagonal] using w.transition.stable

/-- At parameter one the continuation Jacobian has a strict right-half-plane eigenvalue. -/
theorem continuation_jacobian_one_unstable (w : FluxJacobianStabilityTransition N) :
    Matrix.HasUnstableEigenvalue
      (N.massActionJacobian (w.continuationRates 1) (w.continuationState 1)) := by
  rw [w.continuation_jacobian]
  have hpath := exponentialDiagonalPath_one
    w.transition.stablePositive w.transition.unstablePositive
  simpa [continuationDiagonal, hpath] using w.transition.unstable

/-- The continuation steady-state curve is smooth in the real parameter. -/
theorem continuationState_contDiff (w : FluxJacobianStabilityTransition N)
    {n : WithTop ℕ∞} :
    ContDiff ℝ n w.continuationState := by
  exact exponentialDiagonalState_contDiff w.transition.stablePositive


/-- Positive steady state realizing the Hurwitz endpoint. -/
noncomputable def stableState (w : FluxJacobianStabilityTransition N) : Concentration S :=
  concentrationOfPositiveDiagonal w.transition.stableDiagonal

/-- Positive steady state realizing the unstable endpoint. -/
noncomputable def unstableState (w : FluxJacobianStabilityTransition N) : Concentration S :=
  concentrationOfPositiveDiagonal w.transition.unstableDiagonal

/-- Positive rates realizing the Hurwitz endpoint. -/
noncomputable def stableRates (w : FluxJacobianStabilityTransition N) : N.RateConstants :=
  N.rateConstantsOfPositiveSteadyStateFlux w.steady
    (concentrationOfPositiveDiagonal_positive w.transition.stablePositive)

/-- Positive rates realizing the unstable endpoint. -/
noncomputable def unstableRates (w : FluxJacobianStabilityTransition N) : N.RateConstants :=
  N.rateConstantsOfPositiveSteadyStateFlux w.steady
    (concentrationOfPositiveDiagonal_positive w.transition.unstablePositive)

/-- The Hurwitz endpoint is an actual steady state. -/
theorem stable_isSteady (w : FluxJacobianStabilityTransition N) :
    N.IsMassActionSteadyState w.stableRates w.stableState := by
  exact N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux w.steady
    (concentrationOfPositiveDiagonal_positive w.transition.stablePositive)

/-- The unstable endpoint is also an actual steady state with the same reaction flux. -/
theorem unstable_isSteady (w : FluxJacobianStabilityTransition N) :
    N.IsMassActionSteadyState w.unstableRates w.unstableState := by
  exact N.isMassActionSteadyState_rateConstantsOfPositiveSteadyStateFlux w.steady
    (concentrationOfPositiveDiagonal_positive w.transition.unstablePositive)

/-- The stable endpoint Jacobian is Hurwitz. -/
theorem stable_jacobian_hurwitz (w : FluxJacobianStabilityTransition N) :
    Matrix.IsHurwitzReal (N.massActionJacobian w.stableRates w.stableState) := by
  unfold stableRates stableState
  rw [N.massActionJacobian_reciprocalDiagonalRealization w.steady
    w.transition.stableDiagonal w.transition.stablePositive]
  exact w.transition.stable

/-- The unstable endpoint Jacobian has a strict right-half-plane eigenvalue. -/
theorem unstable_jacobian_hasUnstableEigenvalue (w : FluxJacobianStabilityTransition N) :
    Matrix.HasUnstableEigenvalue
      (N.massActionJacobian w.unstableRates w.unstableState) := by
  unfold unstableRates unstableState
  rw [N.massActionJacobian_reciprocalDiagonalRealization w.steady
    w.transition.unstableDiagonal w.transition.unstablePositive]
  exact w.transition.unstable

/-- Consequently the unstable endpoint Jacobian is not Hurwitz. -/
theorem unstable_jacobian_not_hurwitz (w : FluxJacobianStabilityTransition N) :
    ¬ Matrix.IsHurwitzReal
      (N.massActionJacobian w.unstableRates w.unstableState) :=
  Matrix.not_isHurwitzReal_of_hasUnstableEigenvalue w.unstable_jacobian_hasUnstableEigenvalue

end FluxJacobianStabilityTransition

/-- Criterion-I flux data plus the `P^-_0` matrix theorem gives concrete stable/unstable
mass-action steady-state Jacobians. -/
noncomputable def FluxCriterionIWitness.stabilityTransition
    {N : Network S}
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget)
    (w : FluxCriterionIWitness N) : N.FluxJacobianStabilityTransition where
  flux := w.flux
  steady := w.steady
  transition := Matrix.CriterionI.stabilityTransition (n := S) hP0 w.criterion

/-- Criterion-II flux data plus Fisher--Fuller diagonal stabilizability gives the analogous concrete
mass-action stability transition. -/
noncomputable def FluxCriterionIIWitness.stabilityTransition
    {N : Network S}
    (hFF : Matrix.FisherFullerStabilizingScalingTarget)
    (w : FluxCriterionIIWitness N) : N.FluxJacobianStabilityTransition where
  flux := w.flux
  steady := w.steady
  transition := Matrix.CriterionII.stabilityTransition (n := S) hFF w.criterion

/-- Data required immediately before applying the global-Hopf theorem in diagonal coordinates.

`coreInvertible` encodes the rank/invertibility hypothesis that rules out a zero eigenvalue anywhere
on the positive diagonal path.  Because the path `positiveDiagonalSegment` is positive on `[0,1]`
and `J=B(v)D`, this is exactly the extra structural condition used by the full-rank Vassena/Fiedler
argument. -/
structure FluxGlobalHopfData (N : Network S) extends FluxJacobianStabilityTransition N where
  coreInvertible : (N.fluxJacobianCore flux).det ≠ 0

namespace FluxGlobalHopfData

variable {N : Network S}

/-- Every continuation Jacobian is nonsingular: `det(B(v)D(μ)) = det(B(v)) det(D(μ))`, and both
factors are nonzero because the core is invertible and every diagonal entry is positive. -/
theorem continuation_jacobian_det_ne_zero (w : N.FluxGlobalHopfData) (μ : ℝ) :
    (N.massActionJacobian (w.toFluxJacobianStabilityTransition.continuationRates μ)
      (w.toFluxJacobianStabilityTransition.continuationState μ)).det ≠ 0 := by
  rw [w.toFluxJacobianStabilityTransition.continuation_jacobian]
  rw [Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero w.coreInvertible
  exact (Finset.prod_ne_zero_iff).2 fun s _ =>
    ne_of_gt (w.toFluxJacobianStabilityTransition.continuationDiagonal_positive μ s)

/-- The same nonsingularity statement in the proof-erased smooth-family notation. -/
theorem continuation_jacobian_core_scaling_det_ne_zero (w : N.FluxGlobalHopfData) (μ : ℝ) :
    (N.fluxJacobianCore w.flux *
      Matrix.diagonal (w.toFluxJacobianStabilityTransition.continuationDiagonal μ)).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_diagonal]
  apply mul_ne_zero w.coreInvertible
  exact (Finset.prod_ne_zero_iff).2 fun s _ =>
    ne_of_gt (w.toFluxJacobianStabilityTransition.continuationDiagonal_positive μ s)

/-- All CRN-specific hypotheses needed before invoking the global-Hopf continuation theorem are now
available from `FluxGlobalHopfData`: smooth family, smooth equilibrium branch, steady-state identity,
endpoint stability change, and nonsingularity along the whole path. -/
structure ContinuationPackage (w : N.FluxGlobalHopfData) where
  fieldSmooth : ContDiff ℝ (⊤ : WithTop ℕ∞)
    (fun p : ℝ × Concentration S =>
      w.toFluxJacobianStabilityTransition.continuationField p.1 p.2)
  equilibriumSmooth : ContDiff ℝ (⊤ : WithTop ℕ∞)
    w.toFluxJacobianStabilityTransition.continuationState
  steady : ∀ μ : ℝ,
    w.toFluxJacobianStabilityTransition.continuationField μ
      (w.toFluxJacobianStabilityTransition.continuationState μ) = 0
  stableAtZero : Matrix.IsHurwitzReal
    (N.massActionJacobian
      (w.toFluxJacobianStabilityTransition.continuationRates 0)
      (w.toFluxJacobianStabilityTransition.continuationState 0))
  unstableAtOne : Matrix.HasUnstableEigenvalue
    (N.massActionJacobian
      (w.toFluxJacobianStabilityTransition.continuationRates 1)
      (w.toFluxJacobianStabilityTransition.continuationState 1))
  nonsingular : ∀ μ : ℝ,
    (N.massActionJacobian
      (w.toFluxJacobianStabilityTransition.continuationRates μ)
      (w.toFluxJacobianStabilityTransition.continuationState μ)).det ≠ 0

/-- Assemble the complete pre-global-Hopf continuation package. -/
theorem continuationPackage (w : N.FluxGlobalHopfData) : w.ContinuationPackage where
  fieldSmooth := w.toFluxJacobianStabilityTransition.continuationField_contDiff
  equilibriumSmooth := w.toFluxJacobianStabilityTransition.continuationState_contDiff
  steady := by
    intro μ
    rw [w.toFluxJacobianStabilityTransition.continuationField_eq_massAction]
    funext s
    exact w.toFluxJacobianStabilityTransition.continuation_isSteady μ s
  stableAtZero := w.toFluxJacobianStabilityTransition.continuation_jacobian_zero_hurwitz
  unstableAtOne := w.toFluxJacobianStabilityTransition.continuation_jacobian_one_unstable
  nonsingular := w.continuation_jacobian_det_ne_zero

end FluxGlobalHopfData

/-- Exact remaining global-Hopf theorem interface after all CRN realization and endpoint work has
been discharged.  This is the Fiedler/Alexander--Yorke continuation step for the analytic
mass-action family generated by the positive diagonal segment. -/
def DiagonalScalingGlobalHopfTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T),
    Nonempty (N.FluxGlobalHopfData) → N.OscillatoryCapacity

/-- Consume the final global-Hopf bridge once it has been formalized. -/
theorem FluxGlobalHopfData.oscillatoryCapacity
    {N : Network S} (hHopf : DiagonalScalingGlobalHopfTarget)
    (w : N.FluxGlobalHopfData) : N.OscillatoryCapacity :=
  hHopf N ⟨w⟩

end Network

end CRNT
