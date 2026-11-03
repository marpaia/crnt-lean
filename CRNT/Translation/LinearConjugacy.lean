import CRNT.Translation.DynamicalEquivalence
import CRNT.Kinetics.MassActionJacobian
import Mathlib.Data.Matrix.Basic
import CRNT.Equilibria.CompatibilityClass
import CRNT.Stoich.Subspace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# Positive diagonal conjugacy of CRN realizations

Dynamical equivalence requires two realizations to have exactly the same vector field.
A broader standard relation in realization theory is **linear conjugacy**: after a
positive diagonal rescaling of species concentrations the flows coincide.  This module
formalizes that relation independently of any realization-search algorithm.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Positive diagonal change of species coordinates. -/
structure PositiveDiagonalChange (S : Type) [Fintype S] where
  scale : S → ℝ
  positive : ∀ s, 0 < scale s

namespace PositiveDiagonalChange

/-- Coordinate rescaling. -/
def map (D : PositiveDiagonalChange S) (x : S → ℝ) : S → ℝ :=
  fun s => D.scale s * x s

/-- Inverse coordinate rescaling. -/
noncomputable def invMap (D : PositiveDiagonalChange S) (x : S → ℝ) : S → ℝ :=
  fun s => x s / D.scale s

@[simp] theorem invMap_map (D : PositiveDiagonalChange S) (x : S → ℝ) :
    D.invMap (D.map x) = x := by
  funext s
  simp [map, invMap, (D.positive s).ne']

@[simp] theorem map_invMap (D : PositiveDiagonalChange S) (x : S → ℝ) :
    D.map (D.invMap x) = x := by
  funext s
  -- goal is `scale s * (x s / scale s) = x s`
  simp only [map, invMap]
  rw [mul_comm, div_mul_cancel₀ _ (D.positive s).ne']

/-- Associated linear automorphism. -/
noncomputable def linearEquiv (D : PositiveDiagonalChange S) : (S → ℝ) ≃ₗ[ℝ] (S → ℝ) where
  toFun := D.map
  invFun := D.invMap
  left_inv := D.invMap_map
  right_inv := D.map_invMap
  map_add' := by intros; ext s; simp [map, mul_add]
  map_smul' := by intros; ext s; simp [map, mul_assoc, mul_left_comm]

/-- Positive orthants are preserved. -/
theorem map_positive (D : PositiveDiagonalChange S) {x : S → ℝ}
    (hx : ∀ s, 0 < x s) : ∀ s, 0 < D.map x s := by
  intro s
  exact mul_pos (D.positive s) (hx s)

/-- Diagonal matrix of the coordinate change. -/
def matrix (D : PositiveDiagonalChange S) : Matrix S S ℝ :=
  Matrix.diagonal D.scale

/-- Diagonal matrix of the inverse coordinate change. -/
noncomputable def invMatrix (D : PositiveDiagonalChange S) : Matrix S S ℝ :=
  Matrix.diagonal fun s => (D.scale s)⁻¹

end PositiveDiagonalChange

/-- Positive-diagonal conjugacy of two mass-action systems. -/
def MassActionLinearlyConjugate (N M : Network S)
    (κN : N.RateConstants) (κM : M.RateConstants)
    (D : PositiveDiagonalChange S) : Prop :=
  ∀ x : Concentration S,
    M.massActionVectorField κM (D.map x) =
      D.map (N.massActionVectorField κN x)

/-- Dynamical equivalence is conjugacy by the identity diagonal change. -/
noncomputable def identityDiagonalChange (S : Type) [Fintype S] : PositiveDiagonalChange S where
  scale := fun _ => 1
  positive := fun _ => by norm_num

/-- Linear conjugacy transports steady states. -/
theorem MassActionLinearlyConjugate.map_steadyState
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κN x) :
    M.IsMassActionSteadyState κM (D.map x) := by
  unfold IsMassActionSteadyState IsSteadyState at hx ⊢
  intro s
  have hfield := congrFun (h x) s
  -- unfold `map` in the hypothesis first, otherwise `hx s` has nothing to rewrite
  simp only [PositiveDiagonalChange.map] at hfield
  rw [hx s] at hfield
  simpa using hfield

/-- Linear conjugacy transports steady states bijectively. -/
theorem MassActionLinearlyConjugate.steadyState_iff
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    (x : Concentration S) :
    N.IsMassActionSteadyState κN x ↔
      M.IsMassActionSteadyState κM (D.map x) := by
  constructor
  · exact h.map_steadyState
  · intro hm
    -- apply the conjugacy identity at the inverse-rescaled state
    unfold IsMassActionSteadyState IsSteadyState at hm ⊢
    have hf := h x
    intro s
    have hs := congrFun hf s
    have hm0 := hm s
    -- `nlinarith` cannot see inside the sums; the step is `scale s * v = 0` with
    -- `scale s > 0`, so use `mul_eq_zero` directly.
    simp only [PositiveDiagonalChange.map] at hs hm0 ⊢
    rw [hs] at hm0
    exact (mul_eq_zero.mp hm0).resolve_left (D.positive s).ne'

/-- Stoichiometric conjugacy: the species scaling maps one stoichiometric subspace to the
other.  This additional structural hypothesis ensures compatibility classes correspond. -/
def StoichiometricallyConjugate (N M : Network S) (D : PositiveDiagonalChange S) : Prop :=
  N.stoichSubspace.map D.linearEquiv.toLinearMap = M.stoichSubspace

/-- Under stoichiometric conjugacy, compatible concentrations map to compatible
concentrations. -/
theorem StoichiometricallyConjugate.map_compatible
    {N M : Network S} {D : PositiveDiagonalChange S}
    (h : N.StoichiometricallyConjugate M D)
    {x y : Concentration S} (hxy : N.StoichCompatible x y) :
    M.StoichCompatible (D.map x) (D.map y) := by
  rw [StoichCompatible, ← h]
  refine ⟨y - x, hxy, ?_⟩
  change D.map (y - x) = D.map y - D.map x
  funext s
  simp [PositiveDiagonalChange.map]
  ring

/-- Jacobian similarity under a differentiable diagonal conjugacy. -/
theorem jacobian_similarity_of_linearConjugacy
    {N M : Network S} {κN : N.RateConstants} {κM : M.RateConstants}
    {D : PositiveDiagonalChange S}
    (h : N.MassActionLinearlyConjugate M κN κM D)
    (x : Concentration S) :
    M.massActionJacobian κM (D.map x) =
      D.matrix * N.massActionJacobian κN x * D.invMatrix := by
  let DL : Concentration S →L[ℝ] Concentration S :=
    D.linearEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hDL (y : Concentration S) : DL y = D.map y := by rfl
  have hL := (M.massActionVectorField_hasFDerivAt κM (D.map x)).comp x DL.hasFDerivAt
  have hR := DL.hasFDerivAt.comp x (N.massActionVectorField_hasFDerivAt κN x)
  have hLR : (M.massActionJacobianCLM κM (D.map x)).comp DL =
      DL.comp (N.massActionJacobianCLM κN x) := by
    apply hL.unique
    apply hR.congr_of_eventuallyEq
    filter_upwards [] with y
    simp only [Function.comp_apply]
    exact h y
  apply Matrix.ext
  intro i j
  let e : Concentration S := Pi.single j 1
  have hDe : D.map e = Pi.single j (D.scale j) := by
    funext s
    by_cases hs : s = j
    · subst s
      simp [PositiveDiagonalChange.map, e]
    · simp [PositiveDiagonalChange.map, e, Pi.single_apply, hs]
  have hop := congrArg (fun L : Concentration S →L[ℝ] Concentration S => L e) hLR
  have hcoord := congrFun hop i
  simp only [ContinuousLinearMap.comp_apply] at hcoord
  rw [M.massActionJacobianCLM_apply, N.massActionJacobianCLM_apply] at hcoord
  rw [hDL, hDL, hDe] at hcoord
  simp only [Matrix.mulVec_single, Matrix.mulVec_single_one, Pi.smul_apply,
    Matrix.col_apply, smul_eq_mul] at hcoord
  change M.massActionJacobian κM (D.map x) i j =
    ((Matrix.diagonal D.scale * N.massActionJacobian κN x) *
      Matrix.diagonal (fun s => (D.scale s)⁻¹)) i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  change M.massActionJacobian κM (D.map x) i j =
    (D.scale i * N.massActionJacobian κN x i j) * (D.scale j)⁻¹
  have hj : D.scale j ≠ 0 := (D.positive j).ne'
  apply (eq_mul_inv_iff_mul_eq₀ hj).2
  simp [PositiveDiagonalChange.map, e, op_smul_eq_mul] at hcoord
  simpa [mul_comm] using hcoord

/-- Local spectral properties invariant under matrix similarity can therefore be
transported between linearly conjugate realizations. -/
def HasJacobianSimilarityAt (N M : Network S)
    (κN : N.RateConstants) (κM : M.RateConstants)
    (D : PositiveDiagonalChange S) (x : Concentration S) : Prop :=
  M.massActionJacobian κM (D.map x) =
    D.matrix * N.massActionJacobian κN x * D.invMatrix

end Network
end CRNT
