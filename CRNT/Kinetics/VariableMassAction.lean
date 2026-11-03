import CRNT.Kinetics.MassAction

/-!
# Variable-k mass-action systems

A variable-k mass-action system has the same reaction monomials and reaction vectors as an
ordinary mass-action system, but its positive reaction coefficients may vary with time.  This is
the minimal kinetic abstraction needed by the projection argument in strongly-endotactic
permanence proofs.
-/

open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Positive time-dependent reaction coefficients. -/
structure VariableRateConstants (N : Network S) where
  k : ℝ → N.R → ℝ
  positive : ∀ t r, 0 < k t r

/-- Variable-k mass-action rate of one reaction. -/
def variableMassActionRate (N : Network S) (κ : N.VariableRateConstants)
    (t : ℝ) (r : N.R) (x : Concentration S) : ℝ :=
  κ.k t r * (N.reaction r).source.massActionMonomial x

/-- Variable-k mass-action vector field. -/
def variableMassActionVectorField (N : Network S) (κ : N.VariableRateConstants)
    (t : ℝ) (x : Concentration S) : Concentration S :=
  fun s => ∑ r : N.R, N.variableMassActionRate κ t r x * N.reactionVector r s

@[simp] theorem variableMassActionVectorField_apply (N : Network S)
    (κ : N.VariableRateConstants) (t : ℝ) (x : Concentration S) (s : S) :
    N.variableMassActionVectorField κ t x s =
      ∑ r : N.R, N.variableMassActionRate κ t r x * N.reactionVector r s := rfl

/-- Uniform lower/upper control on variable reaction coefficients. -/
def VariableRateConstants.UniformlyBounded {N : Network S} (κ : N.VariableRateConstants)
    (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ t r, δ ≤ κ.k t r ∧ κ.k t r ≤ δ⁻¹

/-- Embed ordinary constant rate constants into the variable-k API. -/
def RateConstants.toVariable {N : Network S} (κ : N.RateConstants) :
    N.VariableRateConstants where
  k := fun _ r => κ.k r
  positive := fun _ r => κ.positive r

@[simp] theorem variableMassActionRate_const (N : Network S) (κ : N.RateConstants)
    (t : ℝ) (r : N.R) (x : Concentration S) :
    N.variableMassActionRate κ.toVariable t r x = N.massActionRate κ r x := rfl

@[simp] theorem variableMassActionVectorField_const (N : Network S) (κ : N.RateConstants)
    (t : ℝ) (x : Concentration S) :
    N.variableMassActionVectorField κ.toVariable t x = N.massActionVectorField κ x := by
  rfl

/-- A variable-k rate is nonnegative at a nonnegative concentration. -/
theorem variableMassActionRate_nonneg (N : Network S) (κ : N.VariableRateConstants)
    (t : ℝ) (r : N.R) {x : Concentration S} (hx : x.Nonnegative) :
    0 ≤ N.variableMassActionRate κ t r x :=
  mul_nonneg (κ.positive t r).le (Complex.massActionMonomial_nonneg hx _)

/-- A variable-k rate is positive at a positive concentration. -/
theorem variableMassActionRate_pos (N : Network S) (κ : N.VariableRateConstants)
    (t : ℝ) (r : N.R) {x : Concentration S} (hx : x.Positive) :
    0 < N.variableMassActionRate κ t r x :=
  mul_pos (κ.positive t r) (Complex.massActionMonomial_pos hx _)

end Network
end CRNT
