import CRNT.Oscillation.KineticBasic
import CRNT.Oscillation.MatrixCriteria
import CRNT.Stoich.Subspace

/-!
# Parameter-rich kinetics and symbolic Jacobians

This file formalizes the local objects used by the parameter-rich oscillation framework of
Blokhuis--Stadler--Vassena.

A reactivity matrix has one row per reaction and one column per species.  Its entries are strictly
positive exactly where that species occurs in the reaction source and zero otherwise.  The
corresponding symbolic Jacobian is `G = S R`, written directly from reaction vectors so it does not
depend on a particular matrix representation of `S`.

`Kinetics.RealizesReactivityAt` states that the coordinate partial derivatives of the reaction rates
at a point are exactly the entries of `R`.  The theorem `vectorField_coordinate_hasDerivAt` then
proves, rather than assumes, that the partial derivatives of the induced vector field are the
entries of the symbolic Jacobian.

`SteadyStateParameterRichFamily` is an operational family-level interface: every positive state and
every admissible reactivity matrix can be realized by a member of the family for which that state is
a steady state.  This packages the derivative freedom and the steady-state parameter inversion used
by the oscillatory-core arguments while keeping it distinct from mass action.
-/

namespace CRNT

open scoped BigOperators

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A reaction-by-species reactivity matrix. -/
abbrev ReactivityMatrix (N : Network S) := Matrix N.R S ℝ

/-- Reactivity matrices are positive exactly at reactant incidences and zero off the source support. -/
structure IsReactivityMatrix (N : Network S) (R : N.ReactivityMatrix) : Prop where
  positive_on_reactants : ∀ r s, 0 < (N.reaction r).source s → 0 < R r s
  zero_off_reactants : ∀ r s, (N.reaction r).source s = 0 → R r s = 0

/-- The symbolic Jacobian `S R`, expressed directly as a sum of reaction-vector columns. -/
def symbolicJacobian (N : Network S) (R : N.ReactivityMatrix) : Matrix S S ℝ :=
  fun i j => ∑ r : N.R, N.reactionVector r i * R r j

@[simp] theorem symbolicJacobian_apply (N : Network S) (R : N.ReactivityMatrix) (i j : S) :
    N.symbolicJacobian R i j = ∑ r : N.R, N.reactionVector r i * R r j :=
  rfl

/-- Linear interpolation between two reactivity matrices. -/
def interpolateReactivity (N : Network S) (R₀ R₁ : N.ReactivityMatrix) (μ : ℝ) :
    N.ReactivityMatrix :=
  fun r s => (1 - μ) * R₀ r s + μ * R₁ r s

/-- Convex interpolation preserves the strict reactivity sign/support pattern. -/
theorem IsReactivityMatrix.interpolate {N : Network S} {R₀ R₁ : N.ReactivityMatrix}
    (h₀ : N.IsReactivityMatrix R₀) (h₁ : N.IsReactivityMatrix R₁)
    {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) :
    N.IsReactivityMatrix (N.interpolateReactivity R₀ R₁ μ) := by
  constructor
  · intro r s hrs
    have hR₀ : 0 < R₀ r s := h₀.positive_on_reactants r s hrs
    have hR₁ : 0 < R₁ r s := h₁.positive_on_reactants r s hrs
    have hcoef : 0 ≤ 1 - μ := sub_nonneg.mpr hμ1
    by_cases hμ : μ = 0
    · subst μ
      simpa [interpolateReactivity] using hR₀
    · have hμpos : 0 < μ := lt_of_le_of_ne hμ0 (Ne.symm hμ)
      have hleft : 0 ≤ (1 - μ) * R₀ r s := mul_nonneg hcoef hR₀.le
      have hright : 0 < μ * R₁ r s := mul_pos hμpos hR₁
      simpa [interpolateReactivity] using add_pos_of_nonneg_of_pos hleft hright
  · intro r s hrs
    rw [interpolateReactivity, h₀.zero_off_reactants r s hrs, h₁.zero_off_reactants r s hrs]
    ring

namespace Kinetics

variable {N : Network S}

/-- A kinetics realizes a reactivity matrix at `x` when every coordinate partial derivative of every
reaction rate equals the corresponding matrix entry.  The partial derivative is represented by
varying only coordinate `s` through `Function.update`. -/
def RealizesReactivityAt (K : N.Kinetics) (x : Concentration S)
    (R : N.ReactivityMatrix) : Prop :=
  ∀ r s, HasDerivAt (fun z : ℝ => K.rate r (Function.update x s z)) (R r s) (x s)

/-- If the reaction-rate partials realize `R`, then each coordinate partial derivative of the full
vector field is the corresponding entry of the symbolic Jacobian `S R`. -/
theorem vectorField_coordinate_hasDerivAt (K : N.Kinetics) (x : Concentration S)
    (R : N.ReactivityMatrix) (hR : K.RealizesReactivityAt x R) (i j : S) :
    HasDerivAt (fun z : ℝ => K.vectorField (Function.update x j z) i)
      (N.symbolicJacobian R i j) (x j) := by
  have hsum : HasDerivAt
      (fun z : ℝ => ∑ r : N.R,
        K.rate r (Function.update x j z) * N.reactionVector r i)
      (∑ r : N.R, R r j * N.reactionVector r i) (x j) := by
    -- `HasDerivAt.sum` produces `∑ r, (fun z => …)`, a sum of *functions*; the goal is a
    -- function of a sum, so bridge with `Finset.sum_apply`.
    have h := HasDerivAt.sum (u := (Finset.univ : Finset N.R))
      (fun r (_ : r ∈ (Finset.univ : Finset N.R)) =>
        (hR r j).mul_const (N.reactionVector r i))
    have hfun : (∑ r : N.R, fun z : ℝ =>
        K.rate r (Function.update x j z) * N.reactionVector r i)
        = fun z : ℝ => ∑ r : N.R,
          K.rate r (Function.update x j z) * N.reactionVector r i := by
      funext z
      simp [Finset.sum_apply]
    rw [hfun] at h
    exact h
  simpa [Network.Kinetics.vectorField, Network.symbolicJacobian, mul_comm] using hsum

end Kinetics

/-- An operational parameter-rich family: at every positive state, every admissible reactivity
matrix can be attained by a family member for which that state is a kinetic steady state. -/
structure SteadyStateParameterRichFamily (N : Network S) : Type where
  members : Set N.Kinetics
  realize : ∀ (x : Concentration S), x.Positive →
    ∀ (R : N.ReactivityMatrix), N.IsReactivityMatrix R →
      ∃ K : N.Kinetics, K ∈ members ∧ N.IsKineticSteadyState K x ∧ K.RealizesReactivityAt x R

/-- A coherent smooth realization of the straight-line path between two reactivity matrices, at a
fixed positive steady state.  Smoothness is imposed on the jointly parameter/state-dependent vector
field, which is the regularity consumed by the later global-Hopf frontier. -/
structure SmoothLinearReactivityRealization (N : Network S)
    (F : N.SteadyStateParameterRichFamily) (x : Concentration S)
    (R₀ R₁ : N.ReactivityMatrix) : Type where
  kinetics : ℝ → N.Kinetics
  member : ∀ μ ∈ Set.Icc (0 : ℝ) 1, kinetics μ ∈ F.members
  steady : ∀ μ ∈ Set.Icc (0 : ℝ) 1, N.IsKineticSteadyState (kinetics μ) x
  realizes : ∀ μ ∈ Set.Icc (0 : ℝ) 1,
    (kinetics μ).RealizesReactivityAt x (N.interpolateReactivity R₀ R₁ μ)
  smooth_field : ContDiff ℝ ⊤
    (fun p : ℝ × Concentration S => (kinetics p.1).vectorField p.2)

/-- The family can realize every straight reactivity interpolation by one coherent smooth kinetic
path, not merely choose unrelated kinetics pointwise. -/
def SupportsSmoothReactivityPaths (N : Network S) (F : N.SteadyStateParameterRichFamily) : Prop :=
  ∀ (x : Concentration S), x.Positive →
    ∀ (R₀ R₁ : N.ReactivityMatrix), N.IsReactivityMatrix R₀ → N.IsReactivityMatrix R₁ →
      Nonempty (N.SmoothLinearReactivityRealization F x R₀ R₁)

/-- **Symbolic nondegeneracy on the stoichiometric rank.**  There is an admissible reactivity
matrix whose symbolic Jacobian has a nonsingular principal block of size exactly the stoichiometric
rank.  This is the finite rank-reduced nondegeneracy notion needed when conservation laws force the
full species-space Jacobian to be singular. -/
def IsSymbolicallyNondegenerate (N : Network S) : Prop :=
  ∃ (R : N.ReactivityMatrix), N.IsReactivityMatrix R ∧
    ∃ I : Finset S, I.card = N.stoichRank ∧
      ((N.symbolicJacobian R).principalSubmatrix I).det ≠ 0

/-- A concrete rank-sized nonsingular symbolic-Jacobian block is a witness of symbolic
nondegeneracy. -/
theorem isSymbolicallyNondegenerate_of_witness (N : Network S)
    {R : N.ReactivityMatrix} (hR : N.IsReactivityMatrix R)
    {I : Finset S} (hcard : I.card = N.stoichRank)
    (hdet : ((N.symbolicJacobian R).principalSubmatrix I).det ≠ 0) :
    N.IsSymbolicallyNondegenerate :=
  ⟨R, hR, I, hcard, hdet⟩

/-- Oscillatory capacity *inside a specified parameter-rich family*. -/
def ParameterRichOscillatoryCapacity (N : Network S) (F : N.SteadyStateParameterRichFamily) : Prop :=
  ∃ K : N.Kinetics, K ∈ F.members ∧ N.HasPositiveKineticPeriodicOrbit K

/-- Forgetting the family turns parameter-rich oscillatory capacity into general admissible-kinetics
oscillatory capacity. -/
theorem kineticOscillatoryCapacity_of_parameterRich
    {N : Network S} {F : N.SteadyStateParameterRichFamily}
    (h : N.ParameterRichOscillatoryCapacity F) : N.KineticOscillatoryCapacity := by
  obtain ⟨K, _, hK⟩ := h
  exact ⟨K, hK⟩

end Network

end CRNT
