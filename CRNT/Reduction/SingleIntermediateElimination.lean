import CRNT.Reduction.Intermediates
import Mathlib.Tactic.FieldSimp

/-!
# Explicit elimination of one linear intermediate

The simplest intermediate motif is

`y --k₁--> H`,  `H --k₂--> z₁`, ..., `H --k_m--> z_m`.

At steady state the intermediate equation is linear:

`0 = k₁ x^y - (Σ_j k_j) x_H`,

so

`x_H = k₁/(Σ_j k_j) x^y`.

Substitution gives effective core reactions `y -> z_j` with rates
`k₁ k_j/(Σ_l k_l)`.  This file records that algebra independently of a particular
network-construction API, making it reusable as the local kernel of the general intermediate
elimination theorem.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Algebraic data for one intermediate fed by one core monomial and drained by finitely many
first-order exits. -/
structure SingleIntermediateKineticData (S : Type) [Fintype S] where
  inputComplex : Complex S
  exitIndex : Type
  [exitFintype : Fintype exitIndex]
  [exitNonempty : Nonempty exitIndex]
  inputRate : ℝ
  exitRate : exitIndex → ℝ
  inputRate_pos : 0 < inputRate
  exitRate_pos : ∀ j, 0 < exitRate j

attribute [instance] SingleIntermediateKineticData.exitFintype
attribute [instance] SingleIntermediateKineticData.exitNonempty

namespace SingleIntermediateKineticData

/-- Total first-order loss rate of the intermediate. -/
def totalExitRate (D : SingleIntermediateKineticData S) : ℝ :=
  ∑ j : D.exitIndex, D.exitRate j

/-- Total exit rate is positive. -/
theorem totalExitRate_pos (D : SingleIntermediateKineticData S) : 0 < D.totalExitRate := by
  unfold totalExitRate
  exact Finset.sum_pos (fun j _ => D.exitRate_pos j) ⟨Classical.choice (inferInstance : Nonempty D.exitIndex), by simp⟩

/-- Steady-state intermediate concentration induced by a core state. -/
noncomputable def intermediateSteadyConcentration (D : SingleIntermediateKineticData S)
    (x : Concentration S) : ℝ :=
  D.inputRate / D.totalExitRate * D.inputComplex.massActionMonomial x

/-- Effective core rate for exit channel `j`. -/
noncomputable def effectiveRate (D : SingleIntermediateKineticData S) (j : D.exitIndex) : ℝ :=
  D.inputRate * D.exitRate j / D.totalExitRate

/-- Effective rates are positive. -/
theorem effectiveRate_pos (D : SingleIntermediateKineticData S) (j : D.exitIndex) :
    0 < D.effectiveRate j := by
  exact div_pos (mul_pos D.inputRate_pos (D.exitRate_pos j)) D.totalExitRate_pos

/-- The explicit steady-state elimination formula solves the intermediate balance equation. -/
theorem intermediate_balance
    (D : SingleIntermediateKineticData S) (x : Concentration S) :
    D.inputRate * D.inputComplex.massActionMonomial x -
      D.totalExitRate * D.intermediateSteadyConcentration x = 0 := by
  unfold intermediateSteadyConcentration
  field_simp [D.totalExitRate_pos.ne']
  ring

/-- Flux through exit `j` after eliminating the intermediate is exactly the effective core
mass-action flux. -/
theorem eliminated_exit_flux
    (D : SingleIntermediateKineticData S) (x : Concentration S) (j : D.exitIndex) :
    D.exitRate j * D.intermediateSteadyConcentration x =
      D.effectiveRate j * D.inputComplex.massActionMonomial x := by
  unfold intermediateSteadyConcentration effectiveRate
  field_simp [D.totalExitRate_pos.ne']

/-- Effective rates partition the input rate: all input flux eventually leaves through one of
the exit channels. -/
theorem sum_effectiveRate (D : SingleIntermediateKineticData S) :
    ∑ j : D.exitIndex, D.effectiveRate j = D.inputRate := by
  unfold effectiveRate
  calc
    (∑ j : D.exitIndex, D.inputRate * D.exitRate j / D.totalExitRate)
        = D.inputRate / D.totalExitRate * ∑ j : D.exitIndex, D.exitRate j := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = D.inputRate := by
      change D.inputRate / D.totalExitRate * D.totalExitRate = D.inputRate
      field_simp [D.totalExitRate_pos.ne']

/-- Positivity of the core monomial implies positivity of the eliminated intermediate. -/
theorem intermediateSteadyConcentration_pos
    (D : SingleIntermediateKineticData S) {x : Concentration S} (hx : x.Positive) :
    0 < D.intermediateSteadyConcentration x := by
  exact mul_pos (div_pos D.inputRate_pos D.totalExitRate_pos)
    (Complex.massActionMonomial_pos hx D.inputComplex)

end SingleIntermediateKineticData

end Network
end CRNT
