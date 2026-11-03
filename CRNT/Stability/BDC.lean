import CRNT.Kinetics.MassActionJacobian
import CRNT.Multistationarity.PMatrix

/-!
# BDC structural Jacobian factorization

For monotone reactant-dependent kinetics, each independent derivative belongs to a
**reaction--reactant pair** `(r,s)`, not merely to a reaction.  The structural Jacobian is

`J(d)_{ij} = Σ_r N_{ir} d_{rj}`,

where `d_{rj}>0` when species `j` is a reactant of `r` and `d_{rj}=0` otherwise.
This is the BDC / qualitative-Jacobian family used in structural CRNT stability and
injectivity theory.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A pair `(reaction, species)` is a reactant pair when the species appears in the
source complex. -/
def IsReactantPair (N : Network S) (r : N.R) (s : S) : Prop :=
  (N.reaction r).source s ≠ 0

instance decidableIsReactantPair (N : Network S) (r : N.R) (s : S) :
    Decidable (N.IsReactantPair r s) :=
  inferInstanceAs (Decidable ((N.reaction r).source s ≠ 0))

/-- Reactivity matrix compatible with monotone reactant dependence. -/
def IsAdmissibleReactivity (N : Network S) (d : N.R → S → ℝ) : Prop :=
  ∀ r s,
    if N.IsReactantPair r s then 0 < d r s else d r s = 0

/-- Nonnegative closure of the admissible reactivity cone. -/
def IsClosedAdmissibleReactivity (N : Network S) (d : N.R → S → ℝ) : Prop :=
  ∀ r s,
    if N.IsReactantPair r s then 0 ≤ d r s else d r s = 0

/-- Structural BDC Jacobian family. -/
def bdcJacobian (N : Network S) (d : N.R → S → ℝ) : Matrix S S ℝ :=
  fun i j => ∑ r : N.R, N.reactionVector r i * d r j

/-- Rank-one extremal corresponding to one reaction--reactant pair. -/
def bdcExtremal (N : Network S) (r : N.R) (s : S) : Matrix S S ℝ :=
  fun i j => if j = s then N.reactionVector r i else 0

/-- BDC Jacobians are conic combinations of pairwise rank-one extremals. -/
theorem bdcJacobian_eq_sum_extremals (N : Network S) (d : N.R → S → ℝ) :
    N.bdcJacobian d = ∑ r : N.R, ∑ s : S, d r s • N.bdcExtremal r s := by
  ext i j
  simp only [bdcJacobian, bdcExtremal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq, mul_comm]

/-- Mass-action reactivity written in pairwise derivative form. -/
def massActionPairReactivity (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.R → S → ℝ :=
  fun r s => κ.k r * massActionMonomialGrad (N.reaction r).source x s

/-- The mass-action Jacobian is a member of the BDC family. -/
theorem bdcJacobian_massAction (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) :
    N.bdcJacobian (N.massActionPairReactivity κ x) = N.massActionJacobian κ x := by
  ext i j
  simp [bdcJacobian, massActionPairReactivity, massActionJacobian]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- At a positive concentration, mass-action derivatives are structurally admissible:
strictly positive exactly at reactant pairs and zero elsewhere. -/
theorem massActionPairReactivity_admissible (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    N.IsAdmissibleReactivity (N.massActionPairReactivity κ x) := by
  intro r s
  by_cases hrs : N.IsReactantPair r s
  · simp [hrs, IsReactantPair, massActionPairReactivity]
    -- positive source exponent and positive concentration make the monomial derivative positive
    have hgrad : 0 < massActionMonomialGrad (N.reaction r).source x s := by
      unfold massActionMonomialGrad
      have hspos : 0 < (N.reaction r).source s := Nat.pos_of_ne_zero hrs
      have hcast : (0 : ℝ) < ((N.reaction r).source s : ℝ) := by exact_mod_cast hspos
      have hxs : 0 < x s := hx s
      have hprod : 0 < ∏ t ∈ Finset.univ.erase s, x t ^ ((N.reaction r).source t) :=
        Finset.prod_pos fun t _ => pow_pos (hx t) _
      exact mul_pos (mul_pos hcast (pow_pos hxs _)) hprod
    rw [if_neg hrs]
    exact mul_pos (κ.positive r) hgrad
  · simp [hrs, IsReactantPair, massActionPairReactivity]
    have hs0 : (N.reaction r).source s = 0 := by
      simpa [IsReactantPair] using hrs
    simp [massActionMonomialGrad, hs0]

/-- Every admissible BDC family contains all positive mass-action Jacobians. -/
theorem massActionJacobian_mem_bdcFamily (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    ∃ d, N.IsAdmissibleReactivity d ∧ N.massActionJacobian κ x = N.bdcJacobian d := by
  exact ⟨N.massActionPairReactivity κ x,
    N.massActionPairReactivity_admissible κ hx,
    (N.bdcJacobian_massAction κ x).symm⟩

end Network

end CRNT
