import CRNT.Stability.BDCPrincipalMinors
import CRNT.LinearAlgebra.CauchyBinet

/-!
# Cauchy--Binet compatibility for BDC principal minors

The structural Jacobian factors as a stoichiometric matrix times a reactant-derivative matrix.
The original version of this file tried to enumerate arbitrary finite species and reaction types
with `Finset.orderEmbOfFin`; that construction silently requires a `LinearOrder` on those types and
therefore did not elaborate for the public CRNT API.

The order-free theorem needed downstream is the determinant expansion itself.  It is proved in
`BDCPrincipalMinors` directly from the Leibniz formula by expanding the finite product of reaction
sums.  This is exactly the finite Cauchy--Binet/multilinearity content, but avoids choosing any
spurious global order on species or reactions.  This module keeps the matrix factorization and the
historical compatibility theorem used by downstream stability code.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Stoichiometric matrix with reaction columns. -/
def bdcStoichMatrix (N : Network S) : Matrix S N.R ℝ :=
  fun s r => N.reactionVector r s

/-- Reactivity matrix with reaction rows and species columns. -/
def bdcReactivityMatrix (N : Network S) (d : N.R → S → ℝ) : Matrix N.R S ℝ :=
  fun r s => d r s

/-- Matrix form of the BDC factorization `J = N D`. -/
theorem bdcJacobian_eq_stoich_mul_reactivity (N : Network S) (d : N.R → S → ℝ) :
    N.bdcJacobian d = N.bdcStoichMatrix * N.bdcReactivityMatrix d := by
  ext i j
  simp [bdcJacobian, bdcStoichMatrix, bdcReactivityMatrix, Matrix.mul_apply]

/-- A reaction subset can support a nonzero Cauchy--Binet term only when it has the right
cardinality and admits a reactant-pair matching to the selected species.  This definition is
order-free. -/
def IsAdmissibleReactionSubset (N : Network S) (I : Finset S) (R : Finset N.R) : Prop :=
  R.card = I.card ∧
    ∃ e : I ≃ R, ∀ i : I, N.IsReactantPair (e i).1 i.1

/-- Order-free Cauchy--Binet/Leibniz expansion of a BDC principal minor.

This compatibility theorem deliberately exposes the canonical selection expansion rather than an
order-dependent enumeration of reaction subsets. -/
theorem det_bdc_principal_expansion_via_cauchyBinet
    (N : Network S) (d : N.R → S → ℝ) (I : Finset S) :
    ((N.bdcJacobian d).submatrix (fun i : I => (i : S)) (fun i : I => (i : S))).det =
      ∑ sel : I → N.R,
        N.selectionCoefficient I sel * N.selectionReactivityMonomial I d sel := by
  exact N.det_bdc_principal_expansion d I

end Network
end CRNT
