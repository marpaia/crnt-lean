import CRNT.Stability.BDC
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Principal-minor coefficients of the BDC family

By multilinearity of the determinant, a principal minor of `J(d)` expands over choices
of one reaction for each selected species.  Each coefficient is a determinant of the
corresponding stoichiometric child-selection matrix, while the monomial records the
independent reaction--reactant derivatives.

This is the precise finite coefficient criterion behind BDC structural P/P0 tests.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Stoichiometric matrix associated with a reaction choice for every selected species. -/
def selectionStoichMatrix (N : Network S) (I : Finset S) (sel : I → N.R) :
    Matrix I I ℝ :=
  fun i j => N.reactionVector (sel j) i.1

/-- Stoichiometric determinant coefficient of a reaction selection. -/
def selectionCoefficient (N : Network S) (I : Finset S) (sel : I → N.R) : ℝ :=
  (N.selectionStoichMatrix I sel).det

/-- Reactivity monomial associated with a selection. -/
def selectionReactivityMonomial (N : Network S) (I : Finset S)
    (d : N.R → S → ℝ) (sel : I → N.R) : ℝ :=
  ∏ j : I, d (sel j) j.1

/-- **Multilinear principal-minor expansion.** -/
theorem det_bdc_principal_expansion (N : Network S) (d : N.R → S → ℝ)
    (I : Finset S) :
    ((N.bdcJacobian d).submatrix (fun i : I => (i : S)) (fun i : I => (i : S))).det =
      ∑ sel : I → N.R,
        N.selectionCoefficient I sel * N.selectionReactivityMonomial I d sel := by
  simp only [Matrix.det_apply', bdcJacobian, Matrix.submatrix_apply,
    Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ,
    selectionCoefficient, selectionStoichMatrix, selectionReactivityMonomial]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sel _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.prod_mul_distrib]
  ring

/-- Coefficient sign required for every principal minor of `-J(d)` to be nonnegative. -/
def HasBDCNonnegativePrincipalCoefficients (N : Network S) : Prop :=
  ∀ (I : Finset S) (sel : I → N.R),
    0 ≤ (-1 : ℝ) ^ I.card * N.selectionCoefficient I sel

/-- Strict structural P condition: nonnegative coefficients, and for every nonempty
principal index set at least one admissible reaction selection has a strictly positive
coefficient. -/
def HasBDCPositivePrincipalCertificate (N : Network S) : Prop :=
  N.HasBDCNonnegativePrincipalCoefficients ∧
  ∀ I : Finset S, I.Nonempty →
    ∃ sel : I → N.R,
      (∀ j : I, N.IsReactantPair (sel j) j.1) ∧
      0 < (-1 : ℝ) ^ I.card * N.selectionCoefficient I sel

/-- Under coefficient nonnegativity, every closed-admissible BDC matrix has
nonnegative signed principal minors. -/
theorem signed_principalMinor_nonneg_of_BDCcoefficients (N : Network S)
    (hcoef : N.HasBDCNonnegativePrincipalCoefficients)
    {d : N.R → S → ℝ} (hd : N.IsClosedAdmissibleReactivity d)
    (I : Finset S) :
    0 ≤ (-1 : ℝ) ^ I.card *
      ((N.bdcJacobian d).submatrix (fun i : I => (i : S)) (fun i : I => (i : S))).det := by
  rw [N.det_bdc_principal_expansion d I]
  rw [Finset.mul_sum]
  apply Finset.sum_nonneg
  intro sel _
  -- goal is `(-1)^card * (coef * monomial)`; regroup so `mul_nonneg` matches
  rw [← mul_assoc]
  apply mul_nonneg (hcoef I sel)
  unfold selectionReactivityMonomial
  apply Finset.prod_nonneg
  intro j _
  by_cases hr : N.IsReactantPair (sel j) j.1
  · exact (by simpa [hr] using hd (sel j) j.1)
  · have := hd (sel j) j.1
    simp [hr] at this
    simp [this]

/-- A positive coefficient certificate makes `-J(d)` a P-matrix for every strictly
admissible reactivity matrix. -/
theorem neg_bdcJacobian_isPMatrix_of_certificate (N : Network S)
    (hcert : N.HasBDCPositivePrincipalCertificate)
    {d : N.R → S → ℝ} (hd : N.IsAdmissibleReactivity d) :
    (-N.bdcJacobian d).IsPMatrix := by
  intro I
  by_cases hI : I.Nonempty
  · obtain ⟨sel, hreact, hpos⟩ := hcert.2 I hI
    have hexpand := N.det_bdc_principal_expansion d I
    have hmono_nonneg : ∀ t : I → N.R,
        0 ≤ N.selectionReactivityMonomial I d t := by
      intro t
      unfold selectionReactivityMonomial
      exact Finset.prod_nonneg fun j _ => by
        have hdt := hd (t j) j.1
        by_cases hr : N.IsReactantPair (t j) j.1
        · exact le_of_lt (by simpa [hr] using hdt)
        · simp [hr] at hdt
          simp [hdt]
    have hmono_pos : 0 < N.selectionReactivityMonomial I d sel := by
      unfold selectionReactivityMonomial
      exact Finset.prod_pos fun j _ => by
        have hdt := hd (sel j) j.1
        simpa [hreact j] using hdt
    have hsum_nonneg : ∀ t ∈ (Finset.univ : Finset (I → N.R)),
        0 ≤ ((-1 : ℝ) ^ I.card * N.selectionCoefficient I t) *
          N.selectionReactivityMonomial I d t := by
      intro t _
      exact mul_nonneg (hcert.1 I t) (hmono_nonneg t)
    have hterm_pos : 0 < ((-1 : ℝ) ^ I.card * N.selectionCoefficient I sel) *
        N.selectionReactivityMonomial I d sel :=
      mul_pos hpos hmono_pos
    have hsum_pos : 0 < ∑ t : I → N.R,
        ((-1 : ℝ) ^ I.card * N.selectionCoefficient I t) *
          N.selectionReactivityMonomial I d t := by
      apply Finset.sum_pos' hsum_nonneg
      exact ⟨sel, Finset.mem_univ _, hterm_pos⟩
    have hJpos : 0 < (-1 : ℝ) ^ I.card *
        ((N.bdcJacobian d).submatrix (fun i : I => (i : S)) (fun i : I => (i : S))).det := by
      rw [hexpand, Finset.mul_sum]
      simpa [mul_assoc] using hsum_pos
    have hsubneg :
        (-N.bdcJacobian d).submatrix (fun i : I => (i : S)) (fun i : I => (i : S)) =
          -((N.bdcJacobian d).submatrix (fun i : I => (i : S)) (fun i : I => (i : S))) := by
      ext a b
      rfl
    rw [hsubneg, Matrix.det_neg]
    simpa using hJpos
  · have : I = ∅ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    simp

/-- Consequently every positive mass-action Jacobian has `-J(x)` a P-matrix whenever
the structural BDC certificate holds. -/
theorem neg_massActionJacobian_isPMatrix_of_BDCcertificate (N : Network S)
    (hcert : N.HasBDCPositivePrincipalCertificate) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) :
    (-N.massActionJacobian κ x).IsPMatrix := by
  rw [← N.bdcJacobian_massAction κ x]
  exact N.neg_bdcJacobian_isPMatrix_of_certificate hcert
    (N.massActionPairReactivity_admissible κ hx)

end Network

end CRNT
