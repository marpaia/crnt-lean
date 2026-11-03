import CRNT.Stability.BDCCauchyBinetProof
import CRNT.Stability.BDCPrincipalMinors

/-!
# Structural nonsingularity of BDC Jacobian families

The Cauchy--Binet coefficient expansion turns a qualitative Jacobian question into a finite
sign question.  If all determinant monomials have one sign and at least one admissible
monomial is nonzero, then the corresponding minor cannot vanish for any positive reactivity
parameters.  This is the structural nonsingularity criterion used in BDC/DSR approaches.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Sign coherence for full-size BDC determinant coefficients. -/
def HasBDCDeterminantSignCoherence (N : Network S) : Prop :=
  ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
    (∀ sel : ↥(Finset.univ : Finset S) → N.R,
      0 ≤ σ * N.selectionCoefficient Finset.univ sel) ∧
    ∃ sel : ↥(Finset.univ : Finset S) → N.R,
      (∀ s, N.IsReactantPair (sel s) s.1) ∧
      0 < σ * N.selectionCoefficient Finset.univ sel

/-- Coherent nonzero determinant coefficients force every strictly admissible BDC Jacobian to
be nonsingular. -/
theorem bdcJacobian_nonsingular_of_signCoherence
    (N : Network S) (h : N.HasBDCDeterminantSignCoherence)
    {d : N.R → S → ℝ} (hd : N.IsAdmissibleReactivity d) :
    (N.bdcJacobian d).det ≠ 0 := by
  obtain ⟨σ, hσ, hnonneg, sel, hselreact, hselpos⟩ := h
  have hexp := N.det_bdc_principal_expansion_via_cauchyBinet d Finset.univ
  have hmono_nonneg : ∀ t : ↥(Finset.univ : Finset S) → N.R,
      0 ≤ N.selectionReactivityMonomial Finset.univ d t := by
    intro t
    unfold selectionReactivityMonomial
    exact Finset.prod_nonneg fun j _ => by
      have hdt := hd (t j) j.1
      by_cases hr : N.IsReactantPair (t j) j.1
      · exact le_of_lt (by simpa [hr] using hdt)
      · simp [hr] at hdt
        simp [hdt]
  have hmono_pos : 0 < N.selectionReactivityMonomial Finset.univ d sel := by
    unfold selectionReactivityMonomial
    exact Finset.prod_pos fun j _ => by
      have hdt := hd (sel j) j.1
      simpa [hselreact j] using hdt
  have hsum_nonneg : ∀ t ∈
      (Finset.univ : Finset (↥(Finset.univ : Finset S) → N.R)),
      0 ≤ (σ * N.selectionCoefficient Finset.univ t) *
        N.selectionReactivityMonomial Finset.univ d t := by
    intro t _
    exact mul_nonneg (hnonneg t) (hmono_nonneg t)
  have hterm_pos : 0 < (σ * N.selectionCoefficient Finset.univ sel) *
      N.selectionReactivityMonomial Finset.univ d sel :=
    mul_pos hselpos hmono_pos
  have hsum_pos : 0 < ∑ t : ↥(Finset.univ : Finset S) → N.R,
      (σ * N.selectionCoefficient Finset.univ t) *
        N.selectionReactivityMonomial Finset.univ d t := by
    apply Finset.sum_pos' hsum_nonneg
    exact ⟨sel, Finset.mem_univ _, hterm_pos⟩
  have hsigned_subdet : 0 < σ *
      ((N.bdcJacobian d).submatrix
        (fun i : (Finset.univ : Finset S) => (i : S))
        (fun i : (Finset.univ : Finset S) => (i : S))).det := by
    rw [hexp, Finset.mul_sum]
    simpa [mul_assoc] using hsum_pos
  have hsubdet_ne :
      ((N.bdcJacobian d).submatrix
        (fun i : (Finset.univ : Finset S) => (i : S))
        (fun i : (Finset.univ : Finset S) => (i : S))).det ≠ 0 := by
    intro hz
    rw [hz, mul_zero] at hsigned_subdet
    exact (lt_irrefl 0) hsigned_subdet
  let e : ↥(Finset.univ : Finset S) ≃ S :=
    { toFun := fun i => i.1
      invFun := fun s => ⟨s, Finset.mem_univ s⟩
      left_inv := fun i => Subtype.ext rfl
      right_inv := fun s => rfl }
  have heq :
      ((N.bdcJacobian d).submatrix
        (fun i : (Finset.univ : Finset S) => (i : S))
        (fun i : (Finset.univ : Finset S) => (i : S))).det =
        (N.bdcJacobian d).det := by
    simpa [e] using Matrix.det_submatrix_equiv_self e (N.bdcJacobian d)
  exact heq ▸ hsubdet_ne

/-- Structural nonsingularity of the BDC cone. -/
def IsBDCStructurallyNonsingular (N : Network S) : Prop :=
  ∀ d, N.IsAdmissibleReactivity d → (N.bdcJacobian d).det ≠ 0

/-- Sign coherence is a finite certificate of structural nonsingularity. -/
theorem BDCSignCoherence.structurallyNonsingular
    (N : Network S) (h : N.HasBDCDeterminantSignCoherence) :
    N.IsBDCStructurallyNonsingular := by
  intro d hd
  exact N.bdcJacobian_nonsingular_of_signCoherence h hd

/-- The same certificate applies to every positive mass-action Jacobian. -/
theorem massActionJacobian_nonsingular_of_BDCSignCoherence
    (N : Network S) (h : N.HasBDCDeterminantSignCoherence)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    (N.massActionJacobian κ x).det ≠ 0 := by
  rw [← N.bdcJacobian_massAction κ x]
  exact N.bdcJacobian_nonsingular_of_signCoherence h
    (N.massActionPairReactivity_admissible κ hx)

/-- A principal-minor certificate yields structural injectivity through the P-matrix layer. -/
theorem BDCPositivePrincipalCertificate.massAction_PMatrix
    (N : Network S) (h : N.HasBDCPositivePrincipalCertificate)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    (-N.massActionJacobian κ x).IsPMatrix :=
  N.neg_massActionJacobian_isPMatrix_of_BDCcertificate h κ hx

end Network
end CRNT
