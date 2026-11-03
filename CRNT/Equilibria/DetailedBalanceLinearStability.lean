import CRNT.Equilibria.DetailedBalanceEntropy
import CRNT.Kinetics.MassActionJacobian
import CRNT.Equilibria.ComplexBalanceGeometry

/-!
# Linear stability at detailed-balanced equilibria

At a positive reactionwise detailed-balanced equilibrium `x*`, pair every reaction with
its reverse.  If `q_r = k_r x*^{y_r}` and `ν_r` is the reaction vector, then

`J(x*) h = -(1/2) Σ_r q_r ν_r <ν_r, D(x*)⁻¹ h>`.

Consequently

`<D⁻¹h, J h> = -(1/2) Σ_r q_r <ν_r,D⁻¹h>² ≤ 0`.

Its nullspace is exactly the tangent space `diag(x*) Sᗮ` to the detailed-balanced
equilibrium manifold.  Restricting to the stoichiometric subspace removes those neutral
conservation directions, making the form strictly negative away from zero.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Weighted inverse-diagonal action `D(x)⁻¹ h`. -/
noncomputable def invDiagonalApply (x h : Concentration S) : S → ℝ :=
  fun s => h s / x s

/-- Euclidean finite-coordinate pairing. -/
def speciesDot (u v : S → ℝ) : ℝ :=
  ∑ s : S, u s * v s

/-- Pairing of a reaction vector against an inverse-scaled perturbation. -/
noncomputable def reactionLogLinearForm (N : Network S) (x h : Concentration S)
    (r : N.R) : ℝ :=
  ∑ s : S, N.reactionVector r s * (h s / x s)

/-- Equilibrium one-way reaction flux. -/
def equilibriumReactionFlux (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) (r : N.R) : ℝ :=
  N.massActionRate κ r xstar

/-- At a positive state, the monomial directional derivative admits the logarithmic
form `x^y <y,D⁻¹h>`. -/
theorem massActionMonomial_directional_derivative_logform
    (y : Complex S) {x : Concentration S} (hx : x.Positive)
    (h : Concentration S) :
    ∑ j : S, massActionMonomialGrad y x j * h j =
      y.massActionMonomial x * ∑ j : S, (y j : ℝ) * (h j / x j) := by
  classical
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hxj : x j ≠ 0 := ne_of_gt (hx j)
  -- `grad_j * x j = y j * monomial`, so `grad_j = y j * monomial / x j`.
  have hg := massActionMonomialGrad_mul_coord y x j
  field_simp
  linear_combination h j * hg

/-- The Jacobian action at a positive point in reaction-logarithmic form. -/
theorem massActionJacobian_mulVec_logform
    (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive) (h : Concentration S) :
    (N.massActionJacobian κ x).mulVec h =
      fun s => ∑ r : N.R,
        N.massActionRate κ r x *
          (∑ j : S, ((N.reaction r).source j : ℝ) * (h j / x j)) *
          N.reactionVector r s := by
  funext s
  simp only [Matrix.mulVec, dotProduct, massActionJacobian]
  calc
    (∑ j : S, (∑ r : N.R,
        κ.k r * massActionMonomialGrad (N.reaction r).source x j * N.reactionVector r s) * h j)
        = ∑ j : S, ∑ r : N.R,
            (κ.k r * massActionMonomialGrad (N.reaction r).source x j *
              N.reactionVector r s) * h j := by
            apply Finset.sum_congr rfl
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ r : N.R, ∑ j : S,
          (κ.k r * massActionMonomialGrad (N.reaction r).source x j *
            N.reactionVector r s) * h j := by
          rw [Finset.sum_comm]
    _ = ∑ r : N.R, N.massActionRate κ r x *
          (∑ j : S, ((N.reaction r).source j : ℝ) * (h j / x j)) *
          N.reactionVector r s := by
          apply Finset.sum_congr rfl
          intro r _
          have hder := massActionMonomial_directional_derivative_logform
            (N.reaction r).source hx h
          have hfactor :
              (∑ j : S,
                (κ.k r * massActionMonomialGrad (N.reaction r).source x j *
                  N.reactionVector r s) * h j) =
                κ.k r * N.reactionVector r s *
                  (∑ j : S, massActionMonomialGrad (N.reaction r).source x j * h j) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
          rw [hfactor, hder]
          simp only [massActionRate]
          ring
/-- **Paired detailed-balance Jacobian formula.** -/
theorem detailedBalance_Jacobian_pair_formula
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (h : Concentration S) :
    (N.massActionJacobian κ xstar).mulVec h =
      fun s => -(1 / 2 : ℝ) * ∑ r : N.R,
        N.equilibriumReactionFlux κ xstar r *
          N.reactionLogLinearForm xstar h r * N.reactionVector r s := by
  rw [N.massActionJacobian_mulVec_logform κ hxs h]
  funext s
  let q : N.R → ℝ := fun r => N.equilibriumReactionFlux κ xstar r
  let src : N.R → ℝ := fun r =>
    ∑ j : S, ((N.reaction r).source j : ℝ) * (h j / xstar j)
  let tgt : N.R → ℝ := fun r =>
    ∑ j : S, ((N.reaction r).target j : ℝ) * (h j / xstar j)
  have hqrev : ∀ r : N.R, q (ρ.rev r) = q r := by
    intro r
    simpa [q, equilibriumReactionFlux] using (hdb r).symm
  have hsrcrev : ∀ r : N.R, src (ρ.rev r) = tgt r := by
    intro r
    simp only [src, tgt, ρ.source_rev]
  have htgtrev : ∀ r : N.R, tgt (ρ.rev r) = src r := by
    intro r
    simp only [src, tgt, ρ.target_rev]
  have hnurev : ∀ r : N.R, N.reactionVector (ρ.rev r) s = -N.reactionVector r s := by
    intro r
    have hv := ρ.reactionVector_rev r
    exact congrFun hv s
  have hrevsum :
      (∑ r : N.R, q r * src r * N.reactionVector r s) =
        ∑ r : N.R, -(q r * tgt r * N.reactionVector r s) := by
    apply Fintype.sum_equiv ρ.equiv
    intro r
    change q r * src r * N.reactionVector r s =
      -(q (ρ.rev r) * tgt (ρ.rev r) * N.reactionVector (ρ.rev r) s)
    rw [hqrev, htgtrev, hnurev]
    ring
  have hform : ∀ r : N.R, N.reactionLogLinearForm xstar h r = tgt r - src r := by
    intro r
    unfold reactionLogLinearForm
    simp only [reactionVector_apply, tgt, src, sub_mul]
    rw [Finset.sum_sub_distrib]
  have hsplit :
      (∑ r : N.R, q r * N.reactionLogLinearForm xstar h r * N.reactionVector r s) =
        (∑ r : N.R, q r * tgt r * N.reactionVector r s) -
          (∑ r : N.R, q r * src r * N.reactionVector r s) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [hform r]
    ring
  -- normalize the right-hand sum through q/src names for the algebraic finish
  have hrevsum' :
      (∑ r : N.R, N.equilibriumReactionFlux κ xstar r *
          (∑ j : S, ((N.reaction r).source j : ℝ) * (h j / xstar j)) *
          N.reactionVector r s) =
        -(∑ r : N.R, N.equilibriumReactionFlux κ xstar r * tgt r *
          N.reactionVector r s) := by
    rw [← Finset.sum_neg_distrib]
    simpa [q, src] using hrevsum
  have hsplit' :
      (∑ r : N.R, N.equilibriumReactionFlux κ xstar r *
          N.reactionLogLinearForm xstar h r * N.reactionVector r s) =
        (∑ r : N.R, N.equilibriumReactionFlux κ xstar r * tgt r * N.reactionVector r s) -
          (∑ r : N.R, N.equilibriumReactionFlux κ xstar r *
            (∑ j : S, ((N.reaction r).source j : ℝ) * (h j / xstar j)) *
            N.reactionVector r s) := by
    simpa [q, src] using hsplit
  rw [hsplit']
  simp only [equilibriumReactionFlux] at hrevsum' ⊢
  linarith [hrevsum']
/-- Detailed-balance Jacobian weighted quadratic form. -/
noncomputable def detailedBalanceJacobianQuadratic
    (N : Network S) (κ : N.RateConstants)
    (xstar h : Concentration S) : ℝ :=
  speciesDot (invDiagonalApply xstar h)
    ((N.massActionJacobian κ xstar).mulVec h)

/-- **Sum-of-squares identity for the detailed-balance Jacobian.** -/
theorem detailedBalanceJacobianQuadratic_eq_neg_sum_sq
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (h : Concentration S) :
    N.detailedBalanceJacobianQuadratic κ xstar h =
      -(1 / 2 : ℝ) * ∑ r : N.R,
        N.equilibriumReactionFlux κ xstar r *
          (N.reactionLogLinearForm xstar h r)^2 := by
  unfold detailedBalanceJacobianQuadratic speciesDot invDiagonalApply
  rw [N.detailedBalance_Jacobian_pair_formula ρ κ hxs hdb h]
  simp only [Pi.mul_apply]
  calc
    (∑ s : S, (h s / xstar s) *
        (-(1 / 2 : ℝ) * ∑ r : N.R,
          N.equilibriumReactionFlux κ xstar r *
            N.reactionLogLinearForm xstar h r * N.reactionVector r s))
        = -(1 / 2 : ℝ) * ∑ s : S, ∑ r : N.R,
            (h s / xstar s) *
              (N.equilibriumReactionFlux κ xstar r *
                N.reactionLogLinearForm xstar h r * N.reactionVector r s) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro s _
            calc
              (h s / xstar s) *
                  (-(1 / 2 : ℝ) * ∑ r : N.R,
                    N.equilibriumReactionFlux κ xstar r *
                      N.reactionLogLinearForm xstar h r * N.reactionVector r s)
                  = -(1 / 2 : ℝ) * ((h s / xstar s) *
                      ∑ r : N.R, N.equilibriumReactionFlux κ xstar r *
                        N.reactionLogLinearForm xstar h r * N.reactionVector r s) := by ring
              _ = -(1 / 2 : ℝ) * ∑ r : N.R,
                    (h s / xstar s) *
                      (N.equilibriumReactionFlux κ xstar r *
                        N.reactionLogLinearForm xstar h r * N.reactionVector r s) := by
                    rw [Finset.mul_sum]
    _ = -(1 / 2 : ℝ) * ∑ r : N.R, ∑ s : S,
            (h s / xstar s) *
              (N.equilibriumReactionFlux κ xstar r *
                N.reactionLogLinearForm xstar h r * N.reactionVector r s) := by
            congr 1
            rw [Finset.sum_comm]
    _ = -(1 / 2 : ℝ) * ∑ r : N.R,
          N.equilibriumReactionFlux κ xstar r *
            (N.reactionLogLinearForm xstar h r)^2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro r _
            have hform :
                (∑ s : S, (h s / xstar s) * N.reactionVector r s) =
                  N.reactionLogLinearForm xstar h r := by
              unfold reactionLogLinearForm
              apply Finset.sum_congr rfl
              intro s _
              ring
            calc
              (∑ s : S, (h s / xstar s) *
                  (N.equilibriumReactionFlux κ xstar r *
                    N.reactionLogLinearForm xstar h r * N.reactionVector r s))
                  = N.equilibriumReactionFlux κ xstar r *
                      N.reactionLogLinearForm xstar h r *
                        (∑ s : S, (h s / xstar s) * N.reactionVector r s) := by
                      rw [Finset.mul_sum]
                      apply Finset.sum_congr rfl
                      intro s _
                      ring
              _ = N.equilibriumReactionFlux κ xstar r *
                    (N.reactionLogLinearForm xstar h r)^2 := by
                      rw [hform]
                      ring
/-- Weighted Jacobian form is nonpositive in every direction. -/
theorem detailedBalanceJacobianQuadratic_nonpos
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (h : Concentration S) :
    N.detailedBalanceJacobianQuadratic κ xstar h ≤ 0 := by
  rw [N.detailedBalanceJacobianQuadratic_eq_neg_sum_sq ρ κ hxs hdb h]
  have hsum : 0 ≤ ∑ r : N.R,
      N.equilibriumReactionFlux κ xstar r *
        (N.reactionLogLinearForm xstar h r)^2 := by
    -- `positivity` cannot establish that the equilibrium flux is nonnegative; it needs
    -- `massActionRate_pos` at the positive point `xstar`.
    refine Finset.sum_nonneg fun r _ => mul_nonneg ?_ (sq_nonneg _)
    exact (N.massActionRate_pos κ r hxs).le
  linarith

/-- Equality holds exactly when the inverse-scaled perturbation is orthogonal to the
stoichiometric subspace. -/
theorem detailedBalanceJacobianQuadratic_eq_zero_iff
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (h : Concentration S) :
    N.detailedBalanceJacobianQuadratic κ xstar h = 0 ↔
      invDiagonalApply xstar h ∈ orthSum N.stoichSubspace := by
  rw [N.detailedBalanceJacobianQuadratic_eq_neg_sum_sq ρ κ hxs hdb h]
  constructor
  · intro hz
    have hsum : (∑ r : N.R,
        N.equilibriumReactionFlux κ xstar r *
          (N.reactionLogLinearForm xstar h r)^2) = 0 := by
      linarith
    have hnonneg : ∀ r ∈ (Finset.univ : Finset N.R),
        0 ≤ N.equilibriumReactionFlux κ xstar r *
          (N.reactionLogLinearForm xstar h r)^2 := by
      intro r _
      exact mul_nonneg (N.massActionRate_pos κ r hxs).le (sq_nonneg _)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
    rw [Network.stoichSubspace]
    apply mem_orthSum_span
    intro g hg
    rcases hg with ⟨r, rfl⟩
    have hr := hterm r (Finset.mem_univ r)
    have hqpos : 0 < N.equilibriumReactionFlux κ xstar r :=
      N.massActionRate_pos κ r hxs
    have hform : N.reactionLogLinearForm xstar h r = 0 := by
      have hsq : (N.reactionLogLinearForm xstar h r)^2 = 0 := by
        exact (mul_eq_zero.mp hr).resolve_left hqpos.ne'
      exact sq_eq_zero_iff.mp hsq
    unfold reactionLogLinearForm at hform
    simp only [invDiagonalApply]
    simpa [mul_comm] using hform
  · intro horth
    have hform : ∀ r : N.R, N.reactionLogLinearForm xstar h r = 0 := by
      intro r
      have hr := (mem_orthSum.mp horth) (N.reactionVector r)
        (N.reactionVector_mem_stoichSubspace r)
      unfold reactionLogLinearForm
      simp only [invDiagonalApply] at hr
      simpa [mul_comm] using hr
    simp [hform]
/-- The Jacobian null quadratic directions are exactly the toric tangent directions
`diag(x*) Sᗮ`. -/
theorem detailedBalance_zeroQuadratic_iff_mem_tangent
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    (h : Concentration S) :
    N.detailedBalanceJacobianQuadratic κ xstar h = 0 ↔
      h ∈ N.complexBalancedTangentSpace xstar := by
  rw [N.detailedBalanceJacobianQuadratic_eq_zero_iff ρ κ hxs hdb h]
  constructor
  · intro horth
    refine ⟨invDiagonalApply xstar h, horth, ?_⟩
    funext s
    change xstar s * (h s / xstar s) = h s
    field_simp [(hxs s).ne']
  · rintro ⟨μ, hμ, hEq⟩
    have hmu : invDiagonalApply xstar h = μ := by
      funext s
      have hs := congrFun hEq s
      change xstar s * μ s = h s at hs
      change h s / xstar s = μ s
      rw [← hs]
      field_simp [(hxs s).ne']
    simpa [hmu] using hμ
/-- **Strict negativity on stoichiometric perturbations.** -/
theorem detailedBalanceJacobianQuadratic_strict_on_stoich
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ xstar)
    {h : Concentration S} (hS : h ∈ N.stoichSubspace) (h0 : h ≠ 0) :
    N.detailedBalanceJacobianQuadratic κ xstar h < 0 := by
  have hnonpos := N.detailedBalanceJacobianQuadratic_nonpos ρ κ hxs hdb h
  apply lt_of_le_of_ne hnonpos
  intro hz
  -- `intro hz` already gives `_ = 0`; the extra `.symm` flipped it the wrong way.
  have horth := (N.detailedBalanceJacobianQuadratic_eq_zero_iff ρ κ hxs hdb h).1 hz
  have hpair := (mem_orthSum.mp horth) h hS
  -- `invDiagonalApply xstar h s` is `h s / xstar s` by definition; make that syntactic so
  -- `linarith` can see `hpair` and `hsumpos` as statements about the same sum.
  simp only [invDiagonalApply] at hpair
  have hsumpos : 0 < ∑ s : S, (h s / xstar s) * h s := by
    -- every summand is `h_s² / x*_s ≥ 0`, and one is strictly positive since `h ≠ 0`
    obtain ⟨s0, hs0⟩ := Function.ne_iff.mp h0
    refine Finset.sum_pos' (fun s _ => ?_) ⟨s0, Finset.mem_univ s0, ?_⟩
    · rw [div_mul_eq_mul_div]
      exact div_nonneg (mul_self_nonneg _) (hxs s).le
    · rw [div_mul_eq_mul_div]
      exact div_pos (mul_self_pos.mpr hs0) (hxs s0)
  linarith

/-- No nonzero stoichiometric perturbation lies in the Jacobian kernel at a detailed-
balanced equilibrium. -/
theorem detailedBalance_Jacobian_injective_on_stoich
    (N : Network S) (ρ : ReversiblePairing N) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hdb : N.IsReactionwiseDetailedBalanced ρ κ xstar) :
    ∀ h ∈ N.stoichSubspace,
      (N.massActionJacobian κ xstar).mulVec h = 0 → h = 0 := by
  intro h hS hJ
  by_contra h0
  have hneg := N.detailedBalanceJacobianQuadratic_strict_on_stoich
    ρ κ hxs hdb hS h0
  simp [detailedBalanceJacobianQuadratic, hJ, speciesDot] at hneg

end Network
end CRNT
