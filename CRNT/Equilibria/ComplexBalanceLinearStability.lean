import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Equilibria.ComplexBalanceGeometry
import CRNT.Equilibria.DetailedBalanceLinearStability
import CRNT.Kinetics.MassActionJacobian
import CRNT.Dynamics.ExponentialDecay
import CRNT.Deficiency.SteadyStateKernel
import CRNT.Theorems.DeficiencyZero.AsymptoticStability

/-!
# Linear stability of positive complex-balanced equilibria

The Horn--Jackson entropy gives more than nonlinear Lyapunov descent.  Its Hessian at a
positive reference equilibrium is the positive diagonal metric `diag(1/x*)`.  The second
variation of entropy dissipation therefore gives a strict quadratic Lyapunov inequality for
the Jacobian restricted to the stoichiometric tangent space.

This proves that the reduced Jacobian is Hurwitz and yields local exponential stability on
the stoichiometric compatibility class.  Neutral directions in the full species space are
exactly the tangent directions to the complex-balanced equilibrium manifold.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Hessian metric of the Horn--Jackson relative entropy at `x*`. -/
noncomputable def entropyHessianQuadratic (xstar h : Concentration S) : ℝ :=
  ∑ s : S, h s ^ 2 / xstar s

/-- Positive definiteness of the entropy Hessian at a positive state. -/
theorem entropyHessianQuadratic_pos
    {xstar h : Concentration S} (hxs : xstar.Positive) (h0 : h ≠ 0) :
    0 < entropyHessianQuadratic xstar h := by
  unfold entropyHessianQuadratic
  obtain ⟨s, hs⟩ : ∃ s, h s ≠ 0 := by
    by_contra hz
    push_neg at hz
    exact h0 (funext hz)
  apply Finset.sum_pos'
  · intro i _
    exact div_nonneg (sq_nonneg _) (hxs i).le
  · refine ⟨s, Finset.mem_univ s, ?_⟩
    exact div_pos (sq_pos_of_ne_zero hs) (hxs s)

/-- Bilinear entropy-Hessian pairing. -/
noncomputable def entropyHessianPairing (xstar u v : Concentration S) : ℝ :=
  ∑ s : S, (u s / xstar s) * v s

/-- Quadratic form of the mass-action Jacobian in the entropy Hessian metric. -/
noncomputable def complexBalanceJacobianQuadratic
    (N : Network S) (κ : N.RateConstants)
    (xstar h : Concentration S) : ℝ :=
  entropyHessianPairing xstar h
    ((N.massActionJacobian κ xstar).mulVec h)

/-- **Sum-of-squares identity for a complex-balanced Jacobian.**  Complex balance
makes the equilibrium one-way reaction flux a circulation on the complex graph; this is
exactly what is needed to symmetrize the entropy-metric quadratic form. -/
theorem complexBalanceJacobianQuadratic_eq_neg_sum_sq
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (h : Concentration S) :
    N.complexBalanceJacobianQuadratic κ xstar h =
      -(1 / 2 : ℝ) * ∑ r : N.R,
        N.equilibriumReactionFlux κ xstar r *
          (N.reactionLogLinearForm xstar h r)^2 := by
  let q : N.R → ℝ := fun r => N.equilibriumReactionFlux κ xstar r
  let a : N.ComplexIdx → ℝ := fun c => ∑ s : S, (c.val s : ℝ) * (h s / xstar s)
  have hinc : N.incidenceMap q = 0 := by
    have hk := (N.isComplexBalanced_iff_kineticMap κ xstar).1 hcb
    have heq := N.kineticMap_eq_incidenceMap κ (N.complexMonomialVector xstar)
    rw [hk] at heq
    simpa [q, equilibriumReactionFlux, massActionRate_eq, complexMonomialVector_apply] using heq.symm
  have hbalance (b : N.ComplexIdx → ℝ) :
      (∑ r : N.R, q r * b (N.targetIdx r)) =
        ∑ r : N.R, q r * b (N.sourceIdx r) := by
    have hz := congrArg (fun z : N.ComplexIdx → ℝ => ∑ c : N.ComplexIdx, z c * b c) hinc
    simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hz
    simp only [incidenceMap_apply, Finset.sum_mul] at hz
    rw [Finset.sum_comm] at hz
    have hinner : ∀ r : N.R,
        (∑ c : N.ComplexIdx,
          (q r * ((if N.targetIdx r = c then (1 : ℝ) else 0) -
            (if N.sourceIdx r = c then 1 else 0))) * b c) =
          q r * b (N.targetIdx r) - q r * b (N.sourceIdx r) := by
      intro r
      calc
        (∑ c : N.ComplexIdx,
          (q r * ((if N.targetIdx r = c then (1 : ℝ) else 0) -
            (if N.sourceIdx r = c then 1 else 0))) * b c) =
          (∑ c : N.ComplexIdx, (q r * (if N.targetIdx r = c then (1 : ℝ) else 0)) * b c) -
          (∑ c : N.ComplexIdx, (q r * (if N.sourceIdx r = c then 1 else 0)) * b c) := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro c _
            ring
        _ = q r * b (N.targetIdx r) - q r * b (N.sourceIdx r) := by simp
    simp only [hinner, Finset.sum_sub_distrib] at hz
    linarith
  have hsq := hbalance (fun c => (a c)^2)
  unfold complexBalanceJacobianQuadratic
  rw [N.massActionJacobian_mulVec_logform κ hxs h]
  unfold entropyHessianPairing
  let src : N.R → ℝ := fun r => a (N.sourceIdx r)
  let tgt : N.R → ℝ := fun r => a (N.targetIdx r)
  have hsrc : ∀ r : N.R,
      (∑ j : S, ((N.reaction r).source j : ℝ) * (h j / xstar j)) = src r := by
    intro r; rfl
  have hform : ∀ r : N.R, N.reactionLogLinearForm xstar h r = tgt r - src r := by
    intro r
    unfold reactionLogLinearForm
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      simp [tgt, src, a, targetIdx, sourceIdx, reactionVector_apply]
      ring
  have hq : ∀ r : N.R, N.massActionRate κ r xstar = q r := fun r => rfl
  simp only [hq, hsrc]
  calc
    (∑ s : S, (h s / xstar s) *
      (∑ r : N.R, q r * src r * N.reactionVector r s)) =
      ∑ r : N.R, q r * src r * (tgt r - src r) := by
        calc
          _ = ∑ s : S, ∑ r : N.R,
              (h s / xstar s) * (q r * src r * N.reactionVector r s) := by
                apply Finset.sum_congr rfl
                intro s _
                rw [Finset.mul_sum]
          _ = ∑ r : N.R, ∑ s : S,
              (h s / xstar s) * (q r * src r * N.reactionVector r s) := by
                exact Finset.sum_comm
          _ = ∑ r : N.R, q r * src r * (tgt r - src r) := by
                apply Finset.sum_congr rfl
                intro r _
                calc
                  (∑ s : S, (h s / xstar s) *
                    (q r * src r * N.reactionVector r s)) =
                      q r * src r *
                        (∑ s : S, (h s / xstar s) * N.reactionVector r s) := by
                          calc
                            _ = ∑ s : S, (q r * src r) *
                                ((h s / xstar s) * N.reactionVector r s) := by
                                  apply Finset.sum_congr rfl
                                  intro s _
                                  ring
                            _ = q r * src r *
                                (∑ s : S, (h s / xstar s) * N.reactionVector r s) := by
                                  symm
                                  exact Finset.mul_sum _ _ _
                  _ = q r * src r * N.reactionLogLinearForm xstar h r := by
                        congr 1
                        unfold reactionLogLinearForm
                        apply Finset.sum_congr rfl
                        intro s _
                        ring
                  _ = q r * src r * (tgt r - src r) := by rw [hform r]
    _ = -(1/2 : ℝ) * ∑ r : N.R, q r * (tgt r - src r)^2 := by
      have hsq' : (∑ r : N.R, q r * (tgt r)^2) = ∑ r : N.R, q r * (src r)^2 := by
        simpa [tgt, src] using hsq
      have hz : ∑ r : N.R, (q r * (tgt r)^2 - q r * (src r)^2) = 0 := by
        rw [Finset.sum_sub_distrib, hsq', sub_self]
      rw [Finset.mul_sum]
      have hid :
          (∑ r : N.R, q r * src r * (tgt r - src r)) -
            (∑ r : N.R, (-(1 / 2 : ℝ)) * (q r * (tgt r - src r) ^ 2)) =
              (1 / 2 : ℝ) *
                ∑ r : N.R, (q r * (tgt r)^2 - q r * (src r)^2) := by
        calc
          _ = ∑ r : N.R,
              (q r * src r * (tgt r - src r) -
                (-(1 / 2 : ℝ)) * (q r * (tgt r - src r) ^ 2)) := by
                  rw [Finset.sum_sub_distrib]
          _ = ∑ r : N.R,
              (1 / 2 : ℝ) * (q r * (tgt r)^2 - q r * (src r)^2) := by
                  apply Finset.sum_congr rfl
                  intro r _
                  ring
          _ = (1 / 2 : ℝ) *
              ∑ r : N.R, (q r * (tgt r)^2 - q r * (src r)^2) := by
                  symm
                  exact Finset.mul_sum _ _ _
      rw [hz, mul_zero] at hid
      linarith
    _ = -(1/2 : ℝ) * ∑ r : N.R,
        N.equilibriumReactionFlux κ xstar r * (N.reactionLogLinearForm xstar h r)^2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro r _
      rw [hform r]

/-- The complex-balance Jacobian quadratic form is exactly the entropy-Hessian
pairing of a perturbation with the Fréchet derivative of the mass-action vector field.

This is the correct differential identity behind linear stability.  In particular, it is
*not* the first derivative at `t = 0` of the product of the entropy gradient displacement
with the vector field: at an equilibrium both factors vanish there, so that first
derivative is zero. -/
theorem complexBalanceJacobianQuadratic_eq_fderiv_pairing
    (N : Network S) (κ : N.RateConstants)
    (xstar h : Concentration S) :
    N.complexBalanceJacobianQuadratic κ xstar h =
      entropyHessianPairing xstar h
        ((fderiv ℝ (fun x => N.massActionVectorField κ x) xstar) h) := by
  rw [(N.massActionVectorField_hasFDerivAt κ xstar).fderiv,
    N.massActionJacobianCLM_apply]
  rfl

/-- Complex balance makes the entropy-metric Jacobian quadratic form nonpositive. -/
theorem complexBalanceJacobianQuadratic_nonpos
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (h : Concentration S) :
    N.complexBalanceJacobianQuadratic κ xstar h ≤ 0 := by
  rw [N.complexBalanceJacobianQuadratic_eq_neg_sum_sq κ hxs hcb h]
  have hsum : 0 ≤ ∑ r : N.R,
      N.equilibriumReactionFlux κ xstar r *
        (N.reactionLogLinearForm xstar h r)^2 := by
    refine Finset.sum_nonneg fun r _ => mul_nonneg ?_ (sq_nonneg _)
    exact (N.massActionRate_pos κ r hxs).le
  linarith

/-- Equality directions of the complex-balanced Jacobian form are exactly tangent to the
complex-balanced equilibrium manifold. -/
theorem complexBalanceJacobianQuadratic_eq_zero_iff_tangent
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    (h : Concentration S) :
    N.complexBalanceJacobianQuadratic κ xstar h = 0 ↔
      h ∈ N.complexBalancedTangentSpace xstar := by
  rw [N.complexBalanceJacobianQuadratic_eq_neg_sum_sq κ hxs hcb h]
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
    have horth : invDiagonalApply xstar h ∈ orthSum N.stoichSubspace := by
      rw [Network.stoichSubspace]
      apply mem_orthSum_span
      intro g hg
      rcases hg with ⟨r, rfl⟩
      have hr := hterm r (Finset.mem_univ r)
      have hqpos : 0 < N.equilibriumReactionFlux κ xstar r :=
        N.massActionRate_pos κ r hxs
      have hform : N.reactionLogLinearForm xstar h r = 0 := by
        have hsq : (N.reactionLogLinearForm xstar h r)^2 = 0 :=
          (mul_eq_zero.mp hr).resolve_left hqpos.ne'
        exact sq_eq_zero_iff.mp hsq
      unfold reactionLogLinearForm at hform
      simp only [invDiagonalApply]
      simpa [mul_comm] using hform
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
    have hform : ∀ r : N.R, N.reactionLogLinearForm xstar h r = 0 := by
      intro r
      have hr := (mem_orthSum.mp hμ) (N.reactionVector r)
        (N.reactionVector_mem_stoichSubspace r)
      unfold reactionLogLinearForm
      rw [← hmu] at hr
      simpa [invDiagonalApply, mul_comm] using hr
    simp [hform]

/-- The equilibrium-manifold tangent and stoichiometric tangent meet only at zero. -/
theorem complexBalancedTangent_inf_stoich_eq_bot
    (N : Network S) {xstar : Concentration S} (hxs : xstar.Positive) :
    N.complexBalancedTangentSpace xstar ⊓ N.stoichSubspace = ⊥ := by
  -- If `h = diag(x*) μ` with `μ ⟂ S` and `h ∈ S`, test the orthogonality of `μ` against
  -- `h` itself: `0 = ⟨μ, h⟩ = Σ x*_s μ_s²`, a sum of nonnegative terms, so `μ = 0`.
  rw [Submodule.eq_bot_iff (N.complexBalancedTangentSpace xstar ⊓ N.stoichSubspace)]
  intro h hh
  obtain ⟨htan, hS⟩ := hh
  obtain ⟨μ, hμ, hmap⟩ := htan
  have hval : ∀ s, h s = xstar s * μ s := by
    intro s; rw [← hmap]; rfl
  have horth : ∑ i : S, μ i * h i = 0 := hμ h hS
  have hterms : ∀ i : S, μ i * h i = xstar i * μ i ^ 2 := by
    intro i; rw [hval i]; ring
  have hsum : ∑ i : S, xstar i * μ i ^ 2 = 0 := by
    rw [← horth]; exact (Finset.sum_congr rfl fun i _ => (hterms i).symm)
  have hzero : ∀ i : S, μ i = 0 := by
    intro i
    have hnn : ∀ j ∈ Finset.univ, 0 ≤ xstar j * μ j ^ 2 := fun j _ =>
      mul_nonneg (hxs j).le (sq_nonneg _)
    have hi := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum i (Finset.mem_univ i)
    rcases mul_eq_zero.1 hi with h1 | h2
    · exact absurd h1 (hxs i).ne'
    · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h2
  funext s
  rw [hval s, hzero s, mul_zero]
  rfl

/-- Strict entropy-metric dissipation on nonzero stoichiometric perturbations. -/
theorem complexBalanceJacobianQuadratic_strict_on_stoich
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar)
    {h : Concentration S} (hS : h ∈ N.stoichSubspace) (h0 : h ≠ 0) :
    N.complexBalanceJacobianQuadratic κ xstar h < 0 := by
  have hle := N.complexBalanceJacobianQuadratic_nonpos κ hxs hcb h
  apply lt_of_le_of_ne hle
  intro heq
  have ht := (N.complexBalanceJacobianQuadratic_eq_zero_iff_tangent
    κ hwr hxs hcb h).1 heq
  have : h ∈ N.complexBalancedTangentSpace xstar ⊓ N.stoichSubspace := ⟨ht, hS⟩
  rw [N.complexBalancedTangent_inf_stoich_eq_bot hxs] at this
  exact h0 this

/-- The Jacobian has no nonzero kernel vector tangent to a stoichiometric class. -/
theorem complexBalanceJacobian_injective_on_stoich
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    ∀ h ∈ N.stoichSubspace,
      (N.massActionJacobian κ xstar).mulVec h = 0 → h = 0 := by
  intro h hS hJ
  by_contra h0
  have hneg := N.complexBalanceJacobianQuadratic_strict_on_stoich
    κ hwr hxs hcb hS h0
  simp [complexBalanceJacobianQuadratic, entropyHessianPairing, hJ] at hneg

/-- A strict quadratic Lyapunov metric for the linearized dynamics restricted to the
stoichiometric tangent space.  This is the coordinate-free finite-dimensional statement one
needs before invoking the standard Lyapunov/Hurwitz theorem. -/
def HasStrictStoichQuadraticLyapunov (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Prop :=
  ∃ Q : N.stoichSubspace → ℝ,
    (∀ h, h ≠ 0 → 0 < Q h) ∧
    ∃ D : N.stoichSubspace → ℝ,
      (∀ h, h ≠ 0 → D h < 0) ∧
      ∀ h : N.stoichSubspace,
        D h = entropyHessianPairing x h.1
          ((N.massActionJacobian κ x).mulVec h.1)

/-- The Horn--Jackson entropy Hessian supplies a strict quadratic Lyapunov metric for the
complex-balanced Jacobian on the stoichiometric tangent space. -/
theorem complexBalanced_hasStrictStoichQuadraticLyapunov
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.HasStrictStoichQuadraticLyapunov κ xstar := by
  -- `Q(h) = Σ h_s²/x*_s` is the entropy Hessian; strictness of the dissipation is exactly
  -- `complexBalanceJacobianQuadratic_strict_on_stoich`.
  refine ⟨fun h => entropyHessianQuadratic xstar h.1, ?_, ?_⟩
  · intro h h0
    refine entropyHessianQuadratic_pos hxs ?_
    intro hzero
    exact h0 (Subtype.ext hzero)
  · refine ⟨fun h => entropyHessianPairing xstar h.1
      ((N.massActionJacobian κ xstar).mulVec h.1), ?_, fun _ => rfl⟩
    intro h h0
    have hne : h.1 ≠ 0 := fun hz => h0 (Subtype.ext hz)
    exact N.complexBalanceJacobianQuadratic_strict_on_stoich κ hwr hxs hcb h.2 hne

/-- A complex vector belongs to the complexification of the real stoichiometric subspace
when both its real and imaginary parts are stoichiometric vectors. -/
def IsComplexifiedStoichVector (N : Network S) (h : S → ℂ) : Prop :=
  (fun s => (h s).re) ∈ N.stoichSubspace ∧
  (fun s => (h s).im) ∈ N.stoichSubspace

/-- Complexification of the real mass-action Jacobian action. -/
noncomputable def complexifiedJacobianMulVec
    (N : Network S) (κ : N.RateConstants) (x : Concentration S)
    (h : S → ℂ) : S → ℂ :=
  fun i => ∑ j : S, (N.massActionJacobian κ x i j : ℂ) * h j

/-- Spectral Hurwitz property of the Jacobian restricted to the **complexified**
stoichiometric subspace.

The complexification is essential: testing only real eigenvectors misses conjugate non-real
eigenpairs and can make the predicate vacuous (for example for a planar rotation). -/
def IsHurwitzOnStoich (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Prop :=
  ∀ (μ : ℂ) (h : S → ℂ),
    h ≠ 0 →
    N.IsComplexifiedStoichVector h →
    N.complexifiedJacobianMulVec κ x h = μ • h →
    μ.re < 0

/-- Strict real quadratic Lyapunov decay implies that every eigenvalue of the complexified
reduced Jacobian has negative real part.

For a complex eigenvector `h = a + i b`, take real and imaginary parts of `Jh = μh`.
Pair the first equation with `a` and the second with `b` in the entropy-Hessian metric.
The cross terms cancel by symmetry, leaving
`D(a)+D(b) = re(μ) (Q(a)+Q(b))`; the left side is strictly negative and the right
quadratic factor is positive because `h ≠ 0`. -/
theorem strictStoichQuadraticLyapunov_implies_hurwitz
    (N : Network S) (κ : N.RateConstants) {x : Concentration S}
    (hx : x.Positive)
    (hQ : N.HasStrictStoichQuadraticLyapunov κ x) :
    N.IsHurwitzOnStoich κ x := by
  rcases hQ with ⟨Q, hQpos, D, hDneg, hD⟩
  intro μ h hh0 hhS heig
  let a : Concentration S := fun s => (h s).re
  let b : Concentration S := fun s => (h s).im
  have haS : a ∈ N.stoichSubspace := hhS.1
  have hbS : b ∈ N.stoichSubspace := hhS.2
  let av : N.stoichSubspace := ⟨a, haS⟩
  let bv : N.stoichSubspace := ⟨b, hbS⟩
  have hab0 : a ≠ 0 ∨ b ≠ 0 := by
    by_contra hz
    push_neg at hz
    rcases hz with ⟨ha0, hb0⟩
    apply hh0
    funext s
    apply Complex.ext
    · simpa [a] using congrFun ha0 s
    · simpa [b] using congrFun hb0 s
  have hDa : D av ≤ 0 := by
    by_cases ha0 : a = 0
    · have hav0 : av = 0 := by apply Subtype.ext; exact ha0
      rw [hav0, hD]
      simp [entropyHessianPairing]
    · exact (hDneg av (by intro hav0; exact ha0 (congrArg Subtype.val hav0))).le
  have hDb : D bv ≤ 0 := by
    by_cases hb0 : b = 0
    · have hbv0 : bv = 0 := by apply Subtype.ext; exact hb0
      rw [hbv0, hD]
      simp [entropyHessianPairing]
    · exact (hDneg bv (by intro hbv0; exact hb0 (congrArg Subtype.val hbv0))).le
  have hDsum : D av + D bv < 0 := by
    rcases hab0 with ha0 | hb0
    · have hlt := hDneg av (by intro hav0; exact ha0 (congrArg Subtype.val hav0))
      linarith
    · have hlt := hDneg bv (by intro hbv0; exact hb0 (congrArg Subtype.val hbv0))
      linarith
  have hre (i : S) :
      (N.massActionJacobian κ x).mulVec a i = μ.re * a i - μ.im * b i := by
    have hi := congrFun heig i
    have hire := congrArg Complex.re hi
    simp only [complexifiedJacobianMulVec, Pi.smul_apply, smul_eq_mul] at hire
    have hsum :
        (∑ j : S, ((N.massActionJacobian κ x i j : ℂ) * h j)).re =
          ∑ j : S, (((N.massActionJacobian κ x i j : ℂ) * h j).re) := by
      simpa using
        (map_sum Complex.reCLM
          (fun j : S => (N.massActionJacobian κ x i j : ℂ) * h j)
          (Finset.univ : Finset S))
    rw [hsum] at hire
    simpa [a, b, Matrix.mulVec, dotProduct, Complex.mul_re] using hire
  have him (i : S) :
      (N.massActionJacobian κ x).mulVec b i = μ.im * a i + μ.re * b i := by
    have hi := congrFun heig i
    have hiim := congrArg Complex.im hi
    simp only [complexifiedJacobianMulVec, Pi.smul_apply, smul_eq_mul] at hiim
    have hsum :
        (∑ j : S, ((N.massActionJacobian κ x i j : ℂ) * h j)).im =
          ∑ j : S, (((N.massActionJacobian κ x i j : ℂ) * h j).im) := by
      simpa using
        (map_sum Complex.imCLM
          (fun j : S => (N.massActionJacobian κ x i j : ℂ) * h j)
          (Finset.univ : Finset S))
    rw [hsum] at hiim
    simpa [a, b, Matrix.mulVec, dotProduct, Complex.mul_im, add_comm] using hiim
  have hmetric_a :
      entropyHessianPairing x a a = entropyHessianQuadratic x a := by
    unfold entropyHessianPairing entropyHessianQuadratic
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hmetric_b :
      entropyHessianPairing x b b = entropyHessianQuadratic x b := by
    unfold entropyHessianPairing entropyHessianQuadratic
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hmetric_pos :
      0 < entropyHessianQuadratic x a + entropyHessianQuadratic x b := by
    rcases hab0 with ha0 | hb0
    · have hpa := entropyHessianQuadratic_pos hx ha0
      have hpb : 0 ≤ entropyHessianQuadratic x b := by
        unfold entropyHessianQuadratic
        exact Finset.sum_nonneg fun s _ => div_nonneg (sq_nonneg _) (hx s).le
      linarith
    · have hpb := entropyHessianQuadratic_pos hx hb0
      have hpa : 0 ≤ entropyHessianQuadratic x a := by
        unfold entropyHessianQuadratic
        exact Finset.sum_nonneg fun s _ => div_nonneg (sq_nonneg _) (hx s).le
      linarith
  have hidentity :
      D av + D bv = μ.re *
        (entropyHessianQuadratic x a + entropyHessianQuadratic x b) := by
    rw [hD av, hD bv]
    unfold entropyHessianPairing entropyHessianQuadratic
    simp only [av, bv]
    simp_rw [hre, him]
    rw [← Finset.sum_add_distrib]
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [hidentity] at hDsum
  rcases (mul_neg_iff.mp hDsum) with hbad | hgood
  · exact False.elim ((not_lt_of_ge hmetric_pos.le) hbad.2)
  · exact hgood.1

/-- Positive complex-balanced equilibria have Hurwitz linearization relative to their
stoichiometric compatibility classes. -/
theorem complexBalanced_isHurwitzOnStoich
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.IsHurwitzOnStoich κ xstar := by
  exact N.strictStoichQuadraticLyapunov_implies_hurwitz κ hxs
    (N.complexBalanced_hasStrictStoichQuadraticLyapunov κ hwr hxs hcb)

/-- Standard local exponential stability inside a positive stoichiometric compatibility
class, stated directly in terms of mass-action trajectories. -/
def LocallyExponentiallyStableInClass (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) : Prop :=
  ∃ ε C α : ℝ,
    0 < ε ∧ 0 < C ∧ 0 < α ∧
    ∀ (x₀ : Concentration S) (γ : ℝ → Concentration S),
      x₀.Positive → N.StoichCompatible xstar x₀ →
      ‖x₀ - xstar‖ < ε →
      γ 0 = x₀ →
      (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
      ∀ t, 0 ≤ t →
        ‖γ t - xstar‖ ≤ C * Real.exp (-α * t) * ‖x₀ - xstar‖

/-! ## Quantitative machinery for nonlinear local exponential stability

Strict negativity of the entropy-metric dissipation at each nonzero tangent vector is
weaker than a decay *rate*.  This section upgrades it by compactness, records the
first-order remainder bound supplied by Frechet differentiability of the mass-action field,
and assembles a Gronwall argument with an explicit trapping region.
-/

section QuadraticStability

open Metric Asymptotics

/-! ## Comparing the entropy Hessian with the squared norm -/

theorem entropyHessianQuadratic_nonneg {x : Concentration S} (hx : x.Positive)
    (h : Concentration S) : 0 ≤ entropyHessianQuadratic x h := by
  rw [entropyHessianQuadratic]
  exact Finset.sum_nonneg fun s _ => div_nonneg (sq_nonneg _) (hx s).le

theorem entropyHessianQuadratic_zero (x : Concentration S) :
    entropyHessianQuadratic x (0 : Concentration S) = 0 := by
  rw [entropyHessianQuadratic]
  apply Finset.sum_eq_zero
  intro s _
  simp

theorem entropyHessianQuadratic_smul (x : Concentration S) (c : ℝ)
    (h : Concentration S) :
    entropyHessianQuadratic x (c • h) = c ^ 2 * entropyHessianQuadratic x h := by
  rw [entropyHessianQuadratic, entropyHessianQuadratic, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The entropy Hessian is bounded above by a multiple of the squared sup norm. -/
theorem entropyHessianQuadratic_le {x : Concentration S} (hx : x.Positive)
    (h : Concentration S) :
    entropyHessianQuadratic x h ≤ (∑ s : S, 1 / x s) * ‖h‖ ^ 2 := by
  rw [entropyHessianQuadratic, Finset.sum_mul]
  refine Finset.sum_le_sum fun s _ => ?_
  have hns : |h s| ≤ ‖h‖ := by
    simpa [Real.norm_eq_abs] using norm_le_pi_norm h s
  have hb : h s ^ 2 ≤ ‖h‖ ^ 2 := by
    nlinarith [abs_nonneg (h s), sq_abs (h s), norm_nonneg h]
  have hrw : h s ^ 2 / x s = (1 / x s) * h s ^ 2 := by ring
  rw [hrw]
  exact mul_le_mul_of_nonneg_left hb (div_nonneg zero_le_one (hx s).le)

/-- The squared sup norm is bounded above by a multiple of the entropy Hessian. -/
theorem norm_sq_le_entropyHessianQuadratic {x : Concentration S} (hx : x.Positive)
    (h : Concentration S) :
    ‖h‖ ^ 2 ≤ ((∑ s : S, x s) + 1) * entropyHessianQuadratic x h := by
  set B : ℝ := (∑ s : S, x s) + 1 with hBdef
  have hBpos : 0 < B := by
    have : 0 ≤ ∑ s : S, x s := Finset.sum_nonneg fun s _ => (hx s).le
    rw [hBdef]; linarith
  have hxB : ∀ s : S, x s ≤ B := by
    intro s
    have hle : x s ≤ ∑ s' : S, x s' :=
      Finset.single_le_sum (f := fun s' => x s') (fun i _ => (hx i).le) (Finset.mem_univ s)
    rw [hBdef]; linarith
  have hQnn : 0 ≤ entropyHessianQuadratic x h := entropyHessianQuadratic_nonneg hx h
  have key : ∀ s : S, h s ^ 2 ≤ B * entropyHessianQuadratic x h := by
    intro s
    have h1 : h s ^ 2 / x s ≤ entropyHessianQuadratic x h := by
      rw [entropyHessianQuadratic]
      exact Finset.single_le_sum (f := fun s' => h s' ^ 2 / x s')
        (fun i _ => div_nonneg (sq_nonneg _) (hx i).le) (Finset.mem_univ s)
    have h2 : h s ^ 2 ≤ entropyHessianQuadratic x h * x s := by
      have hmul := mul_le_mul_of_nonneg_right h1 (hx s).le
      rwa [div_mul_cancel₀ _ (ne_of_gt (hx s))] at hmul
    nlinarith [hxB s, hQnn]
  have hnorm : ‖h‖ ≤ Real.sqrt (B * entropyHessianQuadratic x h) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro s
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (key s)
  have hsq := Real.sq_sqrt (mul_nonneg hBpos.le hQnn)
  nlinarith [hnorm, norm_nonneg h, Real.sqrt_nonneg (B * entropyHessianQuadratic x h)]

/-! ## A uniform decay rate -/

/-- The entropy-metric dissipation quadratic form on the stoichiometric tangent space. -/
noncomputable def stoichDissipation (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (h : N.stoichSubspace) : ℝ :=
  entropyHessianPairing x h.1 ((N.massActionJacobian κ x).mulVec h.1)

theorem stoichDissipation_zero (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.stoichDissipation κ x 0 = 0 := by
  rw [stoichDissipation, entropyHessianPairing]
  apply Finset.sum_eq_zero
  intro s _
  simp

theorem stoichDissipation_smul (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (c : ℝ) (h : N.stoichSubspace) :
    N.stoichDissipation κ x (c • h) = c ^ 2 * N.stoichDissipation κ x h := by
  have hval : ((c • h : N.stoichSubspace) : Concentration S) = c • (h : Concentration S) := rfl
  rw [stoichDissipation, stoichDissipation, hval, Matrix.mulVec_smul,
    entropyHessianPairing, entropyHessianPairing, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem continuous_stoichDissipation (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : Continuous (N.stoichDissipation κ x) := by
  have hcoord : ∀ s : S, Continuous fun h : N.stoichSubspace => (h : Concentration S) s :=
    fun s => (continuous_apply s).comp continuous_subtype_val
  unfold stoichDissipation entropyHessianPairing
  refine continuous_finset_sum _ fun s _ => ?_
  refine Continuous.mul ((hcoord s).div_const (x s)) ?_
  have : (fun h : N.stoichSubspace =>
      ((N.massActionJacobian κ x).mulVec (h : Concentration S)) s)
      = fun h : N.stoichSubspace =>
        ∑ j : S, N.massActionJacobian κ x s j * (h : Concentration S) j := by
    funext h
    simp only [Matrix.mulVec, dotProduct]
  rw [this]
  exact continuous_finset_sum _ fun j _ => continuous_const.mul (hcoord j)

/-- **Uniform decay rate.**  Pointwise strict negativity of the entropy-metric dissipation on
the stoichiometric subspace upgrades, by compactness of the unit sphere, to a uniform rate
against the entropy Hessian. -/
theorem exists_stoich_decay_rate (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Positive)
    (hneg : ∀ h : N.stoichSubspace, h ≠ 0 → N.stoichDissipation κ x h < 0) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ h : N.stoichSubspace,
      N.stoichDissipation κ x h ≤ -lam * entropyHessianQuadratic x h.1 := by
  by_cases htriv : ∀ h : N.stoichSubspace, h = 0
  · refine ⟨1, one_pos, fun h => ?_⟩
    rw [htriv h, N.stoichDissipation_zero κ x]
    have : ((0 : N.stoichSubspace) : Concentration S) = 0 := rfl
    rw [this, entropyHessianQuadratic_zero]
    simp
  · push_neg at htriv
    obtain ⟨h₀, hh₀⟩ := htriv
    have hn₀ : 0 < ‖h₀‖ := norm_pos_iff.mpr hh₀
    set K : Set N.stoichSubspace := sphere (0 : N.stoichSubspace) 1 with hKdef
    have hKcpt : IsCompact K := isCompact_sphere _ _
    have hKne : K.Nonempty := by
      refine ⟨(‖h₀‖)⁻¹ • h₀, ?_⟩
      rw [hKdef, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
        abs_of_pos hn₀]
      exact inv_mul_cancel₀ (ne_of_gt hn₀)
    have hQcont : Continuous fun h : N.stoichSubspace =>
        entropyHessianQuadratic x (h : Concentration S) := by
      have hcoord : ∀ s : S, Continuous fun h : N.stoichSubspace => (h : Concentration S) s :=
        fun s => (continuous_apply s).comp continuous_subtype_val
      unfold entropyHessianQuadratic
      exact continuous_finset_sum _ fun s _ =>
        ((hcoord s).pow 2).div_const (x s)
    obtain ⟨a, haK, hamax⟩ :=
      hKcpt.exists_isMaxOn hKne (N.continuous_stoichDissipation κ x).continuousOn
    obtain ⟨b, hbK, hbmax⟩ := hKcpt.exists_isMaxOn hKne hQcont.continuousOn
    have hane : a ≠ 0 := by
      intro h0
      rw [hKdef, mem_sphere_iff_norm, sub_zero, h0, norm_zero] at haK
      exact absurd haK (by norm_num)
    have hbne : (b : Concentration S) ≠ 0 := by
      intro h0
      rw [hKdef, mem_sphere_iff_norm, sub_zero] at hbK
      have : b = 0 := Submodule.coe_eq_zero.mp h0
      rw [this, norm_zero] at hbK
      exact absurd hbK (by norm_num)
    have hDa : N.stoichDissipation κ x a < 0 := hneg a hane
    have hQb : 0 < entropyHessianQuadratic x (b : Concentration S) :=
      entropyHessianQuadratic_pos hx hbne
    refine ⟨-N.stoichDissipation κ x a / entropyHessianQuadratic x (b : Concentration S),
      div_pos (by linarith) hQb, fun h => ?_⟩
    set lam := -N.stoichDissipation κ x a / entropyHessianQuadratic x (b : Concentration S)
      with hlamdef
    have hlampos : 0 < lam := div_pos (by linarith) hQb
    have hDaeq : N.stoichDissipation κ x a
        = -lam * entropyHessianQuadratic x (b : Concentration S) := by
      rw [hlamdef]
      field_simp
    by_cases hh0 : h = 0
    · rw [hh0, N.stoichDissipation_zero κ x]
      have hz : ((0 : N.stoichSubspace) : Concentration S) = 0 := rfl
      rw [hz, entropyHessianQuadratic_zero]
      simp
    · have hnh : 0 < ‖h‖ := norm_pos_iff.mpr hh0
      obtain ⟨c, hcpos, u, huK, hhu⟩ :
          ∃ c : ℝ, 0 < c ∧ ∃ u : N.stoichSubspace, u ∈ K ∧ h = c • u := by
        refine ⟨‖h‖, hnh, (‖h‖)⁻¹ • h, ?_, ?_⟩
        · rw [hKdef, mem_sphere_iff_norm, sub_zero, norm_smul, norm_inv, Real.norm_eq_abs,
            abs_of_pos hnh]
          exact inv_mul_cancel₀ (ne_of_gt hnh)
        · rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hnh), one_smul]
      have hDu : N.stoichDissipation κ x u ≤ N.stoichDissipation κ x a :=
        (isMaxOn_iff.mp hamax) u huK
      have hQu : entropyHessianQuadratic x (u : Concentration S)
          ≤ entropyHessianQuadratic x (b : Concentration S) :=
        (isMaxOn_iff.mp hbmax) u huK
      have hDh : N.stoichDissipation κ x h = c ^ 2 * N.stoichDissipation κ x u := by
        rw [hhu, N.stoichDissipation_smul κ x]
      have hQh : entropyHessianQuadratic x (h : Concentration S)
          = c ^ 2 * entropyHessianQuadratic x (u : Concentration S) := by
        have hval : ((c • u : N.stoichSubspace) : Concentration S)
            = c • (u : Concentration S) := rfl
        rw [hhu, hval, entropyHessianQuadratic_smul]
      rw [hDh, hQh]
      have hsq : 0 < c ^ 2 := by positivity
      have step1 : c ^ 2 * N.stoichDissipation κ x u ≤ c ^ 2 * N.stoichDissipation κ x a :=
        mul_le_mul_of_nonneg_left hDu (le_of_lt hsq)
      have step2 : c ^ 2 * N.stoichDissipation κ x a
          = -lam * (c ^ 2 * entropyHessianQuadratic x (b : Concentration S)) := by
        rw [hDaeq]; ring
      have step3 : -lam * (c ^ 2 * entropyHessianQuadratic x (b : Concentration S))
          ≤ -lam * (c ^ 2 * entropyHessianQuadratic x (u : Concentration S)) := by
        have hmul : c ^ 2 * entropyHessianQuadratic x (u : Concentration S)
            ≤ c ^ 2 * entropyHessianQuadratic x (b : Concentration S) :=
          mul_le_mul_of_nonneg_left hQu (le_of_lt hsq)
        nlinarith [hlampos, hmul]
      linarith [step1, step2, step3]


/-! ## The nonlinear remainder -/

/-- A complex-balanced concentration is a mass-action steady state: the kinetic map vanishes,
hence so does its image under the complex map. -/
theorem isMassActionSteadyState_of_isComplexBalanced (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hcb : N.IsComplexBalanced κ x) :
    N.IsMassActionSteadyState κ x := by
  intro s
  rw [N.massActionVectorField_eq κ x, (N.isComplexBalanced_iff_kineticMap κ x).1 hcb,
    map_zero]
  rfl

/-- Cauchy--Schwarz-type bound for the entropy-Hessian pairing in the sup norm. -/
theorem abs_entropyHessianPairing_le {x : Concentration S} (hx : x.Positive)
    (u v : Concentration S) :
    |entropyHessianPairing x u v| ≤ (∑ s : S, 1 / x s) * (‖u‖ * ‖v‖) := by
  rw [entropyHessianPairing]
  have hterm : ∀ s ∈ (Finset.univ : Finset S),
      |u s / x s * v s| ≤ (1 / x s) * (‖u‖ * ‖v‖) := by
    intro s _
    have h1 : |u s| ≤ ‖u‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm u s
    have h2 : |v s| ≤ ‖v‖ := by simpa [Real.norm_eq_abs] using norm_le_pi_norm v s
    have hrw : |u s / x s * v s| = (1 / x s) * (|u s| * |v s|) := by
      rw [abs_mul, abs_div, abs_of_pos (hx s)]
      ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg u))
      (div_nonneg zero_le_one (hx s).le)
  calc |∑ s : S, u s / x s * v s|
      ≤ ∑ s : S, |u s / x s * v s| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : S, (1 / x s) * (‖u‖ * ‖v‖) := Finset.sum_le_sum hterm
    _ = (∑ s : S, 1 / x s) * (‖u‖ * ‖v‖) := by rw [Finset.sum_mul]

/-- **First-order remainder bound at a steady state.**  Fréchet differentiability of the
mass-action vector field turns the Jacobian into a genuine linear approximation: near a
steady state the nonlinear remainder is dominated by any prescribed multiple of `‖e‖`. -/
theorem exists_remainder_bound (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hss : N.IsMassActionSteadyState κ xstar)
    {η : ℝ} (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ e : Concentration S, ‖e‖ < δ →
      ‖N.massActionVectorField κ (xstar + e)
        - (N.massActionJacobian κ xstar).mulVec e‖ ≤ η * ‖e‖ := by
  have hderiv := N.massActionVectorField_hasFDerivAt κ xstar
  rw [hasFDerivAt_iff_isLittleO] at hderiv
  have hev := isLittleO_iff.1 hderiv hη
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨δ, hδ, hball⟩ := hev
  refine ⟨δ, hδ, fun e he => ?_⟩
  have hF0 : N.massActionVectorField κ xstar = 0 := by
    funext s
    exact hss s
  have hdist : dist (xstar + e) xstar < δ := by
    rw [dist_eq_norm]
    simpa using he
  have hb := hball hdist
  rw [hF0, N.massActionJacobianCLM_apply κ] at hb
  simpa using hb

/-! ## A forward Grönwall comparison -/

/-- Grönwall comparison needing the differential inequality only on `[0, b]`. -/
theorem le_mul_exp_of_forward_deriv_le {V V' : ℝ → ℝ} {K b : ℝ}
    (hV : ∀ t ∈ Set.Icc (0 : ℝ) b, HasDerivAt V (V' t) t)
    (bound : ∀ t ∈ Set.Ico (0 : ℝ) b, V' t ≤ K * V t) :
    ∀ t ∈ Set.Icc (0 : ℝ) b, V t ≤ V 0 * Real.exp (K * t) := by
  intro t ht
  have key : V t ≤ gronwallBound (V 0) K 0 (t - 0) := by
    refine le_gronwallBound_of_liminf_deriv_right_le
      (f := V) (f' := V') (δ := V 0) (K := K) (ε := 0) (a := 0) (b := b)
      ?_ ?_ le_rfl ?_ t ht
    · intro y hy
      exact ((hV y hy).continuousAt).continuousWithinAt
    · intro y hy r hr
      have hyIcc : y ∈ Set.Icc (0 : ℝ) b := Set.mem_Icc_of_Ico hy
      have hslope :=
        ((hV y hyIcc).hasDerivWithinAt (s := Set.Ici y)).liminf_right_slope_le hr
      refine hslope.mono fun z hz => ?_
      simpa only [slope, smul_eq_mul, vsub_eq_sub] using hz
    · intro y hy
      simpa using bound y hy
  simpa only [sub_zero, gronwallBound_ε0] using key


/-! ## The Lyapunov function along a trajectory -/

/-- Derivative of the entropy-Hessian quadratic Lyapunov function along a mass-action
trajectory. -/
theorem hasDerivAt_quadraticLyapunov (N : Network S) (κ : N.RateConstants)
    (xstar : Concentration S) {γ : ℝ → Concentration S} {t : ℝ}
    (hγ : HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    HasDerivAt (fun τ => entropyHessianQuadratic xstar (γ τ - xstar))
      (2 * entropyHessianPairing xstar (γ t - xstar)
        (N.massActionVectorField κ (γ t))) t := by
  have hcoord : ∀ s : S, HasDerivAt (fun τ => γ τ s)
      (N.massActionVectorField κ (γ t) s) t := fun s => (hasDerivAt_pi.mp hγ) s
  have hterm : ∀ s : S, HasDerivAt (fun τ : ℝ => (γ τ s - xstar s) ^ 2 / xstar s)
      (2 * ((γ t s - xstar s) / xstar s * N.massActionVectorField κ (γ t) s)) t := by
    intro s
    have h1 : HasDerivAt (fun τ => γ τ s - xstar s)
        (N.massActionVectorField κ (γ t) s) t := (hcoord s).sub_const _
    refine HasDerivAt.congr_deriv (((h1.pow 2).div_const (xstar s))) ?_
    push_cast
    ring
  have hraw := HasDerivAt.fun_sum (u := (Finset.univ : Finset S))
    (fun s (_ : s ∈ (Finset.univ : Finset S)) => hterm s)
  have hfun : (fun τ : ℝ => ∑ s : S, (γ τ s - xstar s) ^ 2 / xstar s)
      = fun τ : ℝ => entropyHessianQuadratic xstar (γ τ - xstar) := by
    funext τ
    rw [entropyHessianQuadratic]
    exact Finset.sum_congr rfl fun s _ => by rw [Pi.sub_apply]
  have hval : (∑ s : S, 2 * ((γ t s - xstar s) / xstar s *
        N.massActionVectorField κ (γ t) s))
      = 2 * entropyHessianPairing xstar (γ t - xstar)
        (N.massActionVectorField κ (γ t)) := by
    rw [entropyHessianPairing, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by rw [Pi.sub_apply]
  rw [← hfun, ← hval]
  exact hraw

/-! ## Forward trapping and exponential decay for scalar Lyapunov functions -/

/-- **Trapping.**  A forward-differentiable function starting strictly below a threshold, whose
derivative is nonpositive whenever the function is below that threshold, never reaches it. -/
theorem forward_lt_of_deriv_nonpos_of_lt {V V' : ℝ → ℝ} {K : ℝ}
    (hV : ∀ τ, 0 ≤ τ → HasDerivAt V (V' τ) τ)
    (hV0 : V 0 < K)
    (hbound : ∀ τ, 0 ≤ τ → V τ < K → V' τ ≤ 0) :
    ∀ τ, 0 ≤ τ → V τ < K := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨T, hT0, hTK⟩ := hcon
  have hVcontT : ContinuousOn V (Set.Icc 0 T) := by
    intro y hy
    exact ((hV y hy.1).continuousAt).continuousWithinAt
  set A : Set ℝ := Set.Icc 0 T ∩ V ⁻¹' (Set.Ici K) with hAdef
  have hAcl : IsClosed A :=
    hVcontT.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hAne : A.Nonempty := ⟨T, ⟨hT0, le_refl T⟩, hTK⟩
  have hAbdd : BddBelow A := ⟨0, fun τ hτ => hτ.1.1⟩
  have ht₁A : sInf A ∈ A := hAcl.csInf_mem hAne hAbdd
  set t₁ := sInf A with ht₁def
  have ht₁0 : 0 ≤ t₁ := ht₁A.1.1
  have ht₁T : t₁ ≤ T := ht₁A.1.2
  have ht₁K : K ≤ V t₁ := ht₁A.2
  have ht₁pos : 0 < t₁ := by
    rcases ht₁0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at ht₁K
      linarith
  have hbelow : ∀ τ, 0 ≤ τ → τ < t₁ → V τ < K := by
    intro τ hτ0 hτlt
    by_contra hge
    push_neg at hge
    have hmem : τ ∈ A := ⟨⟨hτ0, le_trans hτlt.le ht₁T⟩, hge⟩
    exact absurd (csInf_le hAbdd hmem) (not_le.mpr hτlt)
  have hanti : AntitoneOn V (Set.Icc 0 t₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc 0 t₁) ?_ ?_ ?_
    · intro y hy
      exact ((hV y hy.1).continuousAt).continuousWithinAt
    · intro y hy
      rw [interior_Icc, Set.mem_Ioo] at hy
      exact ((hV y hy.1.le).differentiableAt).differentiableWithinAt
    · intro y hy
      rw [interior_Icc, Set.mem_Ioo] at hy
      rw [(hV y hy.1.le).deriv]
      exact hbound y hy.1.le (hbelow y hy.1.le hy.2)
  have hle : V t₁ ≤ V 0 :=
    hanti (Set.left_mem_Icc.mpr ht₁0) (Set.right_mem_Icc.mpr ht₁0) ht₁0
  linarith

/-- **Exponential decay from a trapped strict Lyapunov inequality.** -/
theorem forward_le_mul_exp_of_deriv_le_of_lt {V V' : ℝ → ℝ} {K lam : ℝ}
    (hV : ∀ τ, 0 ≤ τ → HasDerivAt V (V' τ) τ)
    (hVnn : ∀ τ, 0 ≤ V τ) (hV0 : V 0 < K) (hlam : 0 < lam)
    (hbound : ∀ τ, 0 ≤ τ → V τ < K → V' τ ≤ -lam * V τ) :
    ∀ τ, 0 ≤ τ → V τ ≤ V 0 * Real.exp (-lam * τ) := by
  have htrap : ∀ τ, 0 ≤ τ → V τ < K := by
    refine forward_lt_of_deriv_nonpos_of_lt hV hV0 (fun τ hτ hlt => ?_)
    have h1 := hbound τ hτ hlt
    have h2 := hVnn τ
    nlinarith
  intro t ht
  exact le_mul_exp_of_forward_deriv_le (K := -lam) (b := t)
    (fun τ hτ => hV τ hτ.1) (fun τ hτ => hbound τ hτ.1 (htrap τ hτ.1)) t
    ⟨ht, le_refl t⟩

/-! ## Splitting the pairing -/

theorem entropyHessianPairing_split (x u v w : Concentration S) :
    entropyHessianPairing x u v
      = entropyHessianPairing x u w + entropyHessianPairing x u (v - w) := by
  rw [entropyHessianPairing, entropyHessianPairing, entropyHessianPairing,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Pi.sub_apply]
  ring

/-! ## Local exponential stability -/

set_option maxHeartbeats 1000000 in
/-- **Local exponential stability from strict quadratic dissipation.**  At a positive steady
state whose entropy-metric dissipation is strictly negative on every nonzero stoichiometric
tangent vector, every genuine forward mass-action trajectory starting close enough in the
stoichiometric class converges exponentially to the steady state. -/
theorem locallyExponentiallyStableInClass_of_strictDissipation (N : Network S)
    (κ : N.RateConstants) {xstar : Concentration S} (hxs : xstar.Positive)
    (hss : N.IsMassActionSteadyState κ xstar)
    (hneg : ∀ h : N.stoichSubspace, h ≠ 0 → N.stoichDissipation κ xstar h < 0) :
    N.LocallyExponentiallyStableInClass κ xstar := by
  obtain ⟨lam, hlam, hrate⟩ := N.exists_stoich_decay_rate κ hxs hneg
  have hMxnn : (0 : ℝ) ≤ ∑ s : S, 1 / xstar s :=
    Finset.sum_nonneg fun s _ => div_nonneg zero_le_one (hxs s).le
  have hBpos : (0 : ℝ) < (∑ s : S, xstar s) + 1 := by
    have : (0 : ℝ) ≤ ∑ s : S, xstar s := Finset.sum_nonneg fun s _ => (hxs s).le
    linarith
  set Mx : ℝ := ∑ s : S, 1 / xstar s with hMxdef
  set B : ℝ := (∑ s : S, xstar s) + 1 with hBdef
  set C₁ : ℝ := Mx + 1 with hC₁def
  have hC₁pos : 0 < C₁ := by rw [hC₁def]; linarith
  set η : ℝ := lam / (2 * (Mx * B + 1)) with hηdef
  have hdenpos : 0 < 2 * (Mx * B + 1) := by nlinarith [hMxnn, hBpos]
  have hηpos : 0 < η := div_pos hlam hdenpos
  have hηeq : η * (2 * (Mx * B + 1)) = lam := by
    rw [hηdef]
    field_simp
  obtain ⟨δ, hδ, hrem⟩ := N.exists_remainder_bound κ hss hηpos
  set C : ℝ := Real.sqrt (B * C₁) with hCdef
  have hCpos : 0 < C := Real.sqrt_pos.mpr (mul_pos hBpos hC₁pos)
  have hCsq : C ^ 2 = B * C₁ := Real.sq_sqrt (mul_pos hBpos hC₁pos).le
  set ε : ℝ := δ / (C + 1) with hεdef
  have hεpos : 0 < ε := div_pos hδ (by linarith)
  have hεδ : ε * (C + 1) = δ := by
    rw [hεdef]
    field_simp
  have hkey : B * C₁ * ε ^ 2 < δ ^ 2 := by
    rw [← hCsq, ← hεδ]
    nlinarith [hCpos, hεpos, mul_pos (mul_pos hεpos hεpos) hCpos]
  refine ⟨ε, C, lam / 2, hεpos, hCpos, by linarith, ?_⟩
  intro x₀ γ hx₀ hcompat hnorm hγ0 hγd
  -- the displacement stays stoichiometric
  have heS : ∀ τ : ℝ, 0 ≤ τ → γ τ - xstar ∈ N.stoichSubspace := by
    intro τ hτ
    have h1 : γ τ - γ 0 ∈ N.stoichSubspace :=
      N.sub_mem_stoichSubspace_of_solution κ hτ (fun u hu => hγd u hu.1)
    have h2 : x₀ - xstar ∈ N.stoichSubspace := hcompat
    have h3 : γ τ - xstar = (γ τ - γ 0) + (x₀ - xstar) := by
      rw [hγ0]; abel
    rw [h3]
    exact N.stoichSubspace.add_mem h1 h2
  have hVnn : ∀ τ : ℝ, 0 ≤ entropyHessianQuadratic xstar (γ τ - xstar) :=
    fun τ => entropyHessianQuadratic_nonneg hxs _
  have hVle : ∀ τ : ℝ, entropyHessianQuadratic xstar (γ τ - xstar)
      ≤ C₁ * ‖γ τ - xstar‖ ^ 2 := by
    intro τ
    have h1 := entropyHessianQuadratic_le hxs (γ τ - xstar)
    have h2 : (0 : ℝ) ≤ ‖γ τ - xstar‖ ^ 2 := sq_nonneg _
    rw [← hMxdef] at h1
    nlinarith [h1, h2]
  have hnormle : ∀ τ : ℝ, ‖γ τ - xstar‖ ^ 2
      ≤ B * entropyHessianQuadratic xstar (γ τ - xstar) := by
    intro τ
    have := norm_sq_le_entropyHessianQuadratic hxs (γ τ - xstar)
    rw [← hBdef] at this
    exact this
  have hVderiv : ∀ τ : ℝ, 0 ≤ τ →
      HasDerivAt (fun σ => entropyHessianQuadratic xstar (γ σ - xstar))
        (2 * entropyHessianPairing xstar (γ τ - xstar)
          (N.massActionVectorField κ (γ τ))) τ :=
    fun τ hτ => N.hasDerivAt_quadraticLyapunov κ xstar (hγd τ hτ)
  have hsmall : ∀ τ : ℝ, entropyHessianQuadratic xstar (γ τ - xstar) < C₁ * ε ^ 2 →
      ‖γ τ - xstar‖ < δ := by
    intro τ hlt
    have h1 := hnormle τ
    have h2 : B * entropyHessianQuadratic xstar (γ τ - xstar) < B * (C₁ * ε ^ 2) :=
      mul_lt_mul_of_pos_left hlt hBpos
    have h3 : B * (C₁ * ε ^ 2) = B * C₁ * ε ^ 2 := by ring
    nlinarith [norm_nonneg (γ τ - xstar), hδ, hkey]
  have hV0 : entropyHessianQuadratic xstar (γ 0 - xstar) < C₁ * ε ^ 2 := by
    have he0 : ‖γ 0 - xstar‖ < ε := by rw [hγ0]; exact hnorm
    have h1 := hVle 0
    have h2 : ‖γ 0 - xstar‖ ^ 2 < ε ^ 2 := by
      nlinarith [norm_nonneg (γ 0 - xstar), hεpos, he0]
    nlinarith [hC₁pos, h1, h2]
  -- the strict differential inequality inside the trapping region
  have hbound : ∀ τ : ℝ, 0 ≤ τ →
      entropyHessianQuadratic xstar (γ τ - xstar) < C₁ * ε ^ 2 →
      2 * entropyHessianPairing xstar (γ τ - xstar) (N.massActionVectorField κ (γ τ))
        ≤ -lam * entropyHessianQuadratic xstar (γ τ - xstar) := by
    intro τ hτ hlt
    have hnδ : ‖γ τ - xstar‖ < δ := hsmall τ hlt
    have heSτ : γ τ - xstar ∈ N.stoichSubspace := heS τ hτ
    have hFeq : N.massActionVectorField κ (γ τ)
        = N.massActionVectorField κ (xstar + (γ τ - xstar)) := by
      congr 1
      abel
    have hRbound : ‖N.massActionVectorField κ (γ τ)
        - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar)‖ ≤ η * ‖γ τ - xstar‖ := by
      rw [hFeq]
      exact hrem (γ τ - xstar) hnδ
    have hsplit : entropyHessianPairing xstar (γ τ - xstar)
          (N.massActionVectorField κ (γ τ))
        = entropyHessianPairing xstar (γ τ - xstar)
            ((N.massActionJacobian κ xstar).mulVec (γ τ - xstar))
          + entropyHessianPairing xstar (γ τ - xstar)
            (N.massActionVectorField κ (γ τ)
              - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar)) :=
      entropyHessianPairing_split _ _ _ _
    have hDle : entropyHessianPairing xstar (γ τ - xstar)
        ((N.massActionJacobian κ xstar).mulVec (γ τ - xstar))
        ≤ -lam * entropyHessianQuadratic xstar (γ τ - xstar) :=
      hrate ⟨γ τ - xstar, heSτ⟩
    have hRle : entropyHessianPairing xstar (γ τ - xstar)
        (N.massActionVectorField κ (γ τ)
          - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar))
        ≤ Mx * (‖γ τ - xstar‖ * ‖N.massActionVectorField κ (γ τ)
          - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar)‖) := by
      have habs := abs_entropyHessianPairing_le hxs (γ τ - xstar)
        (N.massActionVectorField κ (γ τ)
          - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar))
      rw [← hMxdef] at habs
      exact le_trans (le_abs_self _) habs
    have hprod : ‖γ τ - xstar‖ * ‖N.massActionVectorField κ (γ τ)
        - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar)‖
        ≤ η * (B * entropyHessianQuadratic xstar (γ τ - xstar)) := by
      have h1 : ‖γ τ - xstar‖ * ‖N.massActionVectorField κ (γ τ)
          - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar)‖
          ≤ ‖γ τ - xstar‖ * (η * ‖γ τ - xstar‖) :=
        mul_le_mul_of_nonneg_left hRbound (norm_nonneg _)
      have h2 := hnormle τ
      nlinarith [hηpos, norm_nonneg (γ τ - xstar)]
    have hfinal : 2 * (Mx * (η * (B * entropyHessianQuadratic xstar (γ τ - xstar))))
        ≤ lam * entropyHessianQuadratic xstar (γ τ - xstar) := by
      have hVn := hVnn τ
      nlinarith [hηeq, hηpos, hMxnn, hVn]
    have hmono : Mx * (‖γ τ - xstar‖ * ‖N.massActionVectorField κ (γ τ)
        - (N.massActionJacobian κ xstar).mulVec (γ τ - xstar)‖)
        ≤ Mx * (η * (B * entropyHessianQuadratic xstar (γ τ - xstar))) :=
      mul_le_mul_of_nonneg_left hprod hMxnn
    rw [hsplit]
    linarith [hDle, hRle, hmono, hfinal]
  have hdecay := forward_le_mul_exp_of_deriv_le_of_lt
    (V := fun τ => entropyHessianQuadratic xstar (γ τ - xstar))
    (V' := fun τ => 2 * entropyHessianPairing xstar (γ τ - xstar)
      (N.massActionVectorField κ (γ τ)))
    (K := C₁ * ε ^ 2) (lam := lam) hVderiv hVnn hV0 hlam hbound
  intro t ht
  have hd := hdecay t ht
  have he0 : ‖γ 0 - xstar‖ = ‖x₀ - xstar‖ := by rw [hγ0]
  have hexp : (Real.exp (-(lam / 2) * t)) ^ 2 = Real.exp (-lam * t) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hsqle : ‖γ t - xstar‖ ^ 2
      ≤ (C * Real.exp (-(lam / 2) * t) * ‖x₀ - xstar‖) ^ 2 := by
    have h1 := hnormle t
    have h2 : B * entropyHessianQuadratic xstar (γ t - xstar)
        ≤ B * (entropyHessianQuadratic xstar (γ 0 - xstar) * Real.exp (-lam * t)) :=
      mul_le_mul_of_nonneg_left hd hBpos.le
    have h3 : entropyHessianQuadratic xstar (γ 0 - xstar) ≤ C₁ * ‖x₀ - xstar‖ ^ 2 := by
      have := hVle 0
      rwa [he0] at this
    have h4 : (0 : ℝ) < Real.exp (-lam * t) := Real.exp_pos _
    have h5 : (C * Real.exp (-(lam / 2) * t) * ‖x₀ - xstar‖) ^ 2
        = (B * C₁) * (Real.exp (-lam * t) * ‖x₀ - xstar‖ ^ 2) := by
      rw [mul_pow, mul_pow, hexp, hCsq]
      ring
    have h6 : entropyHessianQuadratic xstar (γ 0 - xstar) * Real.exp (-lam * t)
        ≤ (C₁ * ‖x₀ - xstar‖ ^ 2) * Real.exp (-lam * t) :=
      mul_le_mul_of_nonneg_right h3 h4.le
    have h7 : B * (entropyHessianQuadratic xstar (γ 0 - xstar) * Real.exp (-lam * t))
        ≤ B * ((C₁ * ‖x₀ - xstar‖ ^ 2) * Real.exp (-lam * t)) :=
      mul_le_mul_of_nonneg_left h6 hBpos.le
    have h8 : B * ((C₁ * ‖x₀ - xstar‖ ^ 2) * Real.exp (-lam * t))
        = (B * C₁) * (Real.exp (-lam * t) * ‖x₀ - xstar‖ ^ 2) := by ring
    rw [h5]
    linarith [h1, h2, h7, h8]
  have hRnn : (0 : ℝ) ≤ C * Real.exp (-(lam / 2) * t) * ‖x₀ - xstar‖ :=
    mul_nonneg (mul_nonneg hCpos.le (Real.exp_pos _).le) (norm_nonneg _)
  have hfin := Real.sqrt_le_sqrt hsqle
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hRnn] at hfin

end QuadraticStability

/-- Local exponential stability of a positive complex-balanced equilibrium within its
stoichiometric class.  The only remaining ingredient after the CRNT quadratic-form theorem is
the standard finite-dimensional nonlinear linearization theorem. -/
theorem complexBalanced_locallyExponentiallyStable_in_class
    (N : Network S) (κ : N.RateConstants) (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) :
    N.LocallyExponentiallyStableInClass κ xstar := by
  refine N.locallyExponentiallyStableInClass_of_strictDissipation κ hxs
    (N.isMassActionSteadyState_of_isComplexBalanced κ hcb) ?_
  intro h h0
  have hne : (h : Concentration S) ≠ 0 := fun hz => h0 (Subtype.ext hz)
  exact N.complexBalanceJacobianQuadratic_strict_on_stoich κ hwr hxs hcb h.2 hne

end Network
end CRNT
