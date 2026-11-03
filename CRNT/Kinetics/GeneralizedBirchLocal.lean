import CRNT.Kinetics.GeneralizedNondegeneracy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.Analysis.Normed.Group.CocompactMap
import Mathlib.Topology.Maps.Proper.CompactlyGenerated
import Mathlib.Topology.IsLocalHomeomorph

/-!
# Local differential geometry of the generalized Birch map

For subspaces `S,T ⊆ ℝ^ι`, positive `x*`, and an affine-class representative `c`, the
existence problem

`x = x* ⊙ exp w`, `w ∈ Tᗮ`, `x - c ∈ S`

is the zero-fibre problem for the quotient-valued map

`F(w) = [x* ⊙ exp w - c] ∈ (ℝ^ι)/S`.

Under `GeneralizedClosureCondition S T`, this file proves the finite-dimensional local part of
the generalized Birch theorem completely:

* the derivative is the quotient of the positive diagonal scaling `diag(x)` restricted to `Tᗮ`;
* sign transversality makes this derivative injective;
* the rank condition makes it an isomorphism;
* hence `F` is a local homeomorphism everywhere;
* the already-proved generalized Birch uniqueness theorem makes `F` globally injective.

Thus the remaining global existence issue is exactly properness/closedness at infinity of `F`.
-/

namespace CRNT

variable {ι : Type*} [Fintype ι]

/-- Ambient exponential affine map used before quotienting by `S`. -/
noncomputable def generalizedBirchExpAffine (xstar c : ι → ℝ) (w : ι → ℝ) : ι → ℝ :=
  fun i => xstar i * Real.exp (w i) - c i

/-- Derivative of `generalizedBirchExpAffine`: positive diagonal scaling at the current point. -/
noncomputable def generalizedBirchExpAffineDeriv (xstar : ι → ℝ) (w : ι → ℝ) :
    (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  (diagonalScale (fun i => xstar i * Real.exp (w i))).toContinuousLinearMap

/-- The ambient exponential affine map has the expected strict derivative. -/
theorem hasStrictFDerivAt_generalizedBirchExpAffine (xstar c w : ι → ℝ) :
    HasStrictFDerivAt (generalizedBirchExpAffine xstar c)
      (generalizedBirchExpAffineDeriv xstar w) w := by
  rw [hasStrictFDerivAt_pi']
  intro i
  change HasStrictFDerivAt (fun z : ι → ℝ => xstar i * Real.exp (z i) - c i)
    ((ContinuousLinearMap.proj (R := ℝ) i).comp (generalizedBirchExpAffineDeriv xstar w)) w
  have hcoord : HasStrictFDerivAt (fun z : ι → ℝ => z i)
      (ContinuousLinearMap.proj (R := ℝ) i) w :=
    hasStrictFDerivAt_apply (𝕜 := ℝ) i w
  have h := (Real.hasStrictDerivAt_exp (w i)).comp_hasStrictFDerivAt w hcoord
  have h2 := h.const_mul (xstar i)
  have h3 := h2.sub_const (c i)
  have h3' : HasStrictFDerivAt (fun z : ι → ℝ => xstar i * Real.exp (z i) - c i)
      ((xstar i * Real.exp (w i)) • ContinuousLinearMap.proj (R := ℝ) i) w := by
    simpa only [Function.comp_apply, smul_smul] using h3
  exact h3'.congr_fderiv (by
    apply ContinuousLinearMap.ext
    intro z
    simp [generalizedBirchExpAffineDeriv, diagonalScale])

/-- Quotient-valued generalized Birch map.  Its zero fibre is precisely the desired affine/toric
intersection. -/
noncomputable def generalizedBirchQuotientMap
    (S T : Submodule ℝ (ι → ℝ)) (xstar c : ι → ℝ)
    (w : orthSum T) : (ι → ℝ) ⧸ S :=
  S.mkQ (generalizedBirchExpAffine xstar c w.1)

/-- Algebraic derivative of the quotient-valued generalized Birch map. -/
noncomputable def generalizedBirchQuotientDeriv
    (S T : Submodule ℝ (ι → ℝ)) (xstar : ι → ℝ) (w : orthSum T) :
    orthSum T →ₗ[ℝ] ((ι → ℝ) ⧸ S) :=
  S.mkQ.comp
    ((diagonalScale (fun i => xstar i * Real.exp (w.1 i))).comp (orthSum T).subtype)

/-- Strict derivative formula for the quotient-valued generalized Birch map. -/
theorem hasStrictFDerivAt_generalizedBirchQuotientMap
    (S T : Submodule ℝ (ι → ℝ)) (xstar c : ι → ℝ) (w : orthSum T) :
    HasStrictFDerivAt (generalizedBirchQuotientMap S T xstar c)
      (generalizedBirchQuotientDeriv S T xstar w).toContinuousLinearMap w := by
  letI : IsClosed (S : Set (ι → ℝ)) := S.closed_of_finiteDimensional
  have h1 := hasStrictFDerivAt_generalizedBirchExpAffine
    (xstar := xstar) (c := c) (w := w.1)
  have hsub := h1.comp w (orthSum T).subtypeL.hasStrictFDerivAt
  have hq := (S.mkQ.toContinuousLinearMap.hasStrictFDerivAt).comp w hsub
  exact hq.congr_fderiv (by
    apply ContinuousLinearMap.ext
    intro v
    rfl)

/-- Under the closure condition and positivity, the generalized Birch derivative has trivial
kernel.  This is exactly the transversality theorem in quotient coordinates. -/
theorem generalizedBirchQuotientDeriv_ker_eq_bot
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar : ι → ℝ} (hxs : ∀ i, 0 < xstar i) (w : orthSum T) :
    LinearMap.ker (generalizedBirchQuotientDeriv S T xstar w) = ⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  let x : ι → ℝ := fun i => xstar i * Real.exp (w.1 i)
  have hx : ∀ i, 0 < x i := fun i => mul_pos (hxs i) (Real.exp_pos _)
  have hmemS : diagonalScale x v.1 ∈ S := by
    rw [← Submodule.Quotient.mk_eq_zero S]
    change generalizedBirchQuotientDeriv S T xstar w v = 0 at hv
    simpa [generalizedBirchQuotientDeriv, x] using hv
  have hmemTan : diagonalScale x v.1 ∈ toricTangentSubspace T x :=
    ⟨v.1, v.2, rfl⟩
  have hbot : diagonalScale x v.1 ∈ (⊥ : Submodule ℝ (ι → ℝ)) := by
    rw [← generalizedToricNondegenerate_of_signCompatible S T hclosure.signCompatible hx]
    exact ⟨hmemS, hmemTan⟩
  have hz : diagonalScale x v.1 = 0 := by simpa using hbot
  apply Subtype.ext
  funext i
  have hi := congrFun hz i
  change x i * v.1 i = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hx i))

/-- The derivative is a linear equivalence: injectivity comes from sign transversality and
surjectivity from the equal-rank hypothesis. -/
noncomputable def generalizedBirchQuotientDerivEquiv
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar : ι → ℝ} (hxs : ∀ i, 0 < xstar i) (w : orthSum T) :
    orthSum T ≃ₗ[ℝ] ((ι → ℝ) ⧸ S) := by
  apply LinearEquiv.ofInjectiveOfFinrankEq (generalizedBirchQuotientDeriv S T xstar w)
  · exact LinearMap.ker_eq_bot.mp
      (generalizedBirchQuotientDeriv_ker_eq_bot hclosure hxs w)
  · have hdom := finrank_orthSum T
    have hST := hclosure.finrank_eq
    have hq := S.finrank_quotient_add_finrank
    rw [Module.finrank_fintype_fun_eq_card] at hq
    omega

/-- Continuous-linear form of `generalizedBirchQuotientDerivEquiv`. -/
noncomputable def generalizedBirchQuotientDerivCLEquiv
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar : ι → ℝ} (hxs : ∀ i, 0 < xstar i) (w : orthSum T) :
    orthSum T ≃L[ℝ] ((ι → ℝ) ⧸ S) := by
  letI : IsClosed (S : Set (ι → ℝ)) := S.closed_of_finiteDimensional
  exact (generalizedBirchQuotientDerivEquiv hclosure hxs w).toContinuousLinearEquiv

/-- The quotient-valued generalized Birch map is globally injective under the closure condition. -/
theorem generalizedBirchQuotientMap_injective
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) :
    Function.Injective (generalizedBirchQuotientMap S T xstar c) := by
  intro w₁ w₂ hw
  let x₁ : ι → ℝ := fun i => xstar i * Real.exp (w₁.1 i)
  let x₂ : ι → ℝ := fun i => xstar i * Real.exp (w₂.1 i)
  have hx₁ : ∀ i, 0 < x₁ i := fun i => mul_pos (hxs i) (Real.exp_pos _)
  have hx₂ : ∀ i, 0 < x₂ i := fun i => mul_pos (hxs i) (Real.exp_pos _)
  have hmem : x₁ - x₂ ∈ S := by
    rw [← Submodule.Quotient.mk_eq_zero S]
    have hz : S.mkQ (generalizedBirchExpAffine xstar c w₁.1 -
        generalizedBirchExpAffine xstar c w₂.1) = 0 := by
      rw [map_sub]
      change generalizedBirchQuotientMap S T xstar c w₁ -
        generalizedBirchQuotientMap S T xstar c w₂ = 0
      rw [hw, sub_self]
    have heqdiff : generalizedBirchExpAffine xstar c w₁.1 -
        generalizedBirchExpAffine xstar c w₂.1 = x₁ - x₂ := by
      funext i
      simp [generalizedBirchExpAffine, x₁, x₂, Pi.sub_apply]
    rw [← heqdiff]
    exact hz
  have horth : (fun i => Real.log (x₁ i) - Real.log (x₂ i)) ∈ orthSum T := by
    have heq : (fun i => Real.log (x₁ i) - Real.log (x₂ i)) = w₁.1 - w₂.1 := by
      funext i
      change Real.log (x₁ i) - Real.log (x₂ i) = w₁.1 i - w₂.1 i
      simp only [x₁, x₂]
      rw [Real.log_mul (hxs i).ne' (Real.exp_ne_zero _),
        Real.log_mul (hxs i).ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_exp]
      ring
    rw [heq]
    exact (orthSum T).sub_mem w₁.2 w₂.2
  have hxeq : x₁ = x₂ :=
    gen_birch_uniqueness S T hclosure.signCompatible hx₁ hx₂ hmem horth
  apply Subtype.ext
  funext i
  have hi := congrFun hxeq i
  simp only [x₁, x₂] at hi
  have he : Real.exp (w₁.1 i) = Real.exp (w₂.1 i) :=
    (mul_left_cancel₀ (ne_of_gt (hxs i))) hi
  exact Real.exp_injective he

/-- **Local-diffeomorphism half of generalized Birch existence.** Under the closure condition,
the quotient map is a local homeomorphism everywhere.  No properness or degree theory is used. -/
theorem generalizedBirchQuotientMap_isLocalHomeomorph
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) :
    IsLocalHomeomorph (generalizedBirchQuotientMap S T xstar c) := by
  letI : IsClosed (S : Set (ι → ℝ)) := S.closed_of_finiteDimensional
  have hderiv : ∀ w : orthSum T,
      HasStrictFDerivAt (generalizedBirchQuotientMap S T xstar c)
        (generalizedBirchQuotientDerivCLEquiv hclosure hxs w :
          orthSum T →L[ℝ] ((ι → ℝ) ⧸ S)) w := by
    intro w
    have h := hasStrictFDerivAt_generalizedBirchQuotientMap S T xstar c w
    exact h.congr_fderiv (by
      apply ContinuousLinearMap.ext
      intro v
      rfl)
  have hopen : IsOpenMap (generalizedBirchQuotientMap S T xstar c) :=
    isOpenMap_of_hasStrictFDerivAt_equiv hderiv
  have hcont : Continuous (generalizedBirchQuotientMap S T xstar c) :=
    continuous_iff_continuousAt.mpr fun w => (hderiv w).continuousAt
  exact (Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hcont
    (generalizedBirchQuotientMap_injective hclosure hxs) hopen).isLocalHomeomorph

/-- A concrete coercivity criterion for the remaining global step.  In finite dimensions it is
enough to show that the quotient-map norm tends to infinity when the toric parameter norm does. -/
theorem generalizedBirchQuotientMap_isProper_of_norm_coercive
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i)
    (hcoercive : ∀ ε : ℝ, ∃ r : ℝ, ∀ w : orthSum T,
      r < ‖w‖ → ε < ‖generalizedBirchQuotientMap S T xstar c w‖) :
    IsProperMap (generalizedBirchQuotientMap S T xstar c) := by
  letI : IsClosed (S : Set (ι → ℝ)) := S.closed_of_finiteDimensional
  have hlocal := generalizedBirchQuotientMap_isLocalHomeomorph (c := c) hclosure hxs
  have hcont : Continuous (generalizedBirchQuotientMap S T xstar c) := hlocal.continuous
  rw [isProperMap_iff_tendsto_cocompact]
  exact ⟨hcont, Filter.tendsto_cocompact_cocompact_of_norm hcoercive⟩


end CRNT
