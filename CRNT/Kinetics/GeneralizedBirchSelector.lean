import CRNT.Kinetics.GeneralizedBirchExistence
import CRNT.Kinetics.GeneralizedBirchLocal

/-!
# Continuous generalized-Birch selectors

The generalized Birch quotient map is an open embedding under the closure condition.
Consequently, any continuous family of positive target representatives has a continuous
lift to the toric parameter space.  This packages the continuity that the Type-II
weakly-reversible deficiency-one argument needs.
-/

namespace CRNT

open scoped Classical

variable {ι α : Type} [Fintype ι] [DecidableEq ι] [TopologicalSpace α]

/-- The generalized Birch quotient map is an open embedding. -/
theorem generalizedBirchQuotientMap_isOpenEmbedding
    {S T : Submodule ℝ (ι → ℝ)} (hclosure : GeneralizedClosureCondition S T)
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) :
    Topology.IsOpenEmbedding (generalizedBirchQuotientMap S T xstar c) := by
  have hlocal := generalizedBirchQuotientMap_isLocalHomeomorph (c := c) hclosure hxs
  exact Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap
    hlocal.continuous (generalizedBirchQuotientMap_injective hclosure hxs) hlocal.isOpenMap

/-- A continuous positive family of target representatives admits a continuous lift through
    the generalized Birch quotient map. -/
theorem exists_continuous_generalizedBirchQuotientLift
    (S T : Submodule ℝ (ι → ℝ)) (hclosure : GeneralizedClosureCondition S T)
    (xstar : ι → ℝ) (hxs : ∀ i, 0 < xstar i)
    (c : α → (ι → ℝ)) (hcpos : ∀ a i, 0 < c a i) (hccont : Continuous c) :
    ∃ w : α → orthSum T, Continuous w ∧
      ∀ a, generalizedBirchQuotientMap S T xstar 0 (w a) = S.mkQ (c a) := by
  have hex : ∀ a, ∃ w : orthSum T,
      generalizedBirchQuotientMap S T xstar 0 w = S.mkQ (c a) := by
    intro a
    obtain ⟨x, hxpos, hxS, hxT⟩ :=
      generalized_birch_existence_of_conditions S T hclosure xstar (c a) hxs (hcpos a)
    let w : orthSum T := ⟨fun i => Real.log (x i) - Real.log (xstar i), hxT⟩
    refine ⟨w, ?_⟩
    rw [generalizedBirchQuotientMap]
    change S.mkQ (generalizedBirchExpAffine xstar 0 w.1) = S.mkQ (c a)
    have hxeq : (fun i => xstar i * Real.exp (w.1 i)) = x := by
      funext i
      dsimp [w]
      rw [Real.exp_sub, Real.exp_log (hxpos i), Real.exp_log (hxs i)]
      field_simp [(hxs i).ne']
    have haff : generalizedBirchExpAffine xstar 0 w.1 = x := by
      funext i
      simp [generalizedBirchExpAffine, congrFun hxeq i]
    rw [haff]
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero S).mpr hxS
  choose w hw using hex
  refine ⟨w, ?_, hw⟩
  have hemb := generalizedBirchQuotientMap_isOpenEmbedding (c := (0 : ι → ℝ)) hclosure hxs
  apply hemb.isInducing.continuous_iff.mpr
  have heq : generalizedBirchQuotientMap S T xstar 0 ∘ w = fun a => S.mkQ (c a) := by
    funext a
    exact hw a
  rw [heq]
  exact S.mkQL.continuous.comp hccont

/-- The lifted toric family itself is continuous and stays in the requested affine classes. -/
theorem exists_continuous_generalizedBirchSelector
    (S T : Submodule ℝ (ι → ℝ)) (hclosure : GeneralizedClosureCondition S T)
    (xstar : ι → ℝ) (hxs : ∀ i, 0 < xstar i)
    (c : α → (ι → ℝ)) (hcpos : ∀ a i, 0 < c a i) (hccont : Continuous c) :
    ∃ x : α → (ι → ℝ), Continuous x ∧ (∀ a i, 0 < x a i) ∧
      ∀ a, x a - c a ∈ S ∧
        (fun i => Real.log (x a i) - Real.log (xstar i)) ∈ orthSum T := by
  obtain ⟨w, hwcont, hwq⟩ :=
    exists_continuous_generalizedBirchQuotientLift S T hclosure xstar hxs c hcpos hccont
  let x : α → (ι → ℝ) := fun a i => xstar i * Real.exp ((w a).1 i)
  refine ⟨x, ?_, ?_, ?_⟩
  · apply continuous_pi
    intro i
    exact (continuous_const.mul (Real.continuous_exp.comp
      ((continuous_apply i).comp (continuous_subtype_val.comp hwcont))))
  · intro a i
    exact mul_pos (hxs i) (Real.exp_pos _)
  · intro a
    constructor
    · apply (Submodule.Quotient.mk_eq_zero S).mp
      have hz : S.mkQL (x a - c a) = 0 := by
        rw [map_sub]
        have hq := hwq a
        have hq' : S.mkQ (x a) = S.mkQ (c a) := by
          rw [← hq]
          congr 1
          funext i
          simp [x, generalizedBirchQuotientMap, generalizedBirchExpAffine]
        have hqL : S.mkQL (x a) = S.mkQL (c a) := hq'
        rw [hqL, sub_self]
      exact hz
    · have hwmem : ((w a : orthSum T) : ι → ℝ) ∈ orthSum T := (w a).2
      convert hwmem using 1
      funext i
      dsimp [x]
      rw [Real.log_mul (hxs i).ne' (Real.exp_ne_zero _), Real.log_exp]
      ring

/-- The continuous generalized-Birch selector also works when the positive reference point moves
with the parameter. The proof packages the family of quotient maps into one map on a product;
its derivative is block triangular, with the identity on the parameter coordinate and the
invertible generalized-Birch derivative on each fibre. -/
theorem exists_continuous_generalizedBirchSelector_varyingReference
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (S T : Submodule ℝ (ι → ℝ)) (hclosure : GeneralizedClosureCondition S T)
    (xstar : E → (ι → ℝ)) (hxstar : ContDiff ℝ 1 xstar)
    (hxstarpos : ∀ a i, 0 < xstar a i)
    (c : E → (ι → ℝ)) (hc : ContDiff ℝ 1 c)
    (hcpos : ∀ a i, 0 < c a i) :
    ∃ x : E → (ι → ℝ), Continuous x ∧ (∀ a i, 0 < x a i) ∧
      ∀ a, x a - c a ∈ S ∧
        (fun i => Real.log (x a i) - Real.log (xstar a i)) ∈ orthSum T := by
  classical
  let W := orthSum T
  let Q := (ι → ℝ) ⧸ S
  let G : E × W → Q := fun p =>
    generalizedBirchQuotientMap S T (xstar p.1) 0 p.2
  let F : E × W → E × Q := fun p => (p.1, G p)
  letI : IsClosed (S : Set (ι → ℝ)) := S.closed_of_finiteDimensional
  have hxparam : ContDiff ℝ 1 (fun p : E × W => xstar p.1) :=
    hxstar.comp contDiff_fst
  have hwparam : ContDiff ℝ 1 (fun p : E × W => p.2.1) :=
    (W.subtypeL.contDiff).comp contDiff_snd
  have hval : ContDiff ℝ 1 (fun p : E × W =>
      fun i => xstar p.1 i * Real.exp (p.2.1 i)) := by
    apply contDiff_pi.mpr
    intro i
    have hstarCoord : ContDiff ℝ 1 (fun p : E × W => xstar p.1 i) :=
      (contDiff_apply ℝ ℝ i).comp hxparam
    have hwCoord : ContDiff ℝ 1 (fun p : E × W => p.2.1 i) :=
      (contDiff_apply ℝ ℝ i).comp hwparam
    have hexpCoord : ContDiff ℝ 1 (fun p : E × W => Real.exp (p.2.1 i)) :=
      (Real.contDiff_exp (n := 1)).comp hwCoord
    exact hstarCoord.mul hexpCoord
  have hG : ContDiff ℝ 1 G := by
    have hval' : ContDiff ℝ 1 (fun p : E × W =>
        generalizedBirchExpAffine (xstar p.1) 0 p.2.1) := by
      convert hval using 1
      funext p i
      simp [generalizedBirchExpAffine]
    change ContDiff ℝ 1 (fun p : E × W => S.mkQ
      (generalizedBirchExpAffine (xstar p.1) 0 p.2.1))
    exact (S.mkQL.contDiff).comp hval'
  have hF : ContDiff ℝ 1 F := by
    change ContDiff ℝ 1 (fun p : E × W => (p.1, G p))
    exact (ContinuousLinearMap.fst ℝ E W).contDiff.prodMk hG

  have hQ : Module.finrank ℝ Q = Fintype.card ι - Module.finrank ℝ T := by
    dsimp [Q]
    rw [S.finrank_quotient, Module.finrank_fintype_fun_eq_card, hclosure.finrank_eq]
  have hdim : Module.finrank ℝ (E × W) = Module.finrank ℝ (E × Q) := by
    rw [Module.finrank_prod, Module.finrank_prod, finrank_orthSum, hQ]

  have hGderiv_ker (p : E × W) (q : E × W)
      (hq : fderiv ℝ F p q = 0) : q = 0 := by
    have hGdiff : DifferentiableAt ℝ G p := (hG.differentiable (by norm_num)) p
    have hFderiv : HasFDerivAt F (fderiv ℝ F p) p :=
      ((hF.differentiable (by norm_num)) p).hasFDerivAt
    have hpair : HasFDerivAt F
        ((ContinuousLinearMap.fst ℝ E W).prod (fderiv ℝ G p)) p := by
      exact (ContinuousLinearMap.fst ℝ E W).hasFDerivAt.prodMk
        (hGdiff.hasFDerivAt)
    have hdeq := hFderiv.unique hpair
    rw [hdeq] at hq
    have hq1 : q.1 = 0 := by
      have := congrArg Prod.fst hq
      simpa using this
    have hq2 : fderiv ℝ G p q = 0 := by
      have := congrArg Prod.snd hq
      simpa using this
    have hqprod : q = (0, q.2) := Prod.ext hq1 rfl
    have hfiberComp : HasFDerivAt (fun w : W => G (p.1, w))
        ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E W)) p.2 := by
      have hGat : HasFDerivAt G (fderiv ℝ G p) (p.1, p.2) := by
        simpa only [Prod.eta] using hGdiff.hasFDerivAt
      exact HasFDerivAt.comp (g := G) (f := fun w : W => (p.1, w))
        (x := p.2) hGat (hasFDerivAt_prodMk_right p.1 p.2)
    have hfiber : HasFDerivAt (fun w : W => G (p.1, w))
        (generalizedBirchQuotientDeriv S T (xstar p.1) p.2).toContinuousLinearMap p.2 := by
      simpa [G] using
        (hasStrictFDerivAt_generalizedBirchQuotientMap S T (xstar p.1) 0 p.2).hasFDerivAt
    have hfibereq := hfiberComp.unique hfiber
    have hlast :
        ((generalizedBirchQuotientDeriv S T (xstar p.1) p.2).toContinuousLinearMap) q.2 = 0 := by
      calc
        _ = ((fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ E W)) q.2 := by
          rw [hfibereq]
        _ = fderiv ℝ G p (0, q.2) := rfl
        _ = fderiv ℝ G p q := by rw [← hqprod]
        _ = 0 := hq2
    have hker : q.2 ∈ LinearMap.ker
        (generalizedBirchQuotientDeriv S T (xstar p.1) p.2) :=
      LinearMap.mem_ker.mpr (by exact hlast)
    have hker0 := generalizedBirchQuotientDeriv_ker_eq_bot hclosure
      (hxstarpos p.1) p.2
    rw [hker0] at hker
    exact Prod.ext hq1 (by simpa using hker)
  have hGderiv_inj (p : E × W) : Function.Injective (fderiv ℝ F p) := by
    intro q r hqr
    apply sub_eq_zero.mp
    apply hGderiv_ker p (q - r)
    rw [map_sub, hqr, sub_self]

  let derivEquiv (p : E × W) : (E × W) ≃L[ℝ] (E × Q) :=
    (LinearEquiv.ofInjectiveOfFinrankEq (fderiv ℝ F p) (hGderiv_inj p) hdim).toContinuousLinearEquiv
  have hstrict : ∀ p : E × W,
      HasStrictFDerivAt F (derivEquiv p : (E × W) →L[ℝ] (E × Q)) p := by
    intro p
    have h := hF.hasStrictFDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0) (x := p)
    have heq : (derivEquiv p : (E × W) →L[ℝ] (E × Q)) = fderiv ℝ F p := by
      have hcoe := LinearEquiv.coe_ofInjectiveOfFinrankEq
        (fderiv ℝ F p) (hGderiv_inj p) hdim
      apply ContinuousLinearMap.ext
      intro q
      exact congrArg (fun L : (E × W) →ₗ[ℝ] (E × Q) => L q) hcoe
    exact h.congr_fderiv heq.symm
  have hopen : IsOpenMap F := isOpenMap_of_hasStrictFDerivAt_equiv hstrict
  have hinj : Function.Injective F := by
    intro p q hpq
    have hfirst : p.1 = q.1 := congrArg (Prod.fst : E × Q → E) hpq
    have hsecond : G p = G q := congrArg (Prod.snd : E × Q → Q) hpq
    have hlast : p.2 = q.2 := by
      apply generalizedBirchQuotientMap_injective hclosure (hxstarpos p.1)
      simpa [G, hfirst] using hsecond
    exact Prod.ext hfirst hlast
  have hemb : Topology.IsOpenEmbedding F :=
    Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hF.continuous hinj hopen

  have hex : ∀ a, ∃ w : W,
      generalizedBirchQuotientMap S T (xstar a) 0 w = S.mkQ (c a) := by
    intro a
    obtain ⟨y, hypos, hyS, hyT⟩ :=
      generalized_birch_existence_of_conditions S T hclosure (xstar a) (c a)
        (hxstarpos a) (hcpos a)
    let w : W := ⟨fun i => Real.log (y i) - Real.log (xstar a i), hyT⟩
    refine ⟨w, ?_⟩
    rw [generalizedBirchQuotientMap]
    change S.mkQ (generalizedBirchExpAffine (xstar a) 0 w.1) = S.mkQ (c a)
    have hyEq : (fun i => xstar a i * Real.exp (w.1 i)) = y := by
      funext i
      dsimp [w]
      rw [Real.exp_sub, Real.exp_log (hypos i), Real.exp_log (hxstarpos a i)]
      field_simp [(hxstarpos a i).ne']
    have hvalEq : generalizedBirchExpAffine (xstar a) 0 w.1 = y := by
      funext i
      simp [generalizedBirchExpAffine, congrFun hyEq i]
    rw [hvalEq]
    apply sub_eq_zero.mp
    rw [← map_sub]
    exact (Submodule.Quotient.mk_eq_zero S).mpr hyS
  choose w hw using hex
  have hgraph : Continuous fun a : E => (a, w a) := by
    apply hemb.isInducing.continuous_iff.mpr
    have hcomp : F ∘ (fun a : E => (a, w a)) =
        fun a => (a, S.mkQ (c a)) := by
      funext a
      exact Prod.ext rfl (hw a)
    rw [hcomp]
    exact continuous_id.prodMk (S.mkQL.continuous.comp hc.continuous)
  have hwcont : Continuous w := continuous_snd.comp hgraph
  let x : E → (ι → ℝ) := fun a i => xstar a i * Real.exp ((w a).1 i)
  have hxcont : Continuous x := by
    apply continuous_pi
    intro i
    exact ((continuous_apply i).comp hxstar.continuous).mul
      (Real.continuous_exp.comp
        ((continuous_apply i).comp (continuous_subtype_val.comp hwcont)))
  refine ⟨x, hxcont, ?_, ?_⟩
  · intro a i
    exact mul_pos (hxstarpos a i) (Real.exp_pos _)
  · intro a
    constructor
    · have hq : S.mkQL (x a - c a) = 0 := by
        rw [map_sub]
        have hw' := hw a
        change S.mkQL (generalizedBirchExpAffine (xstar a) 0 (w a).1) =
          S.mkQL (c a) at hw'
        have hxeq : generalizedBirchExpAffine (xstar a) 0 (w a).1 = x a := by
          funext i
          simp [generalizedBirchExpAffine, x]
        rw [← hxeq, hw', sub_self]
      exact (Submodule.Quotient.mk_eq_zero S).mp hq
    · have hlog : (fun i => Real.log (x a i) - Real.log (xstar a i)) = (w a).1 := by
        funext i
        simp only [x]
        rw [Real.log_mul (hxstarpos a i).ne' (Real.exp_ne_zero _), Real.log_exp]
        ring
      rw [hlog]
      exact (w a).2

end CRNT
