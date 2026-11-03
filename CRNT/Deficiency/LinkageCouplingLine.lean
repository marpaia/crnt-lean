import CRNT.Deficiency.LinkageCoupling
import CRNT.Deficiency.DeficiencyOneLocalize
import Mathlib.LinearAlgebra.DFinsupp

namespace CRNT
namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

abbrev LinkageStoichProduct (N : Network S) :=
  ∀ q : Quotient N.linkedSetoid, N.linkageStoichSubspace q

noncomputable def linkageStoichSumMap (N : Network S) :
    N.LinkageStoichProduct →ₗ[ℝ] (S → ℝ) where
  toFun u := ∑ q, (u q : S → ℝ)
  map_add' u v := by
    simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' a u := by
    simp only [Pi.smul_apply, Submodule.coe_smul_of_tower, RingHom.id_apply, Finset.smul_sum]

@[simp] theorem linkageStoichSumMap_apply (N : Network S) (u : N.LinkageStoichProduct) :
    N.linkageStoichSumMap u = ∑ q, (u q : S → ℝ) := rfl

theorem range_linkageStoichSumMap (N : Network S) :
    LinearMap.range N.linkageStoichSumMap = N.stoichSubspace := by
  classical
  apply le_antisymm
  · rintro x ⟨u, rfl⟩
    exact Submodule.sum_mem _ fun q _ => N.linkageStoichSubspace_le q (u q).2
  · rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    let q0 := N.classOf (N.sourceIdx r)
    let u : N.LinkageStoichProduct := fun q =>
      if h : q = q0 then
        ⟨N.reactionVector r, h ▸ N.reactionVector_mem_linkageStoichSubspace r⟩
      else 0
    refine ⟨u, ?_⟩
    rw [N.linkageStoichSumMap_apply]
    rw [Finset.sum_eq_single q0]
    · simp [u, q0]
    · intro q _ hq
      simp [u, hq]
    · intro h
      exact absurd (Finset.mem_univ q0) h

theorem finrank_linkageStoichProduct (N : Network S) :
    Module.finrank ℝ N.LinkageStoichProduct = ∑ q, N.linkageStoichRank q := by
  classical
  rw [Module.finrank_pi_fintype]
  rfl

theorem finrank_ker_linkageStoichSumMap (N : Network S) :
    Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) = N.linkageCouplingDeficiency := by
  classical
  have hdim := LinearMap.finrank_range_add_finrank_ker N.linkageStoichSumMap
  rw [N.range_linkageStoichSumMap] at hdim
  rw [N.finrank_linkageStoichProduct] at hdim
  change N.stoichRank + Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) =
    ∑ q, N.linkageStoichRank q at hdim
  have hc := N.stoichRank_add_linkageCoupling_eq_sum
  omega

/-- When the coupling deficiency is one, the classwise stoichiometric relations form a line. -/
theorem exists_spanning_linkageStoichCoupling_of_coupling_one (N : Network S)
    (hc : N.linkageCouplingDeficiency = 1) :
    ∃ g : N.LinkageStoichProduct, N.linkageStoichSumMap g = 0 ∧ g ≠ 0 ∧
      ∀ w : N.LinkageStoichProduct, N.linkageStoichSumMap w = 0 →
        ∃ a : ℝ, a • g = w := by
  have hrank : Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) = 1 := by
    rw [N.finrank_ker_linkageStoichSumMap, hc]
  haveI : Nontrivial (LinearMap.ker N.linkageStoichSumMap) :=
    Module.nontrivial_of_finrank_pos (by rw [hrank]; norm_num)
  obtain ⟨g', hg'0⟩ := exists_ne (0 : LinearMap.ker N.linkageStoichSumMap)
  have hg0 : (g' : N.LinkageStoichProduct) ≠ 0 := by simpa using hg'0
  refine ⟨g'.val, g'.property, hg0, fun w hw => ?_⟩
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one
    (K := ℝ) (V := LinearMap.ker N.linkageStoichSumMap) hrank hg'0
    (⟨w, hw⟩ : LinearMap.ker N.linkageStoichSumMap)
  exact ⟨a, congrArg Subtype.val ha⟩

/-- Restriction to a linkage class is additive. -/
theorem restrictToClass_add (N : Network S) (q : Quotient N.linkedSetoid)
    (v w : N.ComplexIdx → ℝ) :
    N.restrictToClass q (v + w) = N.restrictToClass q v + N.restrictToClass q w := by
  funext c
  simp only [restrictToClass, Pi.add_apply]
  by_cases hc : N.classOf c = q <;> simp [hc]

/-- Restriction to a linkage class commutes with scalar multiplication. -/
theorem restrictToClass_smul (N : Network S) (q : Quotient N.linkedSetoid)
    (a : ℝ) (v : N.ComplexIdx → ℝ) :
    N.restrictToClass q (a • v) = a • N.restrictToClass q v := by
  funext c
  simp only [restrictToClass, Pi.smul_apply, smul_eq_mul]
  by_cases hc : N.classOf c = q <;> simp [hc]

/-- Send a global deficiency vector to its classwise species-space imbalance.  The `q` component
is `Y (g|_q)`, which lies in the `q`-th linkage stoichiometric subspace. -/
noncomputable def deficiencyToLinkageCoupling (N : Network S) :
    N.deficiencySubspace →ₗ[ℝ] N.LinkageStoichProduct where
  toFun g := fun q => ⟨N.complexMap (N.restrictToClass q g.1),
    N.complexMap_restrictToClass_mem_linkageStoichSubspace q g.2.2⟩
  map_add' g h := by
    funext q
    apply Subtype.ext
    change N.complexMap (N.restrictToClass q (g.1 + h.1)) =
      N.complexMap (N.restrictToClass q g.1) + N.complexMap (N.restrictToClass q h.1)
    rw [N.restrictToClass_add, map_add]
  map_smul' a g := by
    funext q
    apply Subtype.ext
    change N.complexMap (N.restrictToClass q (a • g.1)) =
      a • N.complexMap (N.restrictToClass q g.1)
    rw [N.restrictToClass_smul, map_smul]

/-- Every deficiency vector gives a genuine linkage-coupling relation: its classwise species
imbalances sum to zero. -/
theorem deficiencyToLinkageCoupling_mem_ker (N : Network S) (g : N.deficiencySubspace) :
    N.linkageStoichSumMap (N.deficiencyToLinkageCoupling g) = 0 := by
  rw [N.linkageStoichSumMap_apply]
  change (∑ q, N.complexMap (N.restrictToClass q g.1)) = 0
  rw [← map_sum, N.sum_restrictToClass]
  exact g.2.1

/-- The deficiency-to-coupling bridge with codomain restricted to the coupling kernel. -/
noncomputable def deficiencyToLinkageCouplingKer (N : Network S) :
    N.deficiencySubspace →ₗ[ℝ] LinearMap.ker N.linkageStoichSumMap :=
  N.deficiencyToLinkageCoupling.codRestrict (LinearMap.ker N.linkageStoichSumMap)
    (fun g => N.deficiencyToLinkageCoupling_mem_ker g)

/-- If every linkage class has deficiency zero, the bridge from the global deficiency space to
classwise stoichiometric coupling is injective.  Thus in Type II the unique global deficiency mode
is exactly the unique linear dependence among linkage stoichiometric subspaces. -/
theorem deficiencyToLinkageCoupling_injective_of_all_linkageDeficiency_zero (N : Network S)
    (hzero : ∀ q, N.linkageDeficiency q = 0) :
    Function.Injective N.deficiencyToLinkageCoupling := by
  intro g h heq
  apply Subtype.ext
  have hres : ∀ q, N.restrictToClass q (g.1 - h.1) = 0 := by
    intro q
    have hcomp : N.complexMap (N.restrictToClass q (g.1 - h.1)) = 0 := by
      have hq := congrArg (fun u : N.LinkageStoichProduct => (u q : S → ℝ)) heq
      change N.complexMap (N.restrictToClass q g.1) =
        N.complexMap (N.restrictToClass q h.1) at hq
      have hrsub : N.restrictToClass q (g.1 - h.1) =
          N.restrictToClass q g.1 - N.restrictToClass q h.1 := by
        funext c
        simp only [restrictToClass, Pi.sub_apply]
        split <;> simp_all
      rw [hrsub, map_sub, hq, sub_self]
    have hrange : N.restrictToClass q (g.1 - h.1) ∈ LinearMap.range N.incidenceMap := by
      apply N.restrictToClass_mem_range_incidenceMap q
      exact (LinearMap.range N.incidenceMap).sub_mem g.2.2 h.2.2
    have hdef : N.restrictToClass q (g.1 - h.1) ∈ N.deficiencySubspace := by
      exact ⟨hcomp, hrange⟩
    have hsupp := N.restrictToClass_mem_supportedOn q (g.1 - h.1)
    have hlocal : N.restrictToClass q (g.1 - h.1) ∈ N.linkageDeficiencySubspace q :=
      ⟨hdef, hsupp⟩
    rw [N.linkageDeficiencySubspace_eq_bot_of_deficiency_zero (hzero q)] at hlocal
    exact (Submodule.mem_bot ℝ).mp hlocal
  have hsum := congrArg (fun v => ∑ q, v q) (funext hres)
  have hsub : g.1 - h.1 = 0 := by simpa [N.sum_restrictToClass] using hsum
  exact sub_eq_zero.mp hsub

/-- **Type-II coupling is exactly the global deficiency line.**  Under total deficiency one and
zero deficiency in every linkage class, the global deficiency subspace is linearly equivalent to
the kernel of the classwise stoichiometric sum map.  Both are one-dimensional. -/
noncomputable def typeIILinkageCouplingEquiv (N : Network S) (hδ : N.DeficiencyOne)
    (hzero : ∀ q, N.linkageDeficiency q = 0)
    (hc : N.linkageCouplingDeficiency = 1) :
    N.deficiencySubspace ≃ₗ[ℝ] LinearMap.ker N.linkageStoichSumMap := by
  let f := N.deficiencyToLinkageCouplingKer
  have hinj0 : Function.Injective N.deficiencyToLinkageCoupling :=
    N.deficiencyToLinkageCoupling_injective_of_all_linkageDeficiency_zero hzero
  have hinj : Function.Injective f := by
    intro g h heq
    apply hinj0
    exact congrArg Subtype.val heq
  have hdom : Module.finrank ℝ N.deficiencySubspace = 1 :=
    (deficiencyOne_iff_deficiency_eq_one N).mp hδ
  have hcod : Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) = 1 := by
    rw [N.finrank_ker_linkageStoichSumMap, hc]
  have hrank : Module.finrank ℝ N.deficiencySubspace =
      Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) := by rw [hdom, hcod]
  exact LinearEquiv.ofInjectiveOfFinrankEq
    (K := ℝ) (V := N.deficiencySubspace)
    (V' := LinearMap.ker N.linkageStoichSumMap) f hinj hrank

end Network
end CRNT
