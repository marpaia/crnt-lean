import CRNT.Equilibria.TreeConstants
import CRNT.Deficiency.PerClassKernelUnique
import CRNT.Deficiency.PositiveKineticPreimageWR
import CRNT.Deficiency.DeficiencyOneRowDefect
import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.SteadyStateKernel
import CRNT.Deficiency.BorosBirchGraph

/-!
# Linear reduction for weakly reversible deficiency-one existence

This module isolates the part of the Boros existence argument that is purely linear.  At
deficiency one there is a nonzero generator `g` of `ker Y ∩ Im ∂`.  Weak reversibility makes
`Im A_k = Im ∂` and supplies a positive kinetic kernel vector, so **every scalar multiple of `g`**
has a strictly positive preimage under `A_k`.  Simultaneously, the stoichiometric transpose row
space is a hyperplane in the incidence transpose row space.  Thus exactly one nonlinear scalar
monomial-realization obstruction remains.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]


/-- **Canonical per-class kinetic kernel mode.**  On a weakly reversible linkage class, the
restriction of the tree-constant vector spans every kinetic-kernel vector supported on that class.
This is the canonicity needed before parameterizing the Type-II positive kinetic preimages. -/
theorem perClass_kernel_eq_smul_treeConstants
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (θ : Quotient N.linkedSetoid) {v : N.ComplexIdx → ℝ}
    (hvoff : ∀ c, N.classOf c ≠ θ → v c = 0)
    (hvker : N.kineticMap κ v = 0) :
    ∃ t : ℝ, v = t • N.restrictToClass θ (N.treeConstantVector κ) := by
  let b := N.restrictToClass θ (N.treeConstantVector κ)
  have hbpos : ∀ c, N.classOf c = θ → 0 < b c := by
    intro c hc
    rw [show b c = N.treeConstantVector κ c by
      exact N.restrictToClass_apply_of_eq (N.treeConstantVector κ) hc]
    exact (N.treeConstantVector_positive_kernel κ hwr).1 c
  have hboff : ∀ c, N.classOf c ≠ θ → b c = 0 := by
    intro c hc
    exact N.restrictToClass_apply_of_ne (N.treeConstantVector κ) hc
  have hbker : N.kineticMap κ b = 0 := by
    rw [show b = N.restrictToClass θ (N.treeConstantVector κ) from rfl,
      N.kineticMap_restrictToClass, (N.treeConstantVector_positive_kernel κ hwr).2]
    funext c
    by_cases hc : N.classOf c = θ <;> simp [restrictToClass, hc]
  exact N.perClass_kernel_unique κ θ
    (fun c c' hc hc' => hwr.reaches_of_linked (Quotient.exact (hc.trans hc'.symm)))
    hbpos hboff hbker hvoff hvker


/-- The full kinetic kernel is the direct sum of the canonical per-class tree-constant modes. -/
theorem kineticKernel_decompose_treeConstants
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} (hvker : N.kineticMap κ v = 0) :
    ∃ coeff : (Quotient N.linkedSetoid) → ℝ,
      v = ∑ θ, coeff θ • N.restrictToClass θ (N.treeConstantVector κ) := by
  classical
  have hclassker : ∀ θ, N.kineticMap κ (N.restrictToClass θ v) = 0 := by
    intro θ
    rw [N.kineticMap_restrictToClass, hvker]
    funext c
    simp [restrictToClass]
  have hex : ∀ θ, ∃ a : ℝ,
      N.restrictToClass θ v = a • N.restrictToClass θ (N.treeConstantVector κ) := by
    intro θ
    apply N.perClass_kernel_eq_smul_treeConstants hwr κ θ
    · intro c hc
      exact N.restrictToClass_apply_of_ne v hc
    · exact hclassker θ
  choose coeff hcoeff using hex
  refine ⟨coeff, ?_⟩
  rw [← N.sum_restrictToClass v]
  apply Finset.sum_congr rfl
  intro θ _
  exact hcoeff θ

/-- Every preimage of a point on a fixed kinetic line is an affine translate of the canonical
per-class tree-constant kernel modes.  Thus after choosing one particular preimage `z` of `g`, the
only free linear parameters are one scalar per linkage class. -/
theorem kineticPreimage_affine_treeConstants
    (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g z v : N.ComplexIdx → ℝ} (hz : N.kineticMap κ z = g) {a : ℝ}
    (hv : N.kineticMap κ v = a • g) :
    ∃ coeff : (Quotient N.linkedSetoid) → ℝ,
      v = a • z + ∑ θ, coeff θ • N.restrictToClass θ (N.treeConstantVector κ) := by
  have hker : N.kineticMap κ (v - a • z) = 0 := by
    rw [map_sub, map_smul, hv, hz, sub_self]
  obtain ⟨coeff, hcoeff⟩ := N.kineticKernel_decompose_treeConstants hwr κ hker
  refine ⟨coeff, ?_⟩
  have hadd := congrArg (fun w : N.ComplexIdx → ℝ => w + a • z) hcoeff
  simpa [sub_add_cancel, add_comm] using hadd

/-- **Boros linear reduction.** A weakly reversible deficiency-one system has a fixed nonzero
`g ∈ ker Y ∩ Im ∂` spanning the deficiency space, and every point `a • g` on that line has a
strictly positive kinetic preimage. -/
theorem exists_positiveKineticLine_of_weaklyReversible_deficiencyOne
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne)
    (κ : N.RateConstants) :
    ∃ g : N.ComplexIdx → ℝ,
      g ∈ N.deficiencySubspace ∧ g ≠ 0 ∧
      (∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w) ∧
      ∀ a : ℝ, ∃ v : N.ComplexIdx → ℝ,
        (∀ c, 0 < v c) ∧ N.kineticMap κ v = a • g := by
  obtain ⟨g, hgD, hg0, hspan⟩ := N.exists_spanning_deficiencySubspace_of_deficiencyOne hδ
  refine ⟨g, hgD, hg0, hspan, ?_⟩
  intro a
  exact N.exists_strictlyPositive_kineticPreimage_smul_of_mem_deficiencySubspace hwr κ hgD a

/-- If a positive kinetic preimage on the deficiency line is realized exactly as a mass-action
monomial vector, then the realizing concentration is a steady state. -/
theorem isMassActionSteadyState_of_realizes_deficiencyKineticPreimage
    (N : Network S) (κ : N.RateConstants)
    {g v : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) {a : ℝ}
    {x : Concentration S} (hmono : N.complexMonomialVector x = v)
    (hAv : N.kineticMap κ v = a • g) : N.IsMassActionSteadyState κ x := by
  intro s
  have hgY : N.complexMap g = 0 := LinearMap.mem_ker.mp hg.1
  have hzero : N.complexMap (a • g) = 0 := by rw [map_smul, hgY, smul_zero]
  show N.massActionVectorField κ x s = 0
  rw [N.massActionVectorField_eq κ x, hmono, hAv, hzero]
  rfl

/-- Consequently, the full classwise existence theorem is reduced to realizing **one** positive
kinetic preimage on the deficiency line as the monomial vector of a concentration in the requested
positive compatibility class. -/
theorem exists_positiveSteadyState_of_deficiencyLine_monomial_realization
    (N : Network S) (κ : N.RateConstants) {x₀ : Concentration S}
    {g : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace)
    (hrealize : ∃ a : ℝ, ∃ v : N.ComplexIdx → ℝ, ∃ x : Concentration S,
      (∀ c, 0 < v c) ∧ x ∈ N.positiveCompatibilityClass x₀ ∧
      N.complexMonomialVector x = v ∧ N.kineticMap κ v = a • g) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  rcases hrealize with ⟨a, v, x, _, hxclass, hmono, hAv⟩
  exact ⟨x, hxclass,
    N.isMassActionSteadyState_of_realizes_deficiencyKineticPreimage κ hg hmono hAv⟩

/-- Any positive steady state gives the synchronized class-scale realization required by the
Type-II reduction: choose its own monomial vector and unit scale on every linkage class. -/
theorem exists_synchronized_classScale_realization_of_positiveSteadyState
    (N : Network S) (κ : N.RateConstants) {x₀ x : Concentration S}
    (hxclass : x ∈ N.positiveCompatibilityClass x₀)
    (hxss : N.IsMassActionSteadyState κ x)
    {g : N.ComplexIdx → ℝ}
    (hspan : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w) :
    ∃ (a : ℝ) (v : N.ComplexIdx → ℝ) (x : Concentration S)
      (lambda : Quotient N.linkedSetoid → ℝ),
      (∀ c, 0 < v c) ∧
      x ∈ N.positiveCompatibilityClass x₀ ∧
      (∀ q, 0 < lambda q) ∧
      (∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) ∧
      N.kineticMap κ v = a • g ∧
      ∃ L : ℝ, 0 < L ∧ ∀ q,
        N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 →
          lambda q = L := by
  have hdef := N.kineticMap_complexMonomial_mem_deficiencySubspace κ hxss
  obtain ⟨a, ha⟩ := hspan _ hdef
  refine ⟨a, N.complexMonomialVector x, x, (fun _ => 1), ?_, hxclass,
    (fun _ => by norm_num), ?_, ha.symm, ?_⟩
  · intro c
    rw [N.complexMonomialVector_apply]
    exact Complex.massActionMonomial_pos hxclass.2 c.val
  · intro c
    simp
  · refine ⟨1, by norm_num, ?_⟩
    intro q hq
    rfl

/-- The remaining Type-II realization reduces to the active-face inward estimates for Boros's
Birch graph. Once those estimates hold on a nested domain, the projected-field zero is a positive
steady state in the requested class, and its unit class scales give the exact synchronized
realization required by the deficiency-one reduction. -/
theorem exists_borosTypeII_realization_of_activeInward
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)] (κ : N.RateConstants)
    {x₀ : Concentration S} {g : N.ComplexIdx → ℝ}
    (x : N.borosBirchParameterSpace → Concentration S)
    (hxcont : Continuous x) (hxpos : ∀ z s, 0 < x z s)
    (hxclass : ∀ z, x z ∈ N.positiveCompatibilityClass x₀)
    (hspan : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, a • g = w)
    (r : ℕ → ℝ)
    (hinward : ∀ z ∈ Analysis.borosWithinSubspaceNestedDomain
          N.borosLinkageProjectionSystem N.borosBirchParameterSpace r,
      ∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
        ‖Analysis.borosWithinSubspaceProjectionFamily
            N.borosLinkageProjectionSystem N.borosBirchParameterSpace Q z‖ =
          Analysis.borosProjectionRadius r Q →
        0 < inner ℝ (N.borosBirchKineticProjectionField κ x z)
          (Analysis.borosWithinSubspaceProjectionFamily
            N.borosLinkageProjectionSystem N.borosBirchParameterSpace Q z)) :
    ∃ (a : ℝ) (v : N.ComplexIdx → ℝ) (y : Concentration S)
      (lambda : Quotient N.linkedSetoid → ℝ),
      (∀ c, 0 < v c) ∧
      y ∈ N.positiveCompatibilityClass x₀ ∧
      (∀ q, 0 < lambda q) ∧
      (∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector y c) ∧
      N.kineticMap κ v = a • g ∧
      ∃ L : ℝ, 0 < L ∧ ∀ q,
        N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 →
          lambda q = L := by
  obtain ⟨y, hyclass, hyss⟩ :=
    N.exists_borosBirchSteadyState_of_activeInward κ x hxcont hxpos hxclass r hinward
  exact N.exists_synchronized_classScale_realization_of_positiveSteadyState
    κ hyclass hyss hspan

end Network
end CRNT
