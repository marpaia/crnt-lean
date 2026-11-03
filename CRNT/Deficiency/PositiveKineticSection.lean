import CRNT.Deficiency.BorosDeficiencyOneReduction
import Mathlib.Topology.MetricSpace.Basic
namespace CRNT.Network
open scoped BigOperators Classical Topology
variable {S : Type} [DecidableEq S] [Fintype S]
/-- A positive affine kinetic section through a strictly positive kernel point. -/
theorem exists_positiveAffineKineticSection (N : Network S) (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    {g : N.ComplexIdx → ℝ} (hg : g ∈ N.deficiencySubspace) :
    ∃ (b z : N.ComplexIdx → ℝ) (ε : ℝ),
      0 < ε ∧ (∀ c, 0 < b c) ∧ N.kineticMap κ b = 0 ∧ N.kineticMap κ z = g ∧
      ∀ a, |a| < ε → (∀ c, 0 < (b + a • z) c) ∧
        N.kineticMap κ (b + a • z) = a • g := by
  obtain ⟨b, hbpos, hbker⟩ := PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ
  have hgA : g ∈ LinearMap.range (N.kineticMap κ) := by
    rw [N.range_kineticMap_eq_range_incidenceMap_of_weaklyReversible hwr κ]
    exact hg.2
  obtain ⟨z, hz⟩ := hgA
  let U : Set ℝ := {a | ∀ c, 0 < (b + a • z) c}
  have hUopen : IsOpen U := by
    rw [show U = ⋂ c : N.ComplexIdx, (fun a : ℝ => (b + a • z) c) ⁻¹' Set.Ioi 0 by
      ext a
      simp [U]]
    apply isOpen_iInter_of_finite
    intro c
    apply Continuous.isOpen_preimage
    · fun_prop
    · exact isOpen_Ioi
  have h0U : (0 : ℝ) ∈ U := by simpa [U] using hbpos
  have hnhds : U ∈ 𝓝 (0 : ℝ) := hUopen.mem_nhds h0U
  rw [Metric.mem_nhds_iff] at hnhds
  obtain ⟨ε, hε, hball⟩ := hnhds
  refine ⟨b, z, ε, hε, hbpos, hbker, hz, ?_⟩
  intro a ha
  have haU : a ∈ U := hball ?_
  · refine ⟨haU, ?_⟩
    rw [map_add, map_smul, hbker, hz]
    simp
  · simpa [Real.dist_eq] using ha
end CRNT.Network

namespace CRNT.Network
open scoped BigOperators Classical Topology
variable {S : Type} [DecidableEq S] [Fintype S]

/-- The affine kinetic section is continuous as a vector-valued map. -/
theorem continuous_positiveAffineKineticSection
    (b z : ι → ℝ) : Continuous (fun a : ℝ => b + a • z) := by
  fun_prop

/-- On an interval where the affine section is positive, its componentwise logarithm is
continuous. This is the analytic input needed to turn the remaining Type-II compatibility
condition into a scalar intermediate-value problem. -/
theorem continuousOn_log_positiveAffineKineticSection
    (b z : ι → ℝ) {ε : ℝ}
    (hpos : ∀ a, |a| < ε → ∀ i, 0 < (b + a • z) i) :
    ContinuousOn (fun a : ℝ => fun i => Real.log ((b + a • z) i)) (Set.Ioo (-ε) ε) := by
  rw [continuousOn_pi]
  intro i
  apply ContinuousOn.log
  · exact ((continuous_apply i).comp (continuous_positiveAffineKineticSection b z)).continuousOn
  · intro a ha
    exact (hpos a (by simpa [abs_lt] using ha) i).ne'

end CRNT.Network
