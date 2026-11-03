import CRNT.Oscillation.ScalarReturnStability
import CRNT.Oscillation.ContinuousTimeAttraction

/-!
# From a contracting scalar section map to continuous-time orbital attraction

`ScalarReturnStability` proves convergence of scalar Poincare iterates.  `ContinuousTimeAttraction`
proves that convergent section hits plus uniform finite-time shadowing imply attraction of the full
trajectory.  This file closes the bookkeeping bridge between those two results.

A `ScalarSectionInterpolationData` supplies only the geometric information not contained in the
scalar return map: an embedding of section coordinates into phase space, return times, a finite-time
segment flow, and a tail-cover/shadowing estimate.  Convergence of the section states is derived
rather than assumed.
-/

namespace CRNT

open Filter Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {field : E → E} {P : PeriodicTrajectory field}
variable {f : ℝ → ℝ} {x₀ : ℝ}

/-- Geometric realization of a scalar contracting return map as successive hits of a continuous
trajectory near a periodic orbit. -/
structure ScalarSectionInterpolationData
    (D : ScalarLocalContraction f x₀) (hfix : f x₀ = x₀)
    (P : PeriodicTrajectory field) (γ : ℝ → E) where
  /-- Initial scalar section coordinate. -/
  initial : D.LocalInterval
  /-- Embed the local scalar section coordinate into the phase space. -/
  point : D.LocalInterval → E
  /-- The center coordinate represents the reference point of the periodic orbit. -/
  point_center : point D.center = P.orbit 0
  /-- Continuity of the section embedding at the center. -/
  continuousAt_point_center : ContinuousAt point D.center
  /-- Times of successive section hits. -/
  hitTime : ℕ → ℝ
  hitTime_nonneg : ∀ n, 0 ≤ hitTime n
  /-- The trajectory hits exactly the embedded scalar iterates. -/
  hitState_eq : ∀ n,
    γ (hitTime n) = point ((D.toContractingReturnMapData hfix).iterates initial n)
  /-- Finite-time segment evolution from a section hit. -/
  segmentFlow : E → ℝ → E
  maxSegment : ℝ
  maxSegment_nonneg : 0 ≤ maxSegment
  /-- Every sufficiently late trajectory time lies on a bounded segment beginning at a sufficiently
  late section return. -/
  tailCover : ∀ N : ℕ, ∀ t : ℝ, hitTime N ≤ t →
    ∃ n : ℕ, N ≤ n ∧ ∃ s : ℝ,
      0 ≤ s ∧ s ≤ maxSegment ∧ t = hitTime n + s ∧
        γ t = segmentFlow (γ (hitTime n)) s
  /-- Uniform finite-time shadowing of the reference periodic segment. -/
  shadow : ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, dist x (P.orbit 0) < δ →
      ∀ s : ℝ, 0 ≤ s → s ≤ maxSegment →
        dist (segmentFlow x s) (P.orbit s) < ε

namespace ScalarSectionInterpolationData

variable {D : ScalarLocalContraction f x₀} {hfix : f x₀ = x₀}
variable {γ : ℝ → E}

/-- Embedded scalar section iterates converge to the periodic-orbit base point. -/
theorem tendsto_embedded_hits
    (G : ScalarSectionInterpolationData D hfix P γ) :
    Tendsto
      (fun n => G.point ((D.toContractingReturnMapData hfix).iterates G.initial n))
      atTop (𝓝 (P.orbit 0)) := by
  have hscalar :
      Tendsto ((D.toContractingReturnMapData hfix).iterates G.initial) atTop
        (𝓝 (D.toContractingReturnMapData hfix).fixedPoint) :=
    (D.toContractingReturnMapData hfix).tendsto_iterates_fixedPoint G.initial
  have hpoint : Tendsto G.point (𝓝 D.center) (𝓝 (G.point D.center)) :=
    G.continuousAt_point_center
  have hcenter : (D.toContractingReturnMapData hfix).fixedPoint = D.center := rfl
  rw [hcenter] at hscalar
  have hcomp := hpoint.comp hscalar
  simpa only [Function.comp_def, G.point_center] using hcomp

/-- Quantitative eventual form of embedded-hit convergence. -/
theorem embedded_hits_eventually_close
    (G : ScalarSectionInterpolationData D hfix P γ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      dist
        (G.point ((D.toContractingReturnMapData hfix).iterates G.initial n))
        (P.orbit 0) < δ := by
  exact (Metric.tendsto_atTop.mp G.tendsto_embedded_hits) δ hδ

/-- Convert the scalar-section package into the generic continuous-time interpolation certificate.
The section-hit convergence field is proved automatically from contraction. -/
noncomputable def toSectionHitInterpolationData
    (G : ScalarSectionInterpolationData D hfix P γ) :
    SectionHitInterpolationData P γ where
  hitTime := G.hitTime
  hitTime_nonneg := G.hitTime_nonneg
  hitState := fun n => G.point ((D.toContractingReturnMapData hfix).iterates G.initial n)
  segmentFlow := G.segmentFlow
  maxSegment := G.maxSegment
  maxSegment_nonneg := G.maxSegment_nonneg
  hitState_eq := by
    intro n
    exact (G.hitState_eq n).symm
  hit_converges := by
    intro δ hδ
    exact G.embedded_hits_eventually_close hδ
  tailCover := by
    intro N t ht
    obtain ⟨n, hn, s, hs0, hsmax, htime, hseg⟩ := G.tailCover N t ht
    refine ⟨n, hn, s, hs0, hsmax, htime, ?_⟩
    rw [← G.hitState_eq n]
    exact hseg
  shadow := G.shadow

/-- **Scalar contraction to continuous-time attraction.** Once the geometric interpolation data are
supplied, no additional asymptotic argument is required. -/
theorem attractsTrajectory
    (G : ScalarSectionInterpolationData D hfix P γ) :
    P.AttractsTrajectory γ :=
  G.toSectionHitInterpolationData.attractsTrajectory

end ScalarSectionInterpolationData

end CRNT
