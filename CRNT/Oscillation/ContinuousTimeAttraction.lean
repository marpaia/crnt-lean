import CRNT.Oscillation.Basic

/-!
# Continuous-time attraction from convergent section hits

A contracting Poincare map only controls the discrete sequence of section returns.  Orbital
attraction is a continuous-time statement.  This file isolates and proves the interpolation step:
if successive section states converge to a periodic-orbit base point, every late piece of the
trajectory starts from one of those section states, and finite-time flow segments depend uniformly
on the starting point, then the entire trajectory approaches the geometric periodic orbit.

This is the exact nonlinear bridge needed after `ReturnMapAttraction` / `ScalarReturnStability`.
The remaining Floquet-specific work is therefore to verify the finite-time shadowing hypothesis for
the concrete flow (normally from continuous dependence on initial data on a compact time interval).
-/

namespace CRNT

namespace PeriodicTrajectory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {field : E → E}

/-- A single trajectory approaches the geometric image of a periodic orbit, with phase free. -/
def AttractsTrajectory (P : PeriodicTrajectory field) (γ : ℝ → E) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t → ∃ phase : ℝ, dist (γ t) (P.orbit phase) < ε

end PeriodicTrajectory

/-- Data sufficient to interpolate convergence of discrete Poincare hits into continuous-time
orbital attraction.

`segmentFlow x s` is the finite-time trajectory segment starting from a section state `x`.
`shadow` is uniform continuous dependence on the reference periodic segment for
`0 ≤ s ≤ maxSegment`.  The `tailCover` field says that every sufficiently late time belongs to a
segment starting at a sufficiently late section hit. -/
structure SectionHitInterpolationData
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (γ : ℝ → E) where
  hitTime : ℕ → ℝ
  /-- Return times are forward times. -/
  hitTime_nonneg : ∀ n, 0 ≤ hitTime n
  hitState : ℕ → E
  segmentFlow : E → ℝ → E
  maxSegment : ℝ
  maxSegment_nonneg : 0 ≤ maxSegment
  /-- The recorded hit state is the trajectory state at its hit time. -/
  hitState_eq : ∀ n, hitState n = γ (hitTime n)
  /-- Section hits converge to the reference point of the periodic orbit. -/
  hit_converges : ∀ δ : ℝ, 0 < δ →
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → dist (hitState n) (P.orbit 0) < δ
  /-- Every tail of the trajectory is covered by flow segments based at correspondingly late hits. -/
  tailCover : ∀ N : ℕ, ∀ t : ℝ, hitTime N ≤ t →
    ∃ n : ℕ, N ≤ n ∧ ∃ s : ℝ,
      0 ≤ s ∧ s ≤ maxSegment ∧ t = hitTime n + s ∧ γ t = segmentFlow (hitState n) s
  /-- Uniform finite-time dependence of a segment on its starting section state. -/
  shadow : ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : E, dist x (P.orbit 0) < δ →
      ∀ s : ℝ, 0 ≤ s → s ≤ maxSegment →
        dist (segmentFlow x s) (P.orbit s) < ε

namespace SectionHitInterpolationData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {field : E → E} {P : PeriodicTrajectory field} {γ : ℝ → E}

/-- **Discrete-to-continuous attraction theorem.** Convergent section hits plus uniform shadowing
of each bounded return segment imply attraction of the full continuous trajectory to the periodic
orbit. -/
theorem attractsTrajectory (D : SectionHitInterpolationData P γ) :
    P.AttractsTrajectory γ := by
  intro ε hε
  obtain ⟨δ, hδ, hshadow⟩ := D.shadow ε hε
  obtain ⟨N, hN⟩ := D.hit_converges δ hδ
  refine ⟨D.hitTime N, ?_⟩
  intro t ht
  obtain ⟨n, hn, s, hs0, hsmax, htime, hseg⟩ := D.tailCover N t ht
  have hnear : dist (D.hitState n) (P.orbit 0) < δ := hN n hn
  refine ⟨s, ?_⟩
  rw [hseg]
  exact hshadow (D.hitState n) hnear s hs0 hsmax

end SectionHitInterpolationData

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {κ : N.RateConstants}

/-- A basin admits section-hit interpolation data for every exact forward solution.  This is the
continuous-time hypothesis naturally produced after a locally contracting Poincare map has been
constructed. -/
def PositivePeriodicOrbit.HasSectionInterpolationOn
    (P : N.PositivePeriodicOrbit κ) (basin : Set (Concentration S)) : Prop :=
  ∀ x ∈ basin, ∀ γ : ℝ → Concentration S,
    γ 0 = x →
    (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
    Nonempty (SectionHitInterpolationData P.toPeriodicTrajectory γ)

/-- If every exact forward solution in a basin admits the section-hit interpolation certificate,
then the positive periodic orbit attracts every such solution.  This closes the continuous-time
step once the return-map analysis has supplied those certificates. -/
theorem PositivePeriodicOrbit.globallyAttractsSolutions_of_sectionInterpolation
    (P : N.PositivePeriodicOrbit κ) {basin : Set (Concentration S)}
    (hinterp : P.HasSectionInterpolationOn basin) :
    P.GloballyAttractsSolutions basin := by
  intro x hx γ hγ0 hsol ε hε
  obtain ⟨D⟩ := hinterp x hx γ hγ0 hsol
  -- The interpolation certificate uses forward return times, so its constructed threshold can be
  -- replaced by the nonnegative first hit time used in the proof.  Re-run that proof explicitly
  -- to retain the nonnegativity witness required by the CRN attraction API.
  obtain ⟨δ, hδ, hshadow⟩ := D.shadow ε hε
  obtain ⟨M, hM⟩ := D.hit_converges δ hδ
  refine ⟨D.hitTime M, D.hitTime_nonneg M, ?_⟩
  intro t ht
  obtain ⟨n, hn, s, hs0, hsmax, _htime, hseg⟩ := D.tailCover M t ht
  have hnear : dist (D.hitState n) (P.orbit 0) < δ := hM n hn
  refine ⟨s, ?_⟩
  rw [hseg]
  exact hshadow (D.hitState n) hnear s hs0 hsmax

end Network

end CRNT
