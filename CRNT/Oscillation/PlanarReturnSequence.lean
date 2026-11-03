import CRNT.Oscillation.PlanarLateSectionReturn

/-!
# Canonical sequences of late transversal returns

The local flow-box theorem upgrades recurrence to genuine section intersections.  This module turns
that existential statement into a concrete increasing sequence whose section coordinates converge
to zero.  This is the exact sequence used by the classical Poincare--Bendixson ordering argument.
-/

namespace CRNT

open Filter Topology
open scoped NNReal

namespace Planar

/-- An increasing sequence of canonical-section hits converging to the recurrent base point in the
explicit scalar section coordinate. -/
structure CanonicalReturnSequence {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) : Type where
  hit : ℕ → CanonicalSectionHit D q
  time_strictMono : StrictMono (fun n => (hit n).time)
  scalar_tendsto_zero : Tendsto (fun n => (hit n).scalar) Filter.atTop (𝓝 0)

namespace CanonicalReturnSequence

variable {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}

/-- If one return scalar is zero, the recurrent trajectory closes and gives a genuine periodic
trajectory.

The hypothesis `field q ≠ 0` is **necessary**, not a convenience: `CanonicalSectionHit` records
only `time_pos` and the hit equation, so for `field = 0` the constant trajectory at an
equilibrium supplies a scalar-zero hit at every positive time while `PeriodicTrajectory`
demands `nonconstant`.  Without it the statement is false.  Every intended call site has the
hypothesis for free from `FlowTrappingData.equilibriumFree`. -/
theorem periodicTrajectory_of_scalar_eq_zero
    (R : CanonicalReturnSequence D q) {n : ℕ}
    (hzero : (R.hit n).scalar = 0)
    (hne : field q ≠ 0)
    (hsmooth : ContDiff ℝ 1 field) :
    Nonempty (PeriodicTrajectory field) := by
  have hreturn : D.trajectory q (R.hit n).time = q := by
    simpa [hzero, canonicalSectionPoint_zero] using (R.hit n).hit
  have hperiodic : Function.Periodic (D.trajectory q) (R.hit n).time := by
    have huniq : GlobalSolutionUnique field :=
      globalSolutionUnique_of_locallyLipschitz hsmooth.locallyLipschitz
    intro t
    have hshift := exactSolutions_eq_shift_of_hit huniq
      (D.trajectory_solution q) (D.trajectory_solution q)
      (t₁ := (R.hit n).time) (t₂ := 0) (by simpa [D.trajectory_zero] using hreturn)
    have := congrFun hshift t
    simpa [add_comm, add_left_comm, add_assoc] using this
  refine ⟨{
    orbit := D.trajectory q
    period := (R.hit n).time
    period_pos := (R.hit n).time_pos
    solution := D.trajectory_solution q
    periodic := hperiodic
    nonconstant := ?_ }⟩
  -- `nonconstant` is `∃ t, D.trajectory q t ≠ D.trajectory q 0`, so it has to be opened by
  -- contradiction rather than by `intro`.  A constant orbit is an equilibrium orbit, which
  -- `hne` excludes.
  by_contra hconst
  push_neg at hconst
  have hconstq : D.trajectory q = fun _ => q := by
    funext t
    rw [hconst t, D.trajectory_zero]
  refine hne ?_
  have hder := D.trajectory_solution q 0
  rw [hconstq] at hder
  exact hder.unique (hasDerivAt_const (0 : ℝ) q)

/-- Convergence of section scalars gives eventual membership in every symmetric section interval. -/
theorem eventually_scalar_abs_lt (R : CanonicalReturnSequence D q)
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n in Filter.atTop, |(R.hit n).scalar| < eps := by
  have hnhds : {x : ℝ | |x| < eps} ∈ 𝓝 (0 : ℝ) :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by simpa using heps)
  exact R.scalar_tendsto_zero.eventually hnhds

end CanonicalReturnSequence

namespace CanonicalFlowBoxRegularity

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {M : MinimalOmegaData D} {q : Phase2}

/-- Noncomputably choose an increasing return sequence with `|u_n| < 1/(n+1)`.

The recursion asks for the next hit after the previous time plus one, so times are strictly
increasing.  The scalar estimate makes convergence to zero immediate. -/
noncomputable def canonicalReturnSequence
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field) : CanonicalReturnSequence D q := by
  classical
  let eps : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have heps : ∀ n, 0 < eps n := by
    intro n; dsimp [eps]; positivity
  let H : ℕ → CanonicalSectionHit D q := fun n =>
    Nat.rec
      (Classical.choose (R.exists_late_canonicalSectionHit_smallScalar
        M hq hsmooth (heps 0) 0))
      (fun n prev =>
        Classical.choose (R.exists_late_canonicalSectionHit_smallScalar
          M hq hsmooth (heps (n+1)) (prev.time + 1))) n
  have hstep : ∀ n, (H n).time + 1 < (H (n+1)).time := by
    intro n
    simpa [H] using
      (Classical.choose_spec (R.exists_late_canonicalSectionHit_smallScalar
        M hq hsmooth (heps (n+1)) ((H n).time + 1))).1
  have hsmall : ∀ n, |(H n).scalar| < eps n := by
    intro n
    cases n with
    | zero =>
        simpa [H] using
          (Classical.choose_spec (R.exists_late_canonicalSectionHit_smallScalar
            M hq hsmooth (heps 0) 0)).2
    | succ n =>
        simpa [H] using
          (Classical.choose_spec (R.exists_late_canonicalSectionHit_smallScalar
            M hq hsmooth (heps (n+1)) ((H n).time + 1))).2
  refine {
    hit := H
    time_strictMono := strictMono_nat_of_lt_succ (fun n => by linarith [hstep n])
    scalar_tendsto_zero := ?_ }
  -- The bound is on `|scalar|`, not on `scalar`, so `squeeze_zero'` does not apply to the
  -- goal directly.  Squeeze the absolute value first, then transfer.
  have heps0 : Tendsto eps Filter.atTop (𝓝 0) := by
    -- `tendsto_one_div_add_atTop_nhds_zero_nat` is now generic over a `DivisionSemiring 𝕜`
    -- with `[ContinuousSMul ℚ≥0 𝕜]`; `simpa … using` leaves `𝕜` a metavariable and the
    -- instance search gets stuck, so pin `𝕜 := ℝ` explicitly.
    simpa [eps] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have habs : Tendsto (fun n => |(H n).scalar|) Filter.atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun n => abs_nonneg _)
      (Filter.Eventually.of_forall fun n => (hsmall n).le) heps0
  exact (tendsto_zero_iff_abs_tendsto_zero _).mpr habs

end CanonicalFlowBoxRegularity

/-- Every equilibrium-free recurrent minimal-set point with canonical flow-box regularity therefore
carries a concrete sequence of exact transversal returns converging to the base coordinate. -/
theorem exists_canonicalReturnSequence
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    (M : MinimalOmegaData D) {q : Phase2} (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field) :
    Nonempty (CanonicalReturnSequence D q) :=
  ⟨R.canonicalReturnSequence M hq hsmooth⟩

end Planar
end CRNT
