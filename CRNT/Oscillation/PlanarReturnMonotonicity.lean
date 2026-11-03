import CRNT.Oscillation.PlanarLocalReturns
import CRNT.Oscillation.PlanarLocalReturnLoops
import CRNT.Oscillation.PlanarJordanSeparation
import CRNT.Oscillation.PlanarNoCrossing

/-!
# The planar return-ordering kernel

All analytic ingredients of the Poincare--Bendixson proof are now internal: recurrence, exact local
section hits, a positive-speed section window, isolation/discreteness of local hits and first/next
return construction.  The sole planar-topology statement is the classical Jordan ordering lemma.

Starting at scalar `0`, let `H₁` be the first return to a sufficiently small oriented local
transversal.  If the orbit is not periodic, then every later return to that local transversal lies
strictly farther from `0` in the direction of `H₁`.  Jordan's theorem proves this by closing each
successive orbit arc with the straight section segment and using no-crossing plus the fact that all
transversal crossings have the same orientation.

Once this statement is available, recurrence contradicts it immediately: recurrence gives later
returns with arbitrarily small scalar coordinate.  Thus the first return has scalar `0` and the
recurrent point lies on a periodic orbit.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace

namespace Planar

/-- Scalar ordering away from the initial section coordinate `0`. -/
def ReturnFartherFromBase (u₁ u₂ : ℝ) : Prop :=
  (0 < u₁ ∧ u₁ < u₂) ∨ (u₁ < 0 ∧ u₂ < u₁)

/-- **Jordan return-ordering theorem.**

This is the exact universal planar topology kernel after all flow-box and ODE uniqueness work has
been removed.  It is independent of CRNs.  The hypotheses say that `H₁` is the first local return,
all crossings in the scalar window have the same positive normal orientation, and the ambient flow
has no periodic trajectory.  The conclusion orders *every* later local return away from the base.
-/
def JordanLocalReturnOrderingTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D) (q : Phase2) (rho : ℝ),
    q ∈ M.carrier → 0 < rho → ContDiff ℝ 1 field →
    (∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ) →
    ¬ HasPeriodicTrajectoryThrough field q →
    ∀ H₁ : FirstLocalReturn D q rho,
      ∀ H₂ : LocalCanonicalReturn D q rho,
        H₁.time < H₂.time → ReturnFartherFromBase H₁.scalar H₂.scalar

/-- The local oriented-crossing corollary of Jordan separation.

This is deliberately a *pure planar-topology* statement: all recurrence, first-return existence,
flow regularity and no-self-intersection facts are explicit inputs.  A proof is obtained by taking
the Jordan loop formed by the first orbit arc plus its closing section segment, observing which
complement component is entered at the endpoint, and using equal crossing orientation to show that
a later local section hit cannot occur on the base side of that endpoint. -/
def OrientedJordanSectionOrderingTarget : Prop :=
  SimplePlanarLoop.JordanSeparationTarget →
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D) (q : Phase2) (rho : ℝ),
    q ∈ M.carrier → 0 < rho → ContDiff ℝ 1 field →
    (∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ) →
    (¬ HasPeriodicTrajectoryThrough field q) →
    ∀ H1 : FirstLocalReturn D q rho,
      ∀ H2 : LocalCanonicalReturn D q rho,
        H1.time < H2.time → ReturnFartherFromBase H1.scalar H2.scalar

/-- Jordan separation/no-crossing formulation of the same kernel.  Keeping this theorem here makes
clear that the ordering kernel has no extra dynamical content beyond planar separation: a future
orbit arc cannot change complement component except by crossing the Jordan boundary, and equal
crossing orientation forbids re-entering the closing section segment in the reverse chronological
order. -/
theorem jordanLocalReturnOrdering_of_separation
    (hJordan : SimplePlanarLoop.JordanSeparationTarget)
    (hCrossing : OrientedJordanSectionOrderingTarget) :
    JordanLocalReturnOrderingTarget := by
  intro field D M q rho hq hrho hsmooth horient haper H₁ H₂ htime
  exact hCrossing hJordan field D M q rho hq hrho hsmooth horient haper H₁ H₂ htime

/-- A return to scalar zero is an exact return to `q` and therefore closes a periodic trajectory. -/
theorem periodic_of_localReturn_scalar_zero
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    {q : Phase2} {rho : ℝ}
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    (H : LocalCanonicalReturn D q rho)
    (hzero : H.scalar = 0) :
    HasPeriodicTrajectoryThrough field q := by
  have hreturn : D.trajectory q H.time = q := by
    simpa [hzero, canonicalSectionPoint_zero] using H.hit
  have hhit : D.trajectory q 0 = D.trajectory q H.time := by
    rw [D.trajectory_zero, hreturn]
  exact D.periodicTrajectory_of_selfIntersection hsmooth H.time_pos hhit hne

/-- The ordering theorem plus recurrence forces a periodic orbit through every point of an
 equilibrium-free minimal omega set. -/
theorem minimalPoint_periodic_of_returnOrdering
    (horder : JordanLocalReturnOrderingTarget)
    (hflow : CanonicalFlowRegularityTarget)
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    (M : MinimalOmegaData D) {q : Phase2} (hq : q ∈ M.carrier)
    (hsmooth : ContDiff ℝ 1 field) :
    HasPeriodicTrajectoryThrough field q := by
  by_contra haper
  have hne := M.equilibriumFree q hq
  obtain ⟨R⟩ := hflow field D q hsmooth
  obtain ⟨rho, hrho, horient⟩ := exists_positiveSpeedWindow hsmooth.continuous hne
  obtain ⟨H₁⟩ := exists_firstLocalReturn (D := D) (M := M) (q := q)
    M hq R hsmooth hrho
  by_cases hzero : H₁.scalar = 0
  · exact haper (periodic_of_localReturn_scalar_zero hsmooth hne H₁.toLocalCanonicalReturn hzero)
  · have hfar : ∀ H₂ : LocalCanonicalReturn D q rho,
        H₁.time < H₂.time → ReturnFartherFromBase H₁.scalar H₂.scalar :=
      horder field D M q rho hq hrho hsmooth horient haper H₁
    -- Recurrence provides a later local return whose absolute scalar is strictly smaller than that
    -- of the first return, contradicting either branch of `ReturnFartherFromBase`.
    let eps := |H₁.scalar| / 2
    have heps : 0 < eps := by
      dsimp [eps]
      exact half_pos (abs_pos.mpr hzero)
    let epsWindow := min eps rho
    have hepsWindow : 0 < epsWindow := by
      dsimp [epsWindow]
      exact lt_min heps hrho
    obtain ⟨K, hKlate, hKsmall⟩ :=
      R.exists_late_canonicalSectionHit_smallScalar M hq hsmooth
        (eps := epsWindow) hepsWindow (H₁.time + 1)
    let H₂ : LocalCanonicalReturn D q rho := {
      toCanonicalSectionHit := K
      scalar_mem := by
        have hkabs : |K.scalar| < rho :=
          lt_of_lt_of_le hKsmall (min_le_right eps rho)
        exact ⟨by linarith [abs_lt.mp hkabs], by linarith [abs_lt.mp hkabs]⟩ }
    have htime : H₁.time < H₂.time := by
      dsimp [H₂]
      linarith
    have horder12 := hfar H₂ htime
    have hsmall : |H₂.scalar| < |H₁.scalar| := by
      have hhalf : eps ≤ |H₁.scalar| := by
        dsimp [eps]
        nlinarith [abs_nonneg H₁.scalar]
      have hkabs : |K.scalar| < |H₁.scalar| :=
        lt_of_lt_of_le hKsmall (le_trans (min_le_left eps rho) hhalf)
      simpa [H₂] using hkabs
    rcases horder12 with hpos | hneg
    · have hu2pos : 0 < H₂.scalar := lt_trans hpos.1 hpos.2
      rw [abs_of_pos hpos.1, abs_of_pos hu2pos] at hsmall
      linarith
    · have hu2neg : H₂.scalar < 0 := lt_trans hneg.2 hneg.1
      rw [abs_of_neg hneg.1, abs_of_neg hu2neg] at hsmall
      linarith

/-- A periodic trajectory through a point of an invariant minimal set stays in that minimal set. -/
theorem periodicOrbit_subset_minimal
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    (M : MinimalOmegaData D) {q : Phase2} (hq : q ∈ M.carrier)
    (P : PeriodicTrajectory field)
    (horigin : P.orbit 0 = q)
    (hflow : ∀ t : ℝ, P.orbit t = D.trajectory q t) :
    P.orbitSet ⊆ M.carrier := by
  rintro x ⟨t, rfl⟩
  have hshiftN : ∀ n : ℕ, P.orbit (t + (n : ℝ) * P.period) = P.orbit t := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have htimeEq : t + (↑(n + 1) : ℝ) * P.period =
          (t + (n : ℝ) * P.period) + P.period := by
        push_cast
        ring
      calc
        P.orbit (t + (↑(n + 1) : ℝ) * P.period) =
        P.orbit ((t + (n : ℝ) * P.period) + P.period) := by rw [htimeEq]
        _ = P.orbit (t + (n : ℝ) * P.period) := P.periodic _
        _ = P.orbit t := ih
  obtain ⟨n, hn⟩ := exists_nat_gt (-t / P.period)
  have hmul : -t < (n : ℝ) * P.period := (div_lt_iff₀ P.period_pos).mp hn
  have htime : 0 ≤ t + (n : ℝ) * P.period := by linarith
  have hshift := hshiftN n
  have hforward := M.invariant ⟨t + (n : ℝ) * P.period, htime⟩ hq
  rw [D.flow_eq_trajectory q ⟨t + (n : ℝ) * P.period, htime⟩] at hforward
  have hshiftMem : P.orbit (t + (n : ℝ) * P.period) ∈ M.carrier := by
    rw [hflow]
    exact hforward
  rw [hshift] at hshiftMem
  exact hshiftMem

/-- Direct minimal-set Poincare--Bendixson endpoint: a minimal equilibrium-free omega subset contains
an exact periodic orbit. -/
def MinimalPeriodicOrbitTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D), ContDiff ℝ 1 field →
    ∃ P : PeriodicTrajectory field, P.orbitSet ⊆ M.carrier

/-- Flow-box regularity + Jordan return ordering prove the minimal periodic-orbit theorem directly. -/
theorem minimalPeriodicOrbit_of_ordering
    (horder : JordanLocalReturnOrderingTarget)
    (hflow : CanonicalFlowRegularityTarget) :
    MinimalPeriodicOrbitTarget := by
  intro field D M hsmooth
  obtain ⟨q, hq⟩ := M.nonempty
  obtain ⟨P, hP0⟩ := minimalPoint_periodic_of_returnOrdering horder hflow M hq hsmooth
  have huniq := globalSolutionUnique_of_locallyLipschitz hsmooth.locallyLipschitz
  have hinitial : P.orbit 0 = D.trajectory q 0 := by
    rw [hP0, D.trajectory_zero]
  have htrajectory : P.orbit = D.trajectory q :=
    huniq P.orbit (D.trajectory q) P.solution (D.trajectory_solution q) hinitial
  exact ⟨P, periodicOrbit_subset_minimal M hq P hP0 (fun t => congrFun htrajectory t)⟩

/-- The direct minimal-periodic theorem proves the public omega-limit Poincare--Bendixson
classification without constructing an artificial return interval contained in the minimal set. -/
theorem poincareBendixsonOmegaClassification_of_minimalPeriodic
    (hmin : MinimalPeriodicOrbitTarget) :
    PoincareBendixsonOmegaClassificationTarget := by
  intro field D hsmooth
  obtain ⟨M⟩ := D.exists_minimalOmegaData
  obtain ⟨P, hPM⟩ := hmin field D M hsmooth
  exact ⟨P, fun x hx => M.subset_omega (hPM hx)⟩

end Planar
end CRNT
