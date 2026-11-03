import CRNT.Oscillation.SimpleCycle
import CRNT.Oscillation.PlanarLateSectionReturn

/-!
# Shared Jordan-separation kernel for planar oscillation theory

Both classical planar arguments in the oscillation layer use the same topology:

* Poincare--Bendixson closes an orbit segment by a transversal segment and uses separation/no
  crossing to order future returns;
* Bendixson--Dulac takes the simple periodic orbit itself as the Jordan boundary and integrates over
  its bounded component.

This file factors that common topology once.  The ODE-specific work needed to prove simplicity is
already in `SimpleCycle`; the remaining universal statement is the Jordan separation theorem for a
simple closed curve in `R²`.
-/

namespace CRNT
namespace Planar

open Set

/-- A parameterized simple closed planar loop on `[0,1]`. -/
structure SimplePlanarLoop : Type where
  curve : ℝ → Phase2
  continuous : ContinuousOn curve (Set.Icc (0 : ℝ) 1)
  closes : curve 0 = curve 1
  injective_Ico : Set.InjOn curve (Set.Ico (0 : ℝ) 1)

namespace SimplePlanarLoop

/-- Geometric trace of a simple loop. -/
def trace (L : SimplePlanarLoop) : Set Phase2 := L.curve '' Set.Icc (0 : ℝ) 1

/-- Jordan separation data: the trace divides the plane into one bounded interior and one
unbounded exterior, with the trace as their common frontier. -/
structure Separation (L : SimplePlanarLoop) where
  interior : Set Phase2
  exterior : Set Phase2
  interior_open : IsOpen interior
  exterior_open : IsOpen exterior
  interior_nonempty : interior.Nonempty
  exterior_nonempty : exterior.Nonempty
  interior_connected : IsConnected interior
  exterior_connected : IsConnected exterior
  interior_bounded : Bornology.IsBounded interior
  exterior_unbounded : ¬ Bornology.IsBounded exterior
  disjoint_interior_trace : Disjoint interior L.trace
  disjoint_exterior_trace : Disjoint exterior L.trace
  disjoint_components : Disjoint interior exterior
  cover : interior ∪ L.trace ∪ exterior = Set.univ
  frontier_interior : frontier interior = L.trace
  frontier_exterior : frontier exterior = L.trace
  /-- The bounded component lies in the convex hull of its Jordan boundary. -/
  interior_subset_convexHull : interior ⊆ convexHull ℝ L.trace

/-- Universal Jordan-curve theorem in the exact representation used by this repository. -/
def JordanSeparationTarget : Prop :=
  ∀ L : SimplePlanarLoop, Nonempty L.Separation

end SimplePlanarLoop

/-- If a nonempty open set is carved out of an open preconnected set by its own frontier, and
that set meets the frontier nowhere, the two coincide.

`A = V ⊔ (A \ closure V)` is a partition of `A` into two open pieces, because a point of `A`
in `closure V \ V` would lie on `frontier V`.  Preconnectedness then kills the second piece. -/
theorem eq_of_open_preconnected_frontier_disjoint
    {A V : Set Phase2} (hA : IsPreconnected A) (hAo : IsOpen A)
    (hVo : IsOpen V) (hVne : V.Nonempty) (hVA : V ⊆ A)
    (hdisj : Disjoint A (frontier V)) : A = V := by
  have hcover : A ⊆ V ∪ (A \ closure V) := by
    intro x hxA
    by_cases hxc : x ∈ closure V
    · by_cases hxV : x ∈ V
      · exact Or.inl hxV
      · have hxf : x ∈ frontier V := by
          rw [hVo.frontier_eq]
          exact Set.mem_sdiff_of_mem hxc hxV
        exact absurd hxf (Set.disjoint_left.1 hdisj hxA)
    · exact Or.inr ⟨hxA, hxc⟩
  have hdisj2 : Disjoint V (A \ closure V) := by
    rw [Set.disjoint_left]
    intro x hxV hx
    exact hx.2 (subset_closure hxV)
  obtain ⟨v, hv⟩ := hVne
  have hsub : A ⊆ V :=
    hA.subset_left_of_subset_union hVo (hAo.sdiff isClosed_closure) hdisj2 hcover
      ⟨v, hVA hv, hv⟩
  exact le_antisymm hsub hVA

/-- **Uniqueness half of Jordan separation.**  A bounded nonempty open connected set whose
frontier is exactly the loop trace *is* the bounded Jordan component.

This is what lets two independently produced Jordan interiors of the same simple closed curve
be identified.  Boundedness is essential and is what rules out the exterior component: without
it the exterior satisfies every other clause. -/
theorem SimplePlanarLoop.Separation.eq_interior_of_frontier_eq_trace
    {L : SimplePlanarLoop} (S : L.Separation)
    {V : Set Phase2} (hVo : IsOpen V) (hVconn : IsConnected V)
    (hVbdd : Bornology.IsBounded V) (hVfront : frontier V = L.trace) :
    V = S.interior := by
  have hVtrace : Disjoint V L.trace := by
    rw [← hVfront, Set.disjoint_right]
    intro x hx
    rw [hVo.frontier_eq] at hx
    exact hx.2
  have hVsub : V ⊆ S.interior ∪ S.exterior := by
    intro x hxV
    have hx : x ∈ S.interior ∪ L.trace ∪ S.exterior := by
      rw [S.cover]; exact Set.mem_univ x
    rcases hx with (h | h) | h
    · exact Or.inl h
    · exact absurd h (Set.disjoint_left.1 hVtrace hxV)
    · exact Or.inr h
  by_cases hmeet : (V ∩ S.interior).Nonempty
  · have hint : V ⊆ S.interior :=
      hVconn.isPreconnected.subset_left_of_subset_union
        S.interior_open S.exterior_open S.disjoint_components hVsub hmeet
    exact (eq_of_open_preconnected_frontier_disjoint
      S.interior_connected.isPreconnected S.interior_open hVo hVconn.nonempty hint
      (by rw [hVfront]; exact S.disjoint_interior_trace)).symm
  · rw [Set.not_nonempty_iff_eq_empty] at hmeet
    have hVext : V ⊆ S.exterior := by
      intro x hxV
      rcases hVsub hxV with h | h
      · have hmem : x ∈ V ∩ S.interior := ⟨hxV, h⟩
        rw [hmeet] at hmem
        exact absurd hmem (Set.notMem_empty x)
      · exact h
    have hext : S.exterior = V :=
      eq_of_open_preconnected_frontier_disjoint
        S.exterior_connected.isPreconnected S.exterior_open hVo hVconn.nonempty hVext
        (by rw [hVfront]; exact S.disjoint_exterior_trace)
    exact absurd (hext ▸ hVbdd) S.exterior_unbounded

/-- Normalize one least-period traversal to `[0,1]`. -/
noncomputable def PeriodicTrajectory.normalizedLoop
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field) : ℝ → Phase2 :=
  fun s => P.orbit (s * P.period)

/-- A simple closed periodic orbit gives the repository's generic `SimplePlanarLoop`. -/
noncomputable def PeriodicTrajectory.toSimplePlanarLoop
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field)
    (C : P.SimpleClosedCycle) : SimplePlanarLoop where
  curve := P.normalizedLoop
  continuous := by
    have hcont : Continuous P.orbit := P.continuous_orbit
    exact (hcont.comp (continuous_id.mul continuous_const)).continuousOn
  closes := by
    -- `normalizedLoop` is a plain `def`; `simp` will not unfold it here, but `show`
    -- goes through by defeq.
    show P.orbit (0 * P.period) = P.orbit (1 * P.period)
    simpa using (P.periodic 0).symm
  injective_Ico := by
    intro s hs t ht heq
    have hsT : s * P.period ∈ Set.Ico (0 : ℝ) P.period := by
      constructor
      · exact mul_nonneg hs.1 P.period_pos.le
      -- was `ht.2`: wrong hypothesis, this bound is about `s`
      · nlinarith [hs.2, P.period_pos]
    have htT : t * P.period ∈ Set.Ico (0 : ℝ) P.period := by
      constructor
      · exact mul_nonneg ht.1 P.period_pos.le
      · nlinarith [ht.2, P.period_pos]
    have hst := C.injOn_Ico hsT htT heq
    nlinarith [P.period_pos]

/-- The normalized loop has exactly the same geometric trace as the periodic orbit. -/
theorem PeriodicTrajectory.normalizedLoop_trace_eq_orbitSet
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field) :
    (P.normalizedLoop '' Set.Icc (0 : ℝ) 1) = P.orbitSet := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact ⟨s * P.period, rfl⟩
  · rintro ⟨t, rfl⟩
    let r : ℝ := t - P.period * Int.floor (t / P.period)
    have hfr : r = P.period * Int.fract (t / P.period) := by
      have hne : P.period ≠ 0 := P.period_pos.ne'
      simp only [r, Int.fract]
      field_simp
    have hr0 : 0 ≤ r := by
      rw [hfr]; exact mul_nonneg P.period_pos.le (Int.fract_nonneg _)
    have hrT : r < P.period := by
      rw [hfr]
      calc P.period * Int.fract (t / P.period) < P.period * 1 :=
            mul_lt_mul_of_pos_left (Int.fract_lt_one _) P.period_pos
        _ = P.period := mul_one _
    let s : ℝ := r / P.period
    have hs : s ∈ Set.Icc (0 : ℝ) 1 := by
      -- `positivity` cannot do the upper bound `s ≤ 1`
      constructor
      · exact div_nonneg hr0 P.period_pos.le
      · rw [div_le_one P.period_pos]; exact hrT.le
    refine ⟨s, hs, ?_⟩
    have hper := P.periodic
    show P.orbit (s * P.period) = P.orbit t
    -- `Periodic.sub_zsmul_eq` uses `n • period` (zsmul), not `(↑n) * period`
    have hsr : s * P.period = t - (Int.floor (t / P.period)) • P.period := by
      have hne : P.period ≠ 0 := P.period_pos.ne'
      dsimp [s, r]
      rw [zsmul_eq_mul]
      field_simp
    rw [hsr]
    exact hper.sub_zsmul_eq _

/-- The generic loop built from a periodic orbit has the orbit set as its trace. -/
@[simp] theorem PeriodicTrajectory.toSimplePlanarLoop_trace
    {field : Phase2 → Phase2} (P : PeriodicTrajectory field) (C : P.SimpleClosedCycle) :
    (PeriodicTrajectory.toSimplePlanarLoop P C).trace = P.orbitSet :=
  PeriodicTrajectory.normalizedLoop_trace_eq_orbitSet P

/-- Jordan separation specialized to simple periodic trajectories. -/
def PeriodicJordanSeparationTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (P : PeriodicTrajectory field)
    (C : P.SimpleClosedCycle),
    Nonempty ((PeriodicTrajectory.toSimplePlanarLoop P C).Separation)

/-- Generic Jordan separation immediately gives the periodic specialization. -/
theorem periodicJordanSeparation_of_jordan
    (hJordan : SimplePlanarLoop.JordanSeparationTarget) :
    PeriodicJordanSeparationTarget := by
  intro field P C
  exact hJordan (PeriodicTrajectory.toSimplePlanarLoop P C)

end Planar
end CRNT
