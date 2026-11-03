import CRNT.Oscillation.PlanarSectionHitIsolation
import CRNT.Oscillation.PlanarJordanSeparation

/-!
# Jordan loops from adjacent transversal returns

Given two consecutive intersections of one trajectory with the same canonical transversal, close the
orbit arc by the straight section segment.  If the two section points coincide then the autonomous
trajectory is periodic.  Otherwise:

* the orbit arc cannot self-intersect, because a self-intersection would create a smaller period and
  hence an intermediate section hit;
* the open orbit arc cannot intersect the closing section segment, because any such intersection is
  another section hit between the adjacent times;
* the section segment itself is injective because its scalar endpoints are distinct.

Thus the closed arc is a simple planar loop, exactly the Jordan curve used in the standard
Poincare--Bendixson return-ordering proof.
-/

namespace CRNT
namespace Planar

variable {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}

namespace AdjacentSectionHits

/-- Duration of an adjacent return arc. -/
def duration (A : AdjacentSectionHits D q) : ℝ := A.second.time - A.first.time

@[simp] theorem duration_pos (A : AdjacentSectionHits D q) : 0 < A.duration :=
  sub_pos.mpr A.ordered

/-- Time along the orbit arc for a normalized parameter `s in [0,1/2]`. -/
def orbitTime (A : AdjacentSectionHits D q) (s : ℝ) : ℝ :=
  A.first.time + (2*s) * A.duration

/-- Scalar coordinate along the straight closing section segment for `s in [1/2,1]`. -/
def segmentScalar (A : AdjacentSectionHits D q) (s : ℝ) : ℝ :=
  A.second.scalar + (2*s - 1) * (A.first.scalar - A.second.scalar)

/-- Closed orbit-arc/section-segment parameterization. -/
noncomputable def loopCurve (A : AdjacentSectionHits D q) (s : ℝ) : Phase2 :=
  if s < (1/2 : ℝ) then
    D.trajectory q (A.orbitTime s)
  else
    canonicalSectionPoint field q (A.segmentScalar s)

@[simp] theorem loopCurve_zero (A : AdjacentSectionHits D q) :
    A.loopCurve 0 = canonicalSectionPoint field q A.first.scalar := by
  simp [loopCurve, orbitTime, A.first.hit]

@[simp] theorem loopCurve_half (A : AdjacentSectionHits D q) :
    A.loopCurve (1/2 : ℝ) = canonicalSectionPoint field q A.second.scalar := by
  rw [loopCurve, if_neg (by norm_num : ¬ (1/2 : ℝ) < 1/2)]
  simp [segmentScalar]

@[simp] theorem loopCurve_one (A : AdjacentSectionHits D q) :
    A.loopCurve 1 = canonicalSectionPoint field q A.first.scalar := by
  rw [loopCurve, if_neg (by norm_num : ¬ (1 : ℝ) < 1/2)]
  congr 1
  unfold segmentScalar
  ring

/-- The closed curve is continuous on its fundamental interval. -/
theorem loopCurve_continuousOn (A : AdjacentSectionHits D q) :
    ContinuousOn A.loopCurve (Set.Icc (0 : ℝ) 1) := by
  let dom : Set ℝ := Set.Icc (0 : ℝ) 1
  let branch : Set ℝ := Set.Iio (1/2 : ℝ)
  let f : ℝ → Phase2 := fun s => D.trajectory q (A.orbitTime s)
  let g : ℝ → Phase2 := fun s => canonicalSectionPoint field q (A.segmentScalar s)
  have htraj : Continuous (D.trajectory q) :=
    continuous_iff_continuousAt.mpr fun t => (D.trajectory_solution q t).continuousAt
  have htime : Continuous A.orbitTime := by
    fun_prop [orbitTime, duration]
  have hf : Continuous f := htraj.comp htime
  have hg : Continuous g := by
    fun_prop [canonicalSectionPoint, segmentScalar]
  have hglue : Set.EqOn f g (dom ∩ frontier branch) := by
    intro s hs
    have hfront : s = (1/2 : ℝ) := by
      have h := frontier_lt_subset_eq continuous_id continuous_const hs.2
      simpa [branch] using h
    subst s
    change D.trajectory q (A.orbitTime (1/2 : ℝ)) =
      canonicalSectionPoint field q (A.segmentScalar (1/2 : ℝ))
    have htime' : A.orbitTime (1/2 : ℝ) = A.second.time := by
      unfold orbitTime duration
      ring
    rw [htime', A.second.hit]
    simp [segmentScalar]
  have hpw : ContinuousOn (branch.piecewise f g) (branch.ite dom dom) :=
    continuousOn_piecewise_ite hf.continuousOn hg.continuousOn rfl hglue
  have hdom : branch.ite dom dom = dom := by
    ext s
    simp [Set.ite]
  rw [hdom] at hpw
  change ContinuousOn (fun s => if s < (1/2 : ℝ) then
    D.trajectory q (A.orbitTime s) else
    canonicalSectionPoint field q (A.segmentScalar s)) dom
  exact hpw

/-- An equal scalar at adjacent return times is an actual periodic return to the same state. -/
theorem periodicTrajectory_of_equal_scalars
    (A : AdjacentSectionHits D q)
    (hsmooth : ContDiff ℝ 1 field)
    (hnefield : field q ≠ 0)
    (heq : A.first.scalar = A.second.scalar) :
    Nonempty (PeriodicTrajectory field) := by
  have hhit : D.trajectory q A.first.time = D.trajectory q A.second.time := by
    rw [A.first.hit, A.second.hit, heq]
  have hperiodic := D.period_of_selfIntersection hsmooth A.ordered hhit
  let γ : ℝ → Phase2 := fun t => D.trajectory q (t + A.first.time)
  refine ⟨{
    orbit := γ
    period := A.duration
    period_pos := A.duration_pos
    solution := exactSolution_timeShift (D.trajectory_solution q) A.first.time
    periodic := by
      intro t
      dsimp [γ, duration]
      have hp := hperiodic (t + A.first.time)
      convert hp using 1 <;> ring_nf
    nonconstant := ?_ }⟩
  by_contra hnonconstant
  push_neg at hnonconstant
  have hconstFun : γ = fun _ : ℝ => γ 0 := by
    funext t
    exact hnonconstant t
  have hzero : field (canonicalSectionPoint field q A.first.scalar) = 0 := by
    have hder := exactSolution_timeShift (D.trajectory_solution q) A.first.time 0
    have hconstDeriv : HasDerivAt γ 0 0 := by
      rw [hconstFun]
      exact hasDerivAt_const _ _
    have hz := hder.unique hconstDeriv
    simpa [γ, A.first.hit] using hz
  have hq : q = canonicalSectionPoint field q A.first.scalar := by
    have hback := hnonconstant (-A.first.time)
    have hqγ : q = γ 0 := by
      simpa [γ, D.trajectory_zero] using hback
    calc
      q = γ 0 := hqγ
      _ = canonicalSectionPoint field q A.first.scalar := by
        simpa [γ] using A.first.hit
  exact hnefield (hq ▸ hzero)

/-- The orbit arc between adjacent section hits has no self-intersection except possibly its two
endpoints. -/
theorem orbitArc_injective
    (A : AdjacentSectionHits D q)
    (hsmooth : ContDiff ℝ 1 field)
    {s t : ℝ}
    (hs : s ∈ Set.Ico A.first.time A.second.time)
    (ht : t ∈ Set.Ico A.first.time A.second.time)
    (heq : D.trajectory q s = D.trajectory q t) : s = t := by
  by_contra hne
  have hordered {u v : ℝ} (hu : u ∈ Set.Ico A.first.time A.second.time)
      (hv : v ∈ Set.Ico A.first.time A.second.time) (huv : u < v)
      (heq' : D.trajectory q u = D.trajectory q v) : False := by
    have hp := D.period_of_selfIntersection hsmooth huv heq'
    let r := A.first.time + (v - u)
    have hr1 : A.first.time < r := by dsimp [r]; linarith
    have hr2 : r < A.second.time := by dsimp [r]; linarith [hv.2, hu.1]
    have hreturn : D.trajectory q r = D.trajectory q A.first.time := by
      have h := hp A.first.time
      simpa [r, add_comm, add_left_comm, add_assoc] using h
    have hzero : sectionCrossingFunction D q r = 0 := by
      rw [sectionCrossingFunction_eq_zero_iff, hreturn, A.first.hit]
      exact canonicalSectionPoint_mem field q A.first.scalar
    exact (A.noHitBetween r hr1 hr2 hzero).elim
  rcases lt_or_gt_of_ne hne with hst | hts
  · exact (hordered hs ht hst heq).elim
  · exact (hordered ht hs hts heq.symm).elim

/-- Interior points of the orbit arc do not lie on the canonical section. -/
theorem orbitArc_not_mem_section
    (A : AdjacentSectionHits D q)
    {t : ℝ} (h1 : A.first.time < t) (h2 : t < A.second.time) :
    D.trajectory q t ∉ canonicalSection field q := by
  intro hmem
  exact A.noHitBetween t h1 h2
    ((sectionCrossingFunction_eq_zero_iff D q t).mpr hmem)

/-- If the endpoint section coordinates differ, the orbit arc plus closing section segment is a
simple closed loop. -/
noncomputable def simplePlanarLoop_of_scalars_ne
    (A : AdjacentSectionHits D q)
    (hsmooth : ContDiff ℝ 1 field)
    (hnefield : field q ≠ 0)
    (hscalar : A.first.scalar ≠ A.second.scalar) :
    SimplePlanarLoop := by
  have horbit_range {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s < 1/2) :
      A.orbitTime s ∈ Set.Ico A.first.time A.second.time := by
    constructor
    · unfold orbitTime duration
      have hprod : 0 ≤ (2 * s) * A.duration :=
        mul_nonneg (by positivity) A.duration_pos.le
      unfold duration at hprod
      nlinarith
    · have hscale : 2 * s < 1 := by linarith
      have hprod := mul_lt_mul_of_pos_right hscale A.duration_pos
      unfold duration at hprod
      unfold orbitTime duration
      nlinarith
  have hmixed {s t : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1)
      (ht : t ∈ Set.Ico (0 : ℝ) 1) (hsOrbit : s < 1/2)
      (htSegment : ¬ t < 1/2)
      (heq : A.loopCurve s = A.loopCurve t) : False := by
    have htime := horbit_range hs.1 hsOrbit
    have hsection : canonicalSectionPoint field q (A.segmentScalar t) ∈
        canonicalSection field q := canonicalSectionPoint_mem field q _
    have hcurve : D.trajectory q (A.orbitTime s) =
        canonicalSectionPoint field q (A.segmentScalar t) := by
      simpa only [loopCurve, if_pos hsOrbit, if_neg htSegment] using heq
    have hmem : D.trajectory q (A.orbitTime s) ∈ canonicalSection field q :=
      hcurve ▸ hsection
    by_cases hs0 : s = 0
    · subst s
      have hscalarEq : A.segmentScalar t = A.first.scalar := by
        apply canonicalSectionPoint_injective hnefield
        calc
          canonicalSectionPoint field q (A.segmentScalar t) =
              D.trajectory q (A.orbitTime 0) := hcurve.symm
          _ = canonicalSectionPoint field q A.first.scalar := by
            simp [orbitTime, A.first.hit]
      have hdiff : A.first.scalar - A.second.scalar ≠ 0 := sub_ne_zero.mpr hscalar
      have hprod : (2 * t - 2) * (A.first.scalar - A.second.scalar) = 0 := by
        unfold segmentScalar at hscalarEq
        nlinarith
      rcases mul_eq_zero.mp hprod with htval | hval
      · linarith [ht.2]
      · exact hdiff hval
    · have hspos : 0 < s := lt_of_le_of_ne hs.1 (Ne.symm hs0)
      have hfirst : A.first.time < A.orbitTime s := by
        unfold orbitTime duration
        nlinarith [hspos, A.ordered]
      have hsecond : A.orbitTime s < A.second.time := by
        have hscale : 2 * s < 1 := by linarith
        have hprod := mul_lt_mul_of_pos_right hscale A.duration_pos
        unfold duration at hprod
        unfold orbitTime duration
        nlinarith [hprod]
      exact A.orbitArc_not_mem_section hfirst hsecond hmem
  refine {
    curve := A.loopCurve
    continuous := A.loopCurve_continuousOn
    closes := by simp
    injective_Ico := ?_ }
  intro s hs t ht heq
  by_cases hsOrbit : s < 1/2
  · by_cases htOrbit : t < 1/2
    · have htime := A.orbitArc_injective hsmooth
        (horbit_range hs.1 hsOrbit) (horbit_range ht.1 htOrbit) (by
          simpa only [loopCurve, if_pos hsOrbit, if_pos htOrbit] using heq)
      have hmul : (2 * s - 2 * t) * A.duration = 0 := by
        unfold orbitTime duration at htime
        unfold duration
        nlinarith
      rcases mul_eq_zero.mp hmul with hst | hdur
      · linarith
      · exact (A.duration_pos.ne' hdur).elim
    · exact (hmixed hs ht hsOrbit htOrbit heq).elim
  · by_cases htOrbit : t < 1/2
    · exact (hmixed ht hs htOrbit hsOrbit heq.symm).elim
    · have hparam : A.segmentScalar s = A.segmentScalar t := by
        apply canonicalSectionPoint_injective hnefield
        simpa only [loopCurve, if_neg hsOrbit, if_neg htOrbit] using heq
      have hdiff : A.first.scalar - A.second.scalar ≠ 0 := sub_ne_zero.mpr hscalar
      have hprod : (2 * s - 2 * t) * (A.first.scalar - A.second.scalar) = 0 := by
        unfold segmentScalar at hparam
        nlinarith
      rcases mul_eq_zero.mp hprod with hst | hval
      · linarith
      · exact (hdiff hval).elim

/-- Adjacent returns therefore give the classical dichotomy: periodic orbit immediately, or a
simple Jordan loop built from the orbit arc and section segment. -/
theorem periodic_or_simpleLoop
    (A : AdjacentSectionHits D q)
    (hsmooth : ContDiff ℝ 1 field)
    (hnefield : field q ≠ 0) :
    Nonempty (PeriodicTrajectory field) ∨ Nonempty SimplePlanarLoop := by
  by_cases hscalar : A.first.scalar = A.second.scalar
  · exact Or.inl (A.periodicTrajectory_of_equal_scalars hsmooth hnefield hscalar)
  · exact Or.inr ⟨A.simplePlanarLoop_of_scalars_ne hsmooth hnefield hscalar⟩

end AdjacentSectionHits

end Planar
end CRNT
