import CRNT.Oscillation.PlanarLocalReturns
import CRNT.Oscillation.PlanarJordanSeparation
import CRNT.Oscillation.PlanarNoCrossing

/-!
# Simple Jordan loops from consecutive local returns

For the local Poincare section, consecutive return times have no intervening intersection with the
closed scalar window.  Closing the intervening orbit arc by the straight transversal segment
therefore gives a simple Jordan loop unless the trajectory was periodic already.
-/

namespace CRNT
namespace Planar

open Set

/-- Periodicity of the recurrent orbit through a specified base point. -/
def HasPeriodicTrajectoryThrough (field : Phase2 → Phase2) (q : Phase2) : Prop :=
  ∃ P : PeriodicTrajectory field, P.orbit 0 = q

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {q : Phase2} {rho : ℝ}

/-- A non-equilibrium trajectory that meets itself at distinct ordered times yields a periodic
trajectory with that time difference as period. -/
theorem FlowTrappingData.periodicTrajectory_of_selfIntersection
    (D : FlowTrappingData field) (hsmooth : ContDiff ℝ 1 field)
    {q : Phase2} {s t : ℝ} (hst : s < t)
    (hhit : D.trajectory q s = D.trajectory q t) (hne : field q ≠ 0) :
    HasPeriodicTrajectoryThrough field q := by
  let P : PeriodicTrajectory field := {
    orbit := D.trajectory q
    period := t - s
    period_pos := sub_pos.mpr hst
    solution := D.trajectory_solution q
    periodic := D.period_of_selfIntersection hsmooth hst hhit
    nonconstant := by
      by_contra hconst
      push_neg at hconst
      have hconstfun : D.trajectory q = fun _ => q := by
        funext u
        rw [hconst u, D.trajectory_zero]
      have hder := D.trajectory_solution q 0
      rw [hconstfun] at hder
      have hzero := hder.unique (hasDerivAt_const (0 : ℝ) q)
      exact hne (by simpa using hzero) }
  exact ⟨P, by simp [P, D.trajectory_zero]⟩

/-- Unified representation of a return endpoint, allowing the initial crossing at `(time,scalar)=(0,0)`. -/
structure LocalCrossing (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) where
  time : ℝ
  scalar : ℝ
  time_nonneg : 0 ≤ time
  scalar_mem : scalar ∈ Set.Icc (-rho) rho
  hit : D.trajectory q time = canonicalSectionPoint field q scalar

/-- Initial crossing at the recurrent base point. -/
def initialLocalCrossing (D : FlowTrappingData field) (q : Phase2) {rho : ℝ} (hrho : 0 ≤ rho) :
    LocalCrossing D q rho where
  time := 0
  scalar := 0
  time_nonneg := le_rfl
  scalar_mem := by constructor <;> linarith
  hit := by simp [D.trajectory_zero, canonicalSectionPoint_zero]

/-- Forget a positive local return to the nonnegative crossing representation. -/
def LocalCanonicalReturn.toLocalCrossing (H : LocalCanonicalReturn D q rho) :
    LocalCrossing D q rho where
  time := H.time
  scalar := H.scalar
  time_nonneg := H.time_pos.le
  scalar_mem := H.scalar_mem
  hit := H.hit

/-- Two chronologically consecutive local crossings.  The first may be the initial crossing. -/
structure ConsecutiveLocalCrossings (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) where
  first : LocalCrossing D q rho
  second : LocalCrossing D q rho
  ordered : first.time < second.time
  noLocalBetween : ∀ t, first.time < t → t < second.time →
    t ∉ localReturnTimes D q rho

/-- First return gives consecutive crossings from the initial point. -/
def FirstLocalReturn.toConsecutiveCrossings
    (H : FirstLocalReturn D q rho) (hrho : 0 ≤ rho) :
    ConsecutiveLocalCrossings D q rho where
  first := initialLocalCrossing D q hrho
  second := H.toLocalCanonicalReturn.toLocalCrossing
  ordered := H.time_pos
  noLocalBetween := H.first

/-- A consecutive positive-return pair gives consecutive crossings. -/
def ConsecutiveLocalReturns.toConsecutiveCrossings
    (H : ConsecutiveLocalReturns D q rho) :
    ConsecutiveLocalCrossings D q rho where
  first := H.first.toLocalCrossing
  second := H.second.toLocalCrossing
  ordered := H.ordered
  noLocalBetween := H.consecutive

namespace ConsecutiveLocalCrossings

/-- Duration of the orbit arc. -/
def duration (A : ConsecutiveLocalCrossings D q rho) : ℝ := A.second.time - A.first.time

@[simp] theorem duration_pos (A : ConsecutiveLocalCrossings D q rho) : 0 < A.duration :=
  sub_pos.mpr A.ordered

/-- Orbit time on the first half of the normalized loop. -/
def orbitTime (A : ConsecutiveLocalCrossings D q rho) (s : ℝ) : ℝ :=
  A.first.time + (2*s) * A.duration

/-- Scalar coordinate on the straight closing edge. -/
def edgeScalar (A : ConsecutiveLocalCrossings D q rho) (s : ℝ) : ℝ :=
  A.second.scalar + (2*s - 1) * (A.first.scalar - A.second.scalar)

/-- Orbit arc followed by the straight local-section edge back to the first crossing. -/
noncomputable def loopCurve (A : ConsecutiveLocalCrossings D q rho) (s : ℝ) : Phase2 :=
  if s < (1/2 : ℝ) then D.trajectory q (A.orbitTime s)
  else canonicalSectionPoint field q (A.edgeScalar s)

@[simp] theorem loopCurve_zero (A : ConsecutiveLocalCrossings D q rho) :
    A.loopCurve 0 = canonicalSectionPoint field q A.first.scalar := by
  simp [loopCurve, orbitTime, A.first.hit]

@[simp] theorem loopCurve_half (A : ConsecutiveLocalCrossings D q rho) :
    A.loopCurve (1/2 : ℝ) = canonicalSectionPoint field q A.second.scalar := by
  rw [loopCurve, if_neg (by norm_num : ¬ (1/2 : ℝ) < 1/2)]
  simp [edgeScalar]

@[simp] theorem loopCurve_one (A : ConsecutiveLocalCrossings D q rho) :
    A.loopCurve 1 = canonicalSectionPoint field q A.first.scalar := by
  rw [loopCurve, if_neg (by norm_num : ¬ (1 : ℝ) < 1/2)]
  congr 1
  unfold edgeScalar
  ring

/-- The closed orbit arc and section segment agree at the gluing parameter and are continuous on
the normalized interval. -/
theorem loopCurve_continuousOn (A : ConsecutiveLocalCrossings D q rho) :
    ContinuousOn A.loopCurve (Set.Icc (0 : ℝ) 1) := by
  let dom : Set ℝ := Set.Icc (0 : ℝ) 1
  let branch : Set ℝ := Set.Iio (1/2 : ℝ)
  let f : ℝ → Phase2 := fun s => D.trajectory q (A.orbitTime s)
  let g : ℝ → Phase2 := fun s => canonicalSectionPoint field q (A.edgeScalar s)
  have htraj : Continuous (D.trajectory q) :=
    continuous_iff_continuousAt.mpr fun t => (D.trajectory_solution q t).continuousAt
  have htime : Continuous A.orbitTime := by
    fun_prop [orbitTime, duration]
  have hf : Continuous f := htraj.comp htime
  have hg : Continuous g := by
    fun_prop [canonicalSectionPoint, edgeScalar]
  have hglue : Set.EqOn f g (dom ∩ frontier branch) := by
    intro s hs
    have hfront : s = (1/2 : ℝ) := by
      have h := frontier_lt_subset_eq continuous_id continuous_const hs.2
      simpa [branch] using h
    subst s
    change D.trajectory q (A.orbitTime (1/2 : ℝ)) =
      canonicalSectionPoint field q (A.edgeScalar (1/2 : ℝ))
    have htime' : A.orbitTime (1/2 : ℝ) = A.second.time := by
      unfold orbitTime duration
      ring
    rw [htime', A.second.hit]
    simp [edgeScalar]
  have hpw : ContinuousOn (branch.piecewise f g) (branch.ite dom dom) :=
    continuousOn_piecewise_ite hf.continuousOn hg.continuousOn rfl hglue
  have hdom : branch.ite dom dom = dom := by
    ext s
    simp [Set.ite]
  rw [hdom] at hpw
  change ContinuousOn (fun s => if s < (1/2 : ℝ) then
    D.trajectory q (A.orbitTime s) else
    canonicalSectionPoint field q (A.edgeScalar s)) dom
  exact hpw

/-- Every point of the straight closing edge remains inside the local scalar window. -/
theorem edgeScalar_mem (A : ConsecutiveLocalCrossings D q rho)
    {s : ℝ} (hs : s ∈ Set.Icc (1/2 : ℝ) 1) :
    A.edgeScalar s ∈ Set.Icc (-rho) rho := by
  have hCoeff0 : 0 ≤ 2*s - 1 := by linarith [hs.1]
  have hCoeff1 : 2*s - 1 ≤ 1 := by linarith [hs.2]
  have hweights : 0 ≤ 1 - (2*s - 1) := by linarith
  have hformula : A.edgeScalar s =
      (1 - (2*s - 1)) * A.second.scalar + (2*s - 1) * A.first.scalar := by
    dsimp [edgeScalar]
    ring
  constructor
  · rw [hformula]
    calc
      -rho = (1 - (2*s - 1)) * (-rho) + (2*s - 1) * (-rho) := by ring
      _ ≤ (1 - (2*s - 1)) * A.second.scalar + (2*s - 1) * A.first.scalar :=
        add_le_add
          (mul_le_mul_of_nonneg_left A.second.scalar_mem.1 hweights)
          (mul_le_mul_of_nonneg_left A.first.scalar_mem.1 hCoeff0)
  · rw [hformula]
    calc
      (1 - (2*s - 1)) * A.second.scalar + (2*s - 1) * A.first.scalar ≤
          (1 - (2*s - 1)) * rho + (2*s - 1) * rho :=
        add_le_add
          (mul_le_mul_of_nonneg_left A.second.scalar_mem.2 hweights)
          (mul_le_mul_of_nonneg_left A.first.scalar_mem.2 hCoeff0)
      _ = rho := by ring

/-- A scalar between the crossing endpoints remains in the closed section window. -/
theorem intervalBetween_scalars_mem_window
    (a b u : ℝ) (ha : a ∈ Set.Icc (-rho) rho) (hb : b ∈ Set.Icc (-rho) rho)
    (hu : u ∈ Set.uIcc a b) : u ∈ Set.Icc (-rho) rho :=
  Set.uIcc_subset_Icc ha hb hu

/-- An interior orbit point cannot lie on the closing edge: such an intersection would be an
intervening local return. -/
theorem orbitArc_disjoint_edge
    (A : ConsecutiveLocalCrossings D q rho)
    (hne : field q ≠ 0)
    {t : ℝ} (ht1 : A.first.time < t) (ht2 : t < A.second.time)
    {u : ℝ} (hu : u ∈ Set.uIcc A.first.scalar A.second.scalar)
    (hinter : D.trajectory q t = canonicalSectionPoint field q u) : False := by
  have huWindow : u ∈ Set.Icc (-rho) rho :=
    intervalBetween_scalars_mem_window A.first.scalar A.second.scalar u
      A.first.scalar_mem A.second.scalar_mem hu
  have htret : t ∈ localReturnTimes D q rho := by
    refine ⟨lt_of_le_of_lt A.first.time_nonneg ht1, ?_⟩
    exact ⟨u, huWindow, hinter.symm⟩
  exact A.noLocalBetween t ht1 ht2 htret

/-- Under aperiodicity the orbit arc itself is injective. -/
theorem orbitArc_injective
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hqne : field q ≠ 0)
    (haper : ¬ HasPeriodicTrajectoryThrough field q)
    {s t : ℝ}
    (hs : s ∈ Set.Icc A.first.time A.second.time)
    (ht : t ∈ Set.Icc A.first.time A.second.time)
    (heq : D.trajectory q s = D.trajectory q t) : s = t := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hst | hts
  · have P := D.periodicTrajectory_of_selfIntersection hsmooth hst heq hqne
    exact haper P
  · have P := D.periodicTrajectory_of_selfIntersection hsmooth hts heq.symm hqne
    exact haper P

/-- Distinct scalar endpoints follow from aperiodicity: equal endpoints are the same state. -/
theorem scalar_ne
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hqne : field q ≠ 0)
    (haper : ¬ HasPeriodicTrajectoryThrough field q) :
    A.first.scalar ≠ A.second.scalar := by
  intro heq
  have hstate : D.trajectory q A.first.time = D.trajectory q A.second.time := by
    rw [A.first.hit, A.second.hit, heq]
  have P := D.periodicTrajectory_of_selfIntersection hsmooth A.ordered hstate hqne
  exact haper P

/-- Normalized parameters on the first half map into the closed orbit-time interval. -/
theorem orbitTime_mem_Ico (A : ConsecutiveLocalCrossings D q rho)
    {s : ℝ} (hs : s ∈ Set.Ico (0 : ℝ) 1) (hsOrbit : s < 1/2) :
    A.orbitTime s ∈ Set.Ico A.first.time A.second.time := by
  constructor
  · unfold orbitTime duration
    have hprod : 0 ≤ (2*s) * (A.second.time - A.first.time) :=
      mul_nonneg (by linarith [hs.1]) (sub_nonneg.mpr A.ordered.le)
    nlinarith
  · have hscale : 2*s < 1 := by linarith
    have hprod := mul_lt_mul_of_pos_right hscale A.duration_pos
    unfold orbitTime duration at hprod ⊢
    nlinarith

/-- The affine scalar parameter runs through the interval between its endpoint scalars. -/
theorem edgeScalar_mem_between (A : ConsecutiveLocalCrossings D q rho)
    {s : ℝ} (hs : s ∈ Set.Icc (1/2 : ℝ) 1) :
    A.edgeScalar s ∈ Set.uIcc A.first.scalar A.second.scalar := by
  have hCoeff0 : 0 ≤ 2*s - 1 := by linarith [hs.1]
  have hCoeff1 : 2*s - 1 ≤ 1 := by linarith [hs.2]
  have hw0 : 0 ≤ 1 - (2*s - 1) := by linarith
  have hform : A.edgeScalar s =
      (2*s - 1) * A.first.scalar + (1 - (2*s - 1)) * A.second.scalar := by
    dsimp [edgeScalar]
    ring
  rw [Set.mem_uIcc]
  rcases le_total A.first.scalar A.second.scalar with hab | hba
  · left
    constructor
    · calc
        A.first.scalar = (2*s - 1) * A.first.scalar +
            (1 - (2*s - 1)) * A.first.scalar := by ring
        _ ≤ (2*s - 1) * A.first.scalar +
            (1 - (2*s - 1)) * A.second.scalar :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hab hw0)
        _ = A.edgeScalar s := hform.symm
    · calc
        A.edgeScalar s = (2*s - 1) * A.first.scalar +
            (1 - (2*s - 1)) * A.second.scalar := hform
        _ ≤ (2*s - 1) * A.second.scalar +
            (1 - (2*s - 1)) * A.second.scalar :=
          add_le_add (mul_le_mul_of_nonneg_left hab hCoeff0) le_rfl
        _ = A.second.scalar := by ring
  · right
    constructor
    · calc
        A.second.scalar = (2*s - 1) * A.second.scalar +
            (1 - (2*s - 1)) * A.second.scalar := by ring
        _ ≤ (2*s - 1) * A.first.scalar +
            (1 - (2*s - 1)) * A.second.scalar :=
          add_le_add (mul_le_mul_of_nonneg_left hba hCoeff0) le_rfl
        _ = A.edgeScalar s := hform.symm
    · calc
        A.edgeScalar s = (2*s - 1) * A.first.scalar +
            (1 - (2*s - 1)) * A.second.scalar := hform
        _ ≤ (2*s - 1) * A.first.scalar +
            (1 - (2*s - 1)) * A.first.scalar :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left hba hw0)
        _ = A.first.scalar := by ring

/-- Distinct endpoint scalars make the affine closing edge injective. -/
theorem edgeScalar_injective (A : ConsecutiveLocalCrossings D q rho)
    (hscalar : A.first.scalar ≠ A.second.scalar) :
    Function.Injective A.edgeScalar := by
  intro s t heq
  have hmul : (2*s - 2*t) * (A.first.scalar - A.second.scalar) = 0 := by
    unfold edgeScalar at heq
    linear_combination heq
  rcases mul_eq_zero.mp hmul with hst | hscalar'
  · linarith
  · exact False.elim ((sub_ne_zero.mpr hscalar) hscalar')

/-- Every point between the endpoint scalars has a unique parameter on the closing half. -/
theorem edgeScalar_surjective_uIcc (A : ConsecutiveLocalCrossings D q rho)
    (hscalar : A.first.scalar ≠ A.second.scalar)
    {u : ℝ} (hu : u ∈ Set.uIcc A.first.scalar A.second.scalar) :
    ∃ s ∈ Set.Icc (1/2 : ℝ) 1, A.edgeScalar s = u := by
  let den := A.first.scalar - A.second.scalar
  let lam := (u - A.second.scalar) / den
  let s := (lam + 1) / 2
  have hden : den ≠ 0 := sub_ne_zero.mpr hscalar
  have hLam : 0 ≤ lam ∧ lam ≤ 1 := by
    rcases Set.mem_uIcc.mp hu with ⟨hua, hub⟩ | ⟨hub, hua⟩
    · have horder : A.first.scalar < A.second.scalar := by
        by_contra hnot
        have : A.second.scalar ≤ A.first.scalar := le_of_not_gt hnot
        exact hscalar (le_antisymm (hua.trans hub) this)
      have hdenneg : den < 0 := by dsimp [den]; linarith
      have hnum_nonpos : u - A.second.scalar ≤ 0 := by linarith
      have hden_le_num : den ≤ u - A.second.scalar := by dsimp [den]; linarith
      constructor
      · dsimp [lam]
        exact (div_nonneg_iff).2 (Or.inr ⟨hnum_nonpos, hdenneg.le⟩)
      · dsimp [lam, den]
        exact div_le_one_of_ge hden_le_num hdenneg.le
    · have horder : A.second.scalar < A.first.scalar := by
        by_contra hnot
        have : A.first.scalar ≤ A.second.scalar := le_of_not_gt hnot
        exact hscalar (le_antisymm this (hub.trans hua))
      have hdenpos : 0 < den := by dsimp [den]; linarith
      have hnum_nonneg : 0 ≤ u - A.second.scalar := by linarith
      have hnum_le_den : u - A.second.scalar ≤ den := by dsimp [den]; linarith
      constructor
      · dsimp [lam]
        exact div_nonneg hnum_nonneg hdenpos.le
      · dsimp [lam, den]
        exact (div_le_one hdenpos).2 hnum_le_den
  have hs : s ∈ Set.Icc (1/2 : ℝ) 1 := by
    constructor <;> dsimp [s] <;> nlinarith [hLam.1, hLam.2]
  have hedge : A.edgeScalar s = u := by
    dsimp [edgeScalar, s, lam, den]
    field_simp [sub_ne_zero.mpr hscalar]
    ring
  exact ⟨s, hs, hedge⟩

/-- Consecutive local crossings form a simple Jordan loop whenever the ambient orbit is aperiodic. -/
noncomputable def toSimplePlanarLoop
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    (haper : ¬ HasPeriodicTrajectoryThrough field q) :
    SimplePlanarLoop := by
  have hscalar := A.scalar_ne hsmooth hne haper
  refine {
    curve := A.loopCurve
    continuous := A.loopCurve_continuousOn
    closes := by simp
    injective_Ico := ?_ }
  intro s hs t ht heq
  have hmixed {u v : ℝ} (hu : u ∈ Set.Ico (0 : ℝ) 1)
      (hv : v ∈ Set.Ico (0 : ℝ) 1) (huOrbit : u < 1/2)
      (hvEdge : ¬ v < 1/2) (heq' : A.loopCurve u = A.loopCurve v) : False := by
    have htime : A.orbitTime u ∈ Set.Ico A.first.time A.second.time :=
      A.orbitTime_mem_Ico hu huOrbit
    have hcurve : D.trajectory q (A.orbitTime u) =
        canonicalSectionPoint field q (A.edgeScalar v) := by
      simpa only [loopCurve, if_pos huOrbit, if_neg hvEdge] using heq'
    have hscalarBetween : A.edgeScalar v ∈ Set.uIcc A.first.scalar A.second.scalar :=
      A.edgeScalar_mem_between ⟨by linarith [hv.1], le_of_lt hv.2⟩
    by_cases hu0 : u = 0
    · subst u
      have hscalarEq : A.edgeScalar v = A.first.scalar := by
        apply canonicalSectionPoint_injective hne
        calc
          canonicalSectionPoint field q (A.edgeScalar v) =
              D.trajectory q (A.orbitTime 0) := hcurve.symm
          _ = canonicalSectionPoint field q A.first.scalar := by
            simp [orbitTime, A.first.hit]
      have hdiff : A.first.scalar - A.second.scalar ≠ 0 :=
        sub_ne_zero.mpr hscalar
      have hprod : (2*v - 2) * (A.first.scalar - A.second.scalar) = 0 := by
        unfold edgeScalar at hscalarEq
        linear_combination hscalarEq
      rcases mul_eq_zero.mp hprod with hvval | hval
      · linarith [hv.2]
      · exact (hdiff hval).elim
    · have huPos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
      have hfirst : A.first.time < A.orbitTime u := by
        unfold orbitTime duration
        nlinarith [huPos, A.ordered]
      have hsecond : A.orbitTime u < A.second.time := by
        have hscale : 2*u < 1 := by linarith
        have hprod := mul_lt_mul_of_pos_right hscale A.duration_pos
        unfold orbitTime duration at hprod ⊢
        nlinarith
      exact A.orbitArc_disjoint_edge hne hfirst hsecond hscalarBetween hcurve
  by_cases hsOrbit : s < 1/2
  · by_cases htOrbit : t < 1/2
    · have hsTime : A.orbitTime s ∈ Set.Icc A.first.time A.second.time :=
        Set.Ico_subset_Icc_self (A.orbitTime_mem_Ico hs hsOrbit)
      have htTime : A.orbitTime t ∈ Set.Icc A.first.time A.second.time :=
        Set.Ico_subset_Icc_self (A.orbitTime_mem_Ico ht htOrbit)
      have htrajEq : D.trajectory q (A.orbitTime s) = D.trajectory q (A.orbitTime t) := by
        simpa only [loopCurve, if_pos hsOrbit, if_pos htOrbit] using heq
      have htime := A.orbitArc_injective hsmooth hne haper hsTime htTime htrajEq
      have hmul : (2*s - 2*t) * A.duration = 0 := by
        unfold orbitTime at htime
        linear_combination htime
      rcases mul_eq_zero.mp hmul with hst | hdur
      · linarith
      · exact (A.duration_pos.ne' hdur).elim
    · exact (hmixed hs ht hsOrbit htOrbit heq).elim
  · by_cases htOrbit : t < 1/2
    · exact (hmixed ht hs htOrbit hsOrbit heq.symm).elim
    · have hparam : A.edgeScalar s = A.edgeScalar t := by
        apply canonicalSectionPoint_injective hne
        simpa only [loopCurve, if_neg hsOrbit, if_neg htOrbit] using heq
      exact A.edgeScalar_injective hscalar hparam

/-- The closing edge is part of the loop trace. -/
theorem closingEdge_subset_trace
    (A : ConsecutiveLocalCrossings D q rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    (haper : ¬ HasPeriodicTrajectoryThrough field q) :
    canonicalSectionPoint field q '' Set.uIcc A.first.scalar A.second.scalar ⊆
      (A.toSimplePlanarLoop hsmooth hne haper).trace := by
  intro x hx
  obtain ⟨u, hu, rfl⟩ := hx
  have hscalar := A.scalar_ne hsmooth hne haper
  obtain ⟨s, hs, hus⟩ := A.edgeScalar_surjective_uIcc hscalar hu
  have hs01 : s ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith [hs.1], hs.2⟩
  refine ⟨s, hs01, ?_⟩
  change A.loopCurve s = canonicalSectionPoint field q u
  rw [loopCurve, if_neg (by linarith [hs.1]), hus]

end ConsecutiveLocalCrossings

end Planar
end CRNT
