import CRNT.Oscillation.PlanarSectionHitIsolation
import CRNT.Oscillation.PlanarFlowBox

/-!
# Local return chronology on the canonical transversal

The global affine line through a recurrent point is too large for the ordering argument: a trajectory
may cross that line far away while the local Poincare section remains perfectly well behaved.  This
module therefore fixes a small scalar window `[-rho,rho]` on the canonical section and develops the
chronology of returns to that *local* section.

On a window where `<field(xsection u), field q> > 0`, every local zero of the signed section function
is simple.  Hence local hit times are discrete.  Their intersection with a compact time interval is
closed and discrete, therefore finite.  This permits genuine first/next-return constructions and
finite induction over all local crossings before a prescribed time.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace

namespace Planar

open Set Filter Topology

/-- Closed scalar window on the canonical section. -/
def localCanonicalSection (field : Phase2 → Phase2) (q : Phase2) (rho : ℝ) : Set Phase2 :=
  canonicalSectionPoint field q '' Set.Icc (-rho) rho

/-- A canonical section hit whose scalar lies in the chosen closed local window. -/
structure LocalCanonicalReturn {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) extends CanonicalSectionHit D q where
  scalar_mem : scalar ∈ Set.Icc (-rho) rho

namespace LocalCanonicalReturn

variable {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ}

/-- State-space form of local-window membership. -/
theorem state_mem (H : LocalCanonicalReturn D q rho) :
    D.trajectory q H.time ∈ localCanonicalSection field q rho := by
  exact ⟨H.scalar, H.scalar_mem, H.hit.symm⟩

end LocalCanonicalReturn

/-- Positive local return times. -/
def localReturnTimes {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) : Set ℝ :=
  {t | 0 < t ∧ D.trajectory q t ∈ localCanonicalSection field q rho}

/-- Recover the unique scalar coordinate of a local hit. -/
noncomputable def localReturnOfTime
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ}
    (hne : field q ≠ 0) {t : ℝ} (ht : t ∈ localReturnTimes D q rho) :
    LocalCanonicalReturn D q rho := by
  let u := Classical.choose ht.2
  have hu : u ∈ Set.Icc (-rho) rho := (Classical.choose_spec ht.2).1
  have hstate : canonicalSectionPoint field q u = D.trajectory q t :=
    (Classical.choose_spec ht.2).2
  exact {
    time := t
    scalar := u
    time_pos := ht.1
    hit := hstate.symm
    scalar_mem := hu }

/-- Local section points tend to `q` with their scalar coordinate. -/
theorem canonicalSectionPoint_tendsto_base
    {field : Phase2 → Phase2} {q : Phase2} :
    Tendsto (canonicalSectionPoint field q) (𝓝 0) (𝓝 q) := by
  have hcont : Continuous (canonicalSectionPoint field q) := by
    fun_prop [canonicalSectionPoint]
  have h : ContinuousAt (canonicalSectionPoint field q) 0 := hcont.continuousAt
  change Tendsto (canonicalSectionPoint field q) (𝓝 0)
    (𝓝 (canonicalSectionPoint field q 0)) at h
  rw [canonicalSectionPoint_zero] at h
  exact h

/-- Every neighbourhood of `q` contains a symmetric scalar interval of the canonical section. -/
theorem canonicalSectionPoint_eventually_mem_nhds
    {field : Phase2 → Phase2} {q : Phase2} {U : Set Phase2}
    (hU : U ∈ 𝓝 q) :
    ∃ rho > 0, ∀ u, |u| ≤ rho → canonicalSectionPoint field q u ∈ U := by
  have hev := (canonicalSectionPoint_tendsto_base (field := field) (q := q)).eventually hU
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hev
  refine ⟨δ / 2, by positivity, ?_⟩
  intro u hu
  apply hball
  have huδ : |u| < δ := lt_of_le_of_lt hu (by linarith : δ / 2 < δ)
  simpa [Metric.mem_ball, Real.dist_eq] using huδ

/-- Choose a local section window on which every crossing has the same strict normal orientation. -/
theorem exists_positiveSpeedWindow
    {field : Phase2 → Phase2} {q : Phase2}
    (hcont : Continuous field) (hne : field q ≠ 0) :
    ∃ rho > 0, ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ := by
  obtain ⟨U, hU, hspeed⟩ := exists_nhds_positive_canonical_speed hcont hne
  obtain ⟨rho, hrho, hsec⟩ := canonicalSectionPoint_eventually_mem_nhds
    (field := field) (q := q) hU
  refine ⟨rho, hrho, ?_⟩
  intro u hu
  apply hspeed
  exact hsec u (by simpa [abs_le] using hu)

/-- On a positive-speed window, every local return time is isolated inside the local return set. -/
theorem localReturnTime_isolated
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ}
    (hcont : Continuous field)
    (horient : ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ)
    (hne : field q ≠ 0)
    {t : ℝ} (ht : t ∈ localReturnTimes D q rho) :
    ∃ eps > 0, Set.Ioo (t-eps) (t+eps) ∩ localReturnTimes D q rho = {t} := by
  obtain ⟨u, hu, hhit⟩ := ht.2
  have hderiv : 0 < ⟪field (D.trajectory q t), field q⟫_ℝ := by
    rw [← hhit]
    exact horient u hu
  have hzero_t : sectionCrossingFunction D q t = 0 := by
    rw [sectionCrossingFunction_eq_zero_iff, ← hhit]
    exact canonicalSectionPoint_mem field q u
  obtain ⟨eps, heps, hiso⟩ :=
    sectionHit_isolated D q hcont hzero_t hderiv
  refine ⟨eps, heps, ?_⟩
  ext s
  constructor
  · rintro ⟨hsIoo, hsret⟩
    have hzero_t : sectionCrossingFunction D q t = 0 := by
      rw [sectionCrossingFunction_eq_zero_iff, ← hhit]
      exact canonicalSectionPoint_mem field q u
    obtain ⟨v, hv, hsv⟩ := hsret.2
    have hzero_s : sectionCrossingFunction D q s = 0 := by
      rw [sectionCrossingFunction_eq_zero_iff, ← hsv]
      exact canonicalSectionPoint_mem field q v
    have habs : |s - t| < eps := by
      have hslo := hsIoo.1
      have hshi := hsIoo.2
      rw [abs_lt]
      constructor <;> linarith
    have : s = t := hiso s habs hzero_s
    simpa [this]
  · intro hs
    have : s = t := by simpa using hs
    subst s
    exact ⟨by simpa using heps, ht⟩

/-- Local return times form a closed subset of any compact interval whose left endpoint is positive.
The local section window is compact as the continuous image of a scalar interval. -/
theorem isClosed_localReturnTimes_inter_Icc
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho a b : ℝ}
    (hcont : Continuous field) (ha : 0 < a) :
    IsClosed (localReturnTimes D q rho ∩ Set.Icc a b) := by
  have hsection : Continuous (canonicalSectionPoint field q) := by
    fun_prop [canonicalSectionPoint]
  have hcompact : IsCompact (localCanonicalSection field q rho) := by
    rw [localCanonicalSection]
    exact isCompact_Icc.image hsection
  have hclosedSection : IsClosed (localCanonicalSection field q rho) := hcompact.isClosed
  have htrajectory : Continuous (D.trajectory q) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (D.trajectory_solution q t).continuousAt
  have hpre : IsClosed {t : ℝ | D.trajectory q t ∈ localCanonicalSection field q rho} :=
    hclosedSection.preimage htrajectory
  have hset : localReturnTimes D q rho ∩ Set.Icc a b =
      {t | t ∈ Set.Icc a b ∧ D.trajectory q t ∈ localCanonicalSection field q rho} := by
    ext t
    simp only [localReturnTimes, mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨⟨_, ht⟩, hi⟩
      exact ⟨hi, ht⟩
    · rintro ⟨hi, ht⟩
      exact ⟨⟨lt_of_lt_of_le ha hi.1, ht⟩, hi⟩
  rw [hset]
  exact isClosed_Icc.inter hpre

/-- The local-return set restricted to a compact time interval is finite. -/
theorem finite_localReturns_Icc
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ}
    (hcont : Continuous field)
    (horient : ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ)
    (hne : field q ≠ 0) (a b : ℝ) (ha : 0 < a) :
    (localReturnTimes D q rho ∩ Set.Icc a b).Finite := by
  let A : Set ℝ := localReturnTimes D q rho ∩ Set.Icc a b
  have hclosed : IsClosed (localReturnTimes D q rho ∩ Set.Icc a b) := by
    exact isClosed_localReturnTimes_inter_Icc hcont ha
  have hcpt : IsCompact A := by
    exact IsCompact.of_isClosed_subset isCompact_Icc hclosed inter_subset_right
  classical
  let eps : A → ℝ := fun t => Classical.choose
    (localReturnTime_isolated hcont horient hne t.2.1)
  have heps : ∀ t : A, 0 < eps t := fun t => (Classical.choose_spec
    (localReturnTime_isolated hcont horient hne t.2.1)).1
  let U : A → Set ℝ := fun t => Set.Ioo ((t : ℝ) - eps t) ((t : ℝ) + eps t)
  have hUopen : ∀ t, IsOpen (U t) := fun t => isOpen_Ioo
  have hcover : A ⊆ ⋃ t : A, U t := by
    intro x hx
    let t : A := ⟨x, hx⟩
    refine Set.mem_iUnion.mpr ⟨t, ?_⟩
    change (t : ℝ) - eps t < x ∧ x < (t : ℝ) + eps t
    have htx : (t : ℝ) = x := rfl
    rw [htx]
    constructor <;> linarith [heps t]
  obtain ⟨T, hT⟩ := hcpt.elim_finite_subcover U hUopen hcover
  have hsub : A ⊆ (T.image fun t : A => (t : ℝ) : Finset ℝ) := by
    intro x hx
    rcases Set.mem_iUnion₂.mp (hT hx) with ⟨t, htT, hxt⟩
    have hiso := (Classical.choose_spec
      (localReturnTime_isolated hcont horient hne t.2.1)).2
    have hxEq : x = (t : ℝ) := by
      have hpair : x ∈ U t ∩ A := ⟨hxt, hx⟩
      have hsingle : U t ∩ localReturnTimes D q rho = {(t : ℝ)} := hiso
      have hpair' : x ∈ U t ∩ localReturnTimes D q rho :=
        ⟨hxt, hx.1⟩
      rw [hsingle] at hpair'
      simpa using hpair'
    exact Finset.mem_image.mpr ⟨t, htT, hxEq.symm⟩
  exact (T.image fun t : A => (t : ℝ)).finite_toSet.subset hsub

/-- A transverse crossing at time zero excludes positive local returns for a short interval. -/
theorem localReturn_gap_after_zero
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ}
    (hcont : Continuous field) (hne : field q ≠ 0) :
    ∃ δ > 0, Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho = ∅ := by
  have hzero : sectionCrossingFunction D q 0 = 0 := by
    rw [sectionCrossingFunction_eq_zero_iff]
    rw [D.trajectory_zero]
    simpa [canonicalSectionPoint_zero] using canonicalSectionPoint_mem field q 0
  have hderiv : 0 < ⟪field (D.trajectory q 0), field q⟫_ℝ := by
    simpa [D.trajectory_zero] using canonical_transversal_speed_pos hne
  obtain ⟨δ, hδ, hiso⟩ := sectionHit_isolated D q hcont hzero hderiv
  refine ⟨δ, hδ, ?_⟩
  ext t
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
  rintro ⟨ht, htret⟩
  obtain ⟨u, hu, hhit⟩ := htret.2
  have hsection : D.trajectory q t ∈ canonicalSection field q := by
    rw [← hhit]
    exact canonicalSectionPoint_mem field q u
  have hzero_t : sectionCrossingFunction D q t = 0 :=
    (sectionCrossingFunction_eq_zero_iff D q t).2 hsection
  have hdist : |t - 0| < δ := by
    rw [sub_zero, abs_of_pos ht.1]
    exact ht.2
  have heq := hiso t hdist hzero_t
  exact (ne_of_gt ht.1) heq

/-- Zero is a lower bound for the positive local return times. -/
theorem localReturnTimes_bddBelow
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ} :
    BddBelow (localReturnTimes D q rho) :=
  ⟨0, fun t ht => ht.1.le⟩

/-- A positive local-return set is closed once its time-zero accumulation is excluded. -/
theorem isClosed_localReturnTimes_of_gap
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ}
    (hcont : Continuous field)
    (hgap : ∃ δ > 0, Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho = ∅) :
    IsClosed (localReturnTimes D q rho) := by
  obtain ⟨δ, hδ, hgapEq⟩ := hgap
  have hsection : IsClosed (localCanonicalSection field q rho) := by
    have hc : Continuous (canonicalSectionPoint field q) := by
      fun_prop [canonicalSectionPoint]
    have hk : IsCompact (localCanonicalSection field q rho) := by
      rw [localCanonicalSection]
      exact isCompact_Icc.image hc
    exact hk.isClosed
  have htrajectory : Continuous (D.trajectory q) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (D.trajectory_solution q t).continuousAt
  have hset : localReturnTimes D q rho =
      Set.Ici δ ∩ {t : ℝ | D.trajectory q t ∈ localCanonicalSection field q rho} := by
    ext t
    constructor
    · intro ht
      have hge : δ ≤ t := by
        by_contra hnot
        have htδ : t < δ := lt_of_not_ge hnot
        have hmem : t ∈ Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho :=
          ⟨⟨ht.1, htδ⟩, ht⟩
        rw [hgapEq] at hmem
        exact hmem
      exact ⟨hge, ht.2⟩
    · rintro ⟨htδ, hmem⟩
      exact ⟨lt_of_lt_of_le hδ htδ, hmem⟩
  rw [hset]
  exact isClosed_Ici.inter (hsection.preimage htrajectory)

/-- The gap at zero and a nonempty local-return set make its infimum a positive member. -/
theorem sInf_mem_localReturnTimes
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2} {rho : ℝ}
    (hcont : Continuous field) (hne : field q ≠ 0)
    (hneSet : (localReturnTimes D q rho).Nonempty)
    (hgap : ∃ δ > 0, Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho = ∅) :
    sInf (localReturnTimes D q rho) ∈ localReturnTimes D q rho := by
  obtain ⟨δ, hδ, hgapEq⟩ := hgap
  have hδle : δ ≤ sInf (localReturnTimes D q rho) := by
    apply le_csInf hneSet
    intro t ht
    by_contra hnot
    have htδ : t < δ := lt_of_not_ge hnot
    have hnotmem : t ∈ Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho :=
      ⟨⟨ht.1, htδ⟩, ht⟩
    rw [hgapEq] at hnotmem
    exact hnotmem
  have hclosed := isClosed_localReturnTimes_of_gap hcont ⟨δ, hδ, hgapEq⟩
  have hcl : sInf (localReturnTimes D q rho) ∈ closure (localReturnTimes D q rho) := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, ht, htt⟩ := exists_lt_of_csInf_lt hneSet
      (show sInf (localReturnTimes D q rho) < sInf (localReturnTimes D q rho) + ε by linarith)
    have hle : sInf (localReturnTimes D q rho) ≤ t :=
      csInf_le localReturnTimes_bddBelow ht
    refine ⟨t, ht, ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  exact hclosed.closure_subset hcl

/-- A first positive local return: no earlier positive time hits the local section window. -/
structure FirstLocalReturn {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (rho : ℝ)
    extends LocalCanonicalReturn D q rho where
  first : ∀ t, 0 < t → t < time → t ∉ localReturnTimes D q rho

/-- Recurrence plus isolation at time zero produces a first positive local return. -/
theorem exists_firstLocalReturn
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    {M : MinimalOmegaData D} {q : Phase2}
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field)
    {rho : ℝ} (hrho : 0 < rho) :
    Nonempty (FirstLocalReturn D q rho) := by
  have hne := M.equilibriumFree q hq
  have hnonempty : (localReturnTimes D q rho).Nonempty := by
    obtain ⟨H, _hT, hsmall⟩ :=
      R.exists_late_canonicalSectionHit_smallScalar M hq hsmooth hrho 1
    exact ⟨H.time, H.time_pos, ⟨H.scalar, by
      constructor <;> linarith [abs_lt.mp hsmall], H.hit.symm⟩⟩
  have hgap0 : ∃ δ > 0, Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho = ∅ := by
    exact localReturn_gap_after_zero hsmooth.continuous hne
  let t₁ := sInf (localReturnTimes D q rho)
  have htpos : 0 < t₁ := by
    obtain ⟨δ, hδ, hgap⟩ := hgap0
    have hδle : δ ≤ t₁ := by
      apply le_csInf hnonempty
      intro t ht
      by_contra hnot
      have htδ : t < δ := lt_of_not_ge hnot
      have hmem : t ∈ Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho :=
        ⟨⟨ht.1, htδ⟩, ht⟩
      rw [hgap] at hmem
      exact hmem
    exact lt_of_lt_of_le hδ hδle
  have htmem : t₁ ∈ localReturnTimes D q rho := by
    exact sInf_mem_localReturnTimes hsmooth.continuous hne hnonempty hgap0
  let H := localReturnOfTime hne htmem
  refine ⟨{
    toLocalCanonicalReturn := H
    first := ?_ }⟩
  intro t ht0 htt
  intro htret
  exact (not_lt_of_ge (csInf_le localReturnTimes_bddBelow htret)) htt

/-- Consecutive returns in the local window. -/
structure ConsecutiveLocalReturns {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) : Type where
  first : LocalCanonicalReturn D q rho
  second : LocalCanonicalReturn D q rho
  ordered : first.time < second.time
  consecutive : ∀ t, first.time < t → t < second.time →
    t ∉ localReturnTimes D q rho

/-- Every local return has a chronologically next local return when arbitrarily late recurrence
is available and the chosen section window is transverse throughout.  A flow box controls a
neighborhood of the base point; it does not certify transversality on every positive-radius window. -/
theorem exists_nextLocalReturn
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    {M : MinimalOmegaData D} {q : Phase2}
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field)
    {rho : ℝ} (hrho : 0 < rho)
    (horient : ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ)
    (H : LocalCanonicalReturn D q rho) :
    ∃ H' : LocalCanonicalReturn D q rho,
      H.time < H'.time ∧
      ∀ t, H.time < t → t < H'.time → t ∉ localReturnTimes D q rho := by
  have hne := M.equilibriumFree q hq
  have hlate : ∃ t ∈ localReturnTimes D q rho, H.time < t := by
    obtain ⟨K, hKtime, hKsmall⟩ :=
      R.exists_late_canonicalSectionHit_smallScalar M hq hsmooth hrho (H.time + 1)
    refine ⟨K.time, ?_, by linarith⟩
    exact ⟨K.time_pos, ⟨K.scalar, by
      constructor <;> linarith [abs_lt.mp hKsmall], K.hit.symm⟩⟩
  let A := localReturnTimes D q rho
  let B := A ∩ Set.Ioi H.time
  have hBne : B.Nonempty := by
    rcases hlate with ⟨t, htA, ht⟩
    exact ⟨t, htA, ht⟩
  have hBdd : BddBelow B := ⟨H.time, by
    intro t ht
    exact le_of_lt ht.2⟩
  let tnext := sInf B
  have hge : H.time ≤ tnext := le_csInf hBne (fun t ht => le_of_lt ht.2)
  have hgt : H.time < tnext := by
    by_contra hnot
    have heq : tnext = H.time := le_antisymm (le_of_not_gt hnot) hge
    obtain ⟨eps, heps, hiso⟩ := localReturnTime_isolated hsmooth.continuous
      horient hne ⟨H.time_pos, H.state_mem⟩
    have hupper : tnext < H.time + eps := by rw [heq]; linarith
    obtain ⟨t, htB, htlt⟩ := exists_lt_of_csInf_lt hBne hupper
    have htH : H.time < t := by simpa using htB.2
    have htIoo : t ∈ Set.Ioo (H.time - eps) (H.time + eps) := by
      constructor <;> linarith [htH, htlt, heps]
    have hmem : t ∈ Set.Ioo (H.time - eps) (H.time + eps) ∩ A :=
      ⟨htIoo, htB.1⟩
    rw [hiso] at hmem
    have hteq : t = H.time := by simpa using hmem
    exact (ne_of_gt htB.2) hteq
  have hgap0 : ∃ δ > 0, Set.Ioo (0 : ℝ) δ ∩ localReturnTimes D q rho = ∅ := by
    exact localReturn_gap_after_zero hsmooth.continuous hne
  have hclosed := isClosed_localReturnTimes_of_gap hsmooth.continuous hgap0
  have hcl : tnext ∈ closure A := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨t, htB, htlt⟩ := exists_lt_of_csInf_lt hBne
      (show sInf B < sInf B + ε by linarith)
    have hle : tnext ≤ t := csInf_le hBdd htB
    refine ⟨t, htB.1, ?_⟩
    rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
    linarith
  have htnext : tnext ∈ A := hclosed.closure_subset hcl
  let H' := localReturnOfTime hne htnext
  refine ⟨H', hgt, ?_⟩
  intro t htH htt htret
  have htB : t ∈ B := ⟨htret, htH⟩
  exact (not_lt_of_ge (csInf_le hBdd htB)) htt

end Planar
end CRNT
