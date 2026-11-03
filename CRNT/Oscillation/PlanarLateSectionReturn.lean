import CRNT.Oscillation.PlanarFlowBox
import CRNT.Oscillation.PlanarMinimalSet

/-!
# Late canonical-section returns from recurrence and a local flow box

The minimal-set recurrence theorem only says that the orbit of a recurrent point comes arbitrarily
close to that point.  Poincare--Bendixson needs genuine intersections with a one-dimensional
transversal.  A local flow box converts the former into the latter.

Suppose a late point `trajectory q T` lies in the target of the canonical flow-box chart.  Its local
coordinates `(tau,u)` satisfy

`trajectory q T = trajectory (canonicalSectionPoint field q u) tau`.

Autonomous uniqueness/no-crossing then shifts the equality backwards by `tau` and gives

`trajectory q (T-tau) = canonicalSectionPoint field q u`.

By shrinking the target so that `|tau| < 1`, arbitrarily late recurrence gives arbitrarily late
*actual* section hits.  This is the recurrence-to-transversal step of the classical proof.
-/

namespace CRNT

-- `Tendsto`/`𝓝` and `ℝ≥0` are all scoped; without these, `autoImplicit` binds them as
-- unknown-typed variables and they surface as `Function expected` / `LE Type`.
open Filter Topology
open scoped NNReal

namespace Planar

/-- Package the two canonical flow-box coordinates into `Phase2`. -/
noncomputable def flowBoxCoord (t u : ℝ) : Phase2 := WithLp.toLp 2 ![t, u]

@[simp] theorem flowBoxCoord_zero (t u : ℝ) : flowBoxCoord t u 0 = t := by
  simp [flowBoxCoord, WithLp.ofLp_toLp]

@[simp] theorem flowBoxCoord_one (t u : ℝ) : flowBoxCoord t u 1 = u := by
  simp [flowBoxCoord, WithLp.ofLp_toLp]

/-- A genuine positive-time intersection of the recurrent trajectory with the canonical section. -/
structure CanonicalSectionHit {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) : Type where
  time : ℝ
  scalar : ℝ
  time_pos : 0 < time
  hit : D.trajectory q time = canonicalSectionPoint field q scalar

namespace CanonicalFlowBoxRegularity

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {M : MinimalOmegaData D} {q : Phase2}

/-- The inverse chart coordinates tend to `(0,0)` as ambient points tend to `q`. -/
theorem inverse_tendsto_zero
    (R : CanonicalFlowBoxRegularity D q)
    (hne : field q ≠ 0) :
    Tendsto (R.localHomeomorph hne).symm (𝓝 q) (𝓝 (0 : Phase2)) := by
  have hq := R.q_mem_target hne
  have hcont := (R.localHomeomorph hne).continuousAt_symm hq
  -- `ContinuousAt f q` is `Tendsto f (𝓝 q) (𝓝 (f q))`, so we must identify `symm q = 0`.
  have hmap : (R.localHomeomorph hne) 0 = q := by
    simpa [localHomeomorph] using R.map_zero
  have hzero : (R.localHomeomorph hne).symm q = 0 := by
    -- rewriting the goal is not motive-correct; rewrite inside `left_inv` instead
    have hinv := (R.localHomeomorph hne).left_inv (R.zero_mem_source hne)
    rw [hmap] at hinv
    exact hinv
  exact hzero ▸ hcont

/-- There is a neighbourhood of `q` in the flow-box target whose inverse time coordinate has
absolute value `< eps`. -/
theorem exists_target_nhds_time_small
    (R : CanonicalFlowBoxRegularity D q)
    (hne : field q ≠ 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ U : Set Phase2,
      U ∈ 𝓝 q ∧ U ⊆ (R.localHomeomorph hne).target ∧
      ∀ y ∈ U, |((R.localHomeomorph hne).symm y) 0| < eps := by
  let V : Set Phase2 := {z | |z 0| < eps}
  have hV : V ∈ 𝓝 (0 : Phase2) := by
    -- `continuous_apply` is for bare pi types; on `EuclideanSpace` use the bundled
    -- coordinate projection.
    have hcont : Continuous fun z : Phase2 => z 0 :=
      (EuclideanSpace.proj (0 : Fin 2)).continuous
    have hopen : IsOpen {r : ℝ | |r| < eps} := isOpen_lt continuous_abs continuous_const
    have hzero : (0 : ℝ) ∈ {r : ℝ | |r| < eps} := by simpa using heps
    exact (hopen.mem_nhds hzero) |> (hcont.continuousAt.preimage_mem_nhds)
  have hinv := (R.inverse_tendsto_zero hne).eventually hV
  have htgt : (R.localHomeomorph hne).target ∈ 𝓝 q :=
    (R.localHomeomorph hne).open_target.mem_nhds (R.q_mem_target hne)
  refine ⟨(R.localHomeomorph hne).target ∩
      ((R.localHomeomorph hne).symm ⁻¹' V), ?_, ?_, ?_⟩
  · exact inter_mem htgt hinv
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

/-- A late near-return lying in the flow-box target produces a genuine canonical-section hit.

The result records the exact relation `s = T - tau` between global return time and local flow-box
time. -/
theorem sectionHit_of_target_return
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    {T : ℝ≥0}
    (hy : D.flow T q ∈ (R.localHomeomorph hne).target) :
    ∃ tau u : ℝ,
      D.trajectory q ((T : ℝ) - tau) = canonicalSectionPoint field q u ∧
      tau = ((R.localHomeomorph hne).symm (D.flow T q)) 0 ∧
      u = ((R.localHomeomorph hne).symm (D.flow T q)) 1 := by
  let z : Phase2 := (R.localHomeomorph hne).symm (D.flow T q)
  have hzsrc : z ∈ (R.localHomeomorph hne).source :=
    (R.localHomeomorph hne).map_target hy
  have hforward : canonicalFlowBoxMap D q z = D.flow T q := by
    -- `hy` is *target* membership, so this is `right_inv`, not `left_inv`
    have hleft := (R.localHomeomorph hne).right_inv hy
    simpa [z, CanonicalFlowBoxRegularity.localHomeomorph] using hleft
  have htarget :
      D.trajectory (canonicalSectionPoint field q (z 1)) (z 0) =
        D.trajectory q (T : ℝ) := by
    simpa [canonicalFlowBoxMap, D.flow_eq_trajectory] using hforward
  have hshift := D.trajectory_noCrossing hsmooth htarget (-z 0)
  have hhit :
      D.trajectory (canonicalSectionPoint field q (z 1)) 0 =
        D.trajectory q ((T : ℝ) - z 0) := by
    simpa [sub_eq_add_neg, add_assoc, add_comm] using hshift
  refine ⟨z 0, z 1, ?_, rfl, rfl⟩
  simpa [D.trajectory_zero] using hhit.symm

/-- **Arbitrarily late genuine transversal returns.**  From recurrence of `q` in a minimal omega
set and local flow-box regularity, for every requested lower bound `T0` there is a later positive
intersection of the orbit of `q` with the canonical section through `q`. -/
theorem exists_late_canonicalSectionHit
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field)
    (T0 : ℝ) :
    ∃ H : CanonicalSectionHit D q, T0 < H.time := by
  have hne : field q ≠ 0 := M.equilibriumFree q hq
  obtain ⟨U, hU, hUtgt, hUsmall⟩ :=
    R.exists_target_nhds_time_small hne (eps := 1) one_pos
  -- `max 0` is too weak: it only gives `T ≥ 0`, and with `|tau| < 1` that allows
  -- `T - tau < 0`.  Taking `max 1` forces `T ≥ 1 > tau`, hence `T - tau > 0`.
  let A : ℝ≥0 := ⟨max 1 (T0 + 2), le_trans zero_le_one (le_max_left _ _)⟩
  obtain ⟨T, hAT, hTU⟩ := M.exists_late_return hq hU A
  have htarget : D.flow T q ∈ (R.localHomeomorph hne).target := hUtgt hTU
  obtain ⟨tau, u, hhit, htau, hu⟩ :=
    R.sectionHit_of_target_return hsmooth hne htarget
  have htausmall : |tau| < 1 := by
    rw [htau]
    exact hUsmall _ hTU
  have hTlarge : T0 + 2 ≤ (T : ℝ) := by
    have hA : T0 + 2 ≤ (A : ℝ) := by
      dsimp [A]
      exact le_max_right _ _
    exact hA.trans (by exact_mod_cast hAT)
  have htime : T0 < (T : ℝ) - tau := by
    -- `lt_of_abs_lt` yields a single `<`; the conjunction comes from `abs_lt`
    have htau_lt : tau < 1 := (abs_lt.mp htausmall).2
    linarith
  have hTone : (1 : ℝ) ≤ (T : ℝ) := by
    have h1 : (1 : ℝ) ≤ (A : ℝ) := by
      dsimp [A]
      exact le_max_left _ _
    exact h1.trans (by exact_mod_cast hAT)
  have htau_lt' : tau < 1 := (abs_lt.mp htausmall).2
  have hpos : 0 < (T : ℝ) - tau := by linarith
  let H : CanonicalSectionHit D q :=
    { time := (T : ℝ) - tau
      scalar := u
      time_pos := hpos
      hit := hhit }
  exact ⟨H, htime⟩

end CanonicalFlowBoxRegularity

end Planar
end CRNT

namespace CRNT

-- the second namespace block needs the same scoped opens as the first
open Filter Topology
open scoped NNReal

namespace Planar
namespace CanonicalFlowBoxRegularity

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {M : MinimalOmegaData D} {q : Phase2}

/-- Shrink the local target so both canonical flow-box coordinates are uniformly small. -/
theorem exists_target_nhds_coords_small
    (R : CanonicalFlowBoxRegularity D q)
    (hne : field q ≠ 0) {eps : ℝ} (heps : 0 < eps) :
    ∃ U : Set Phase2,
      U ∈ 𝓝 q ∧ U ⊆ (R.localHomeomorph hne).target ∧
      ∀ y ∈ U,
        |((R.localHomeomorph hne).symm y) 0| < eps ∧
        |((R.localHomeomorph hne).symm y) 1| < eps := by
  let V : Set Phase2 := {z | |z 0| < eps ∧ |z 1| < eps}
  have hV : V ∈ 𝓝 (0 : Phase2) := by
    have h0 : {z : Phase2 | |z 0| < eps} ∈ 𝓝 (0 : Phase2) := by
      exact (isOpen_lt ((EuclideanSpace.proj (0 : Fin 2)).continuous.abs) continuous_const).mem_nhds (by simpa using heps)
    have h1 : {z : Phase2 | |z 1| < eps} ∈ 𝓝 (0 : Phase2) := by
      exact (isOpen_lt ((EuclideanSpace.proj (1 : Fin 2)).continuous.abs) continuous_const).mem_nhds (by simpa using heps)
    exact inter_mem h0 h1
  have hinv := (R.inverse_tendsto_zero hne).eventually hV
  have htgt : (R.localHomeomorph hne).target ∈ 𝓝 q :=
    (R.localHomeomorph hne).open_target.mem_nhds (R.q_mem_target hne)
  refine ⟨(R.localHomeomorph hne).target ∩
      ((R.localHomeomorph hne).symm ⁻¹' V), inter_mem htgt hinv, ?_, ?_⟩
  · intro y hy; exact hy.1
  · intro y hy; exact hy.2

/-- Arbitrarily late canonical section hits can be chosen with arbitrarily small scalar coordinate. -/
theorem exists_late_canonicalSectionHit_smallScalar
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field)
    {eps : ℝ} (heps : 0 < eps) (T0 : ℝ) :
    ∃ H : CanonicalSectionHit D q, T0 < H.time ∧ |H.scalar| < eps := by
  have hne : field q ≠ 0 := M.equilibriumFree q hq
  obtain ⟨U, hU, hUtgt, hUsmall⟩ := R.exists_target_nhds_coords_small hne heps
  -- `max 0` only gives `T ≥ 0`, but `tau < eps` needs `T ≥ eps` for `0 < T - tau`.
  let A : ℝ≥0 := ⟨max eps (T0 + eps + 2), le_trans heps.le (le_max_left _ _)⟩
  obtain ⟨T, hAT, hTU⟩ := M.exists_late_return hq hU A
  have htarget := hUtgt hTU
  obtain ⟨tau, u, hhit, htau, hu⟩ :=
    R.sectionHit_of_target_return hsmooth hne htarget
  have hsmall := hUsmall _ hTU
  have htausmall : |tau| < eps := by simpa [htau] using hsmall.1
  have husmall : |u| < eps := by simpa [hu] using hsmall.2
  have hTlarge : T0 + eps + 2 ≤ (T : ℝ) := by
    have hA : T0 + eps + 2 ≤ (A : ℝ) := by
      dsimp [A]; exact le_max_right _ _
    exact hA.trans (by exact_mod_cast hAT)
  have htau_lt : tau < eps := (abs_lt.mp htausmall).2
  have hTeps : eps ≤ (T : ℝ) := by
    have h1 : eps ≤ (A : ℝ) := by
      dsimp [A]; exact le_max_left _ _
    exact h1.trans (by exact_mod_cast hAT)
  have htime : T0 < (T : ℝ) - tau := by linarith
  have hpos : 0 < (T : ℝ) - tau := by linarith
  refine ⟨{
    time := (T : ℝ) - tau
    scalar := u
    time_pos := hpos
    hit := hhit }, htime, husmall⟩

end CanonicalFlowBoxRegularity
end Planar
end CRNT
