import CRNT.Oscillation.PlanarOneSidedReturns

/-!
# Isolation and successor structure of canonical transversal hits

To use Jordan separation in the Poincare--Bendixson ordering argument we need adjacent, not merely
arbitrarily chosen, transversal crossings.  The signed section function

`h(t) = <trajectory q t - q, field q>`

has derivative `<field(trajectory q t), field q>`.  Near the recurrent base point this derivative
has the same positive sign as `<field q,field q>`, so section zeros there are simple and isolated.
Together with arbitrarily late exact hits, closedness of the zero set produces a next crossing.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open Filter Topology
open scoped InnerProductSpace

namespace Planar

/-- Signed canonical-section coordinate of the recurrent trajectory. -/
noncomputable def sectionCrossingFunction {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (t : ℝ) : ℝ :=
  canonicalSectionCoord field q (D.trajectory q t)

/-- A time is a canonical section hit exactly when the crossing function vanishes. -/
theorem sectionCrossingFunction_eq_zero_iff
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (q : Phase2) (t : ℝ) :
    sectionCrossingFunction D q t = 0 ↔
      D.trajectory q t ∈ canonicalSection field q := by
  rfl

/-- Time derivative of the signed section function. -/
theorem sectionCrossingFunction_hasDerivAt
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (q : Phase2) (t : ℝ) :
    HasDerivAt (sectionCrossingFunction D q)
      ⟪field (D.trajectory q t), field q⟫_ℝ t := by
  unfold sectionCrossingFunction canonicalSectionCoord
  have hsub := (D.trajectory_solution q t).sub_const q
  have hinner := hsub.inner ℝ (hasDerivAt_const t (field q))
  simpa using hinner

/-- Transversality persists in a neighbourhood of a non-equilibrium base point. -/
theorem exists_nhds_positive_canonical_speed
    {field : Phase2 → Phase2} {q : Phase2}
    (hcont : Continuous field) (hne : field q ≠ 0) :
    ∃ U ∈ 𝓝 q, ∀ x ∈ U, 0 < ⟪field x, field q⟫_ℝ := by
  have hpos : 0 < ⟪field q, field q⟫_ℝ := canonical_transversal_speed_pos hne
  have hc : ContinuousAt (fun x => ⟪field x, field q⟫_ℝ) q :=
    hcont.continuousAt.inner continuousAt_const
  have hev : ∀ᶠ x in 𝓝 q, 0 < ⟪field x, field q⟫_ℝ :=
    (continuousAt_const.eventually_lt hc hpos)
  exact ⟨{x | 0 < ⟪field x, field q⟫_ℝ}, hev, fun x hx => hx⟩

/-- While a trajectory stays in the positive-speed neighbourhood, the section coordinate is
strictly increasing in time. -/
theorem strictMonoOn_sectionCrossingFunction
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (q : Phase2)
    {a b : ℝ}
    (hspeed : ∀ t ∈ Set.Icc a b,
      0 < ⟪field (D.trajectory q t), field q⟫_ℝ) :
    StrictMonoOn (sectionCrossingFunction D q) (Set.Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b)
  · intro t ht
    exact (sectionCrossingFunction_hasDerivAt D q t).continuousAt.continuousWithinAt
  · intro t ht
    rw [(sectionCrossingFunction_hasDerivAt D q t).deriv]
    exact hspeed t (interior_subset ht)

/-- A canonical section crossing occurring inside a positive-speed flow box is isolated. -/
theorem sectionHit_isolated
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (q : Phase2)
    (hcont : Continuous field)
    {t₀ : ℝ} (hzero : sectionCrossingFunction D q t₀ = 0)
    (htrans : 0 < ⟪field (D.trajectory q t₀), field q⟫_ℝ) :
    ∃ δ > 0, ∀ t, |t - t₀| < δ →
      sectionCrossingFunction D q t = 0 → t = t₀ := by
  have htraj : ContinuousAt (D.trajectory q) t₀ :=
    (D.trajectory_solution q t₀).continuousAt
  have hspeedCont : ContinuousAt
      (fun t => ⟪field (D.trajectory q t), field q⟫_ℝ) t₀ :=
    (hcont.continuousAt.comp htraj).inner continuousAt_const
  have hspeedEventually : ∀ᶠ t in 𝓝 t₀,
      0 < ⟪field (D.trajectory q t), field q⟫_ℝ :=
    continuousAt_const.eventually_lt hspeedCont htrans
  obtain ⟨δ, hδpos, hδ⟩ := Metric.mem_nhds_iff.mp hspeedEventually
  refine ⟨δ, hδpos, ?_⟩
  intro t ht hzt
  let a := min t t₀
  let b := max t t₀
  have hspeed : ∀ s ∈ Set.Icc a b,
      0 < ⟪field (D.trajectory q s), field q⟫_ℝ := by
    intro s hs
    have hdist : |s - t₀| < δ := by
      rcases le_total t t₀ with hle | hge
      · have hslo : t ≤ s := by simpa [a, b, hle] using hs.1
        have hshi : s ≤ t₀ := by simpa [a, b, hle] using hs.2
        have ht_abs : |t - t₀| = t₀ - t := by
          calc
            |t - t₀| = -(t - t₀) := abs_of_nonpos (sub_nonpos.mpr hle)
            _ = t₀ - t := by ring
        have hs_abs : |s - t₀| = t₀ - s := by
          calc
            |s - t₀| = -(s - t₀) := abs_of_nonpos (sub_nonpos.mpr hshi)
            _ = t₀ - s := by ring
        rw [hs_abs]
        have hleAbs : t₀ - s ≤ |t - t₀| := by rw [ht_abs]; linarith
        linarith
      · have hslo : t₀ ≤ s := by simpa [a, b, hge] using hs.1
        have hshi : s ≤ t := by simpa [a, b, hge] using hs.2
        have ht_abs : |t - t₀| = t - t₀ := abs_of_nonneg (sub_nonneg.mpr hge)
        have hs_abs : |s - t₀| = s - t₀ := abs_of_nonneg (sub_nonneg.mpr hslo)
        rw [hs_abs]
        have hleAbs : s - t₀ ≤ |t - t₀| := by rw [ht_abs]; linarith
        linarith
    have hsball : s ∈ Metric.ball t₀ δ := by
      simpa [Metric.mem_ball, Real.dist_eq] using hdist
    exact hδ hsball
  have hmono := strictMonoOn_sectionCrossingFunction D q hspeed
  by_contra hne_t
  rcases lt_or_gt_of_ne hne_t with hlt | hgt
  · have := hmono (by simp [a, b, hlt.le]) (by simp [a, b, hlt.le]) hlt
    rw [hzt, hzero] at this
    exact lt_irrefl 0 this
  · have := hmono (by simp [a, b, hgt.le]) (by simp [a, b, hgt.le]) hgt
    rw [hzero, hzt] at this
    exact lt_irrefl 0 this

/-- Set of positive canonical-section crossing times after a lower bound. -/
def positiveSectionHitTimes {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (T : ℝ) : Set ℝ :=
  {t | T < t ∧ sectionCrossingFunction D q t = 0}

/-- The section-hit time set is closed away from its strict lower-bound cut. -/
theorem isClosed_sectionZeroSet
    {field : Phase2 → Phase2} (D : FlowTrappingData field) (q : Phase2) :
    IsClosed {t : ℝ | sectionCrossingFunction D q t = 0} := by
  have hcont : Continuous (sectionCrossingFunction D q) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (sectionCrossingFunction_hasDerivAt D q t).continuousAt
  exact isClosed_singleton.preimage hcont

/-- Consecutive canonical section crossings. -/
structure AdjacentSectionHits {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) : Type where
  first : CanonicalSectionHit D q
  second : CanonicalSectionHit D q
  ordered : first.time < second.time
  noHitBetween : ∀ t, first.time < t → t < second.time →
    sectionCrossingFunction D q t ≠ 0

/-- Given one sufficiently local crossing and the existence of arbitrarily late crossings, the
next crossing exists as the infimum of later zero times; isolation makes the infimum strictly later. -/
theorem exists_next_sectionHit
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    {M : MinimalOmegaData D} {q : Phase2}
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (R : CanonicalFlowBoxRegularity D q)
    (hsmooth : ContDiff ℝ 1 field)
    (H : CanonicalSectionHit D q)
    (htrans : 0 < ⟪field (D.trajectory q H.time), field q⟫_ℝ) :
    ∃ H' : CanonicalSectionHit D q,
      H.time < H'.time ∧
      ∀ t, H.time < t → t < H'.time → sectionCrossingFunction D q t ≠ 0 := by
  let A : Set ℝ := {t | H.time < t ∧ sectionCrossingFunction D q t = 0}
  have hAne : A.Nonempty := by
    obtain ⟨K, hK⟩ := R.exists_late_canonicalSectionHit M hq hsmooth (H.time + 1)
    exact ⟨K.time, by
      refine ⟨by linarith, ?_⟩
      rw [sectionCrossingFunction_eq_zero_iff]
      rw [K.hit]
      exact canonicalSectionPoint_mem field q K.scalar⟩
  have hAbdd : BddBelow A := ⟨H.time, by intro t ht; exact ht.1.le⟩
  let tnext := sInf A
  have hge : H.time ≤ tnext := le_csInf hAne (fun t ht => ht.1.le)
  have hgt : H.time < tnext := by
    by_contra hEq
    have heq : tnext = H.time := le_antisymm (le_of_not_gt hEq) hge
    -- Isolation at `H` gives a zero-free right interval, contradicting the defining infimum.
    have hzeroH : sectionCrossingFunction D q H.time = 0 := by
      rw [sectionCrossingFunction_eq_zero_iff, H.hit]
      exact canonicalSectionPoint_mem field q H.scalar
    obtain ⟨δ, hδpos, hiso⟩ := sectionHit_isolated D q
      hsmooth.continuous hzeroH htrans
    have hupper : sInf A < H.time + δ := by rw [← heq]; dsimp [tnext]; linarith
    obtain ⟨t, htA, htlt⟩ := exists_lt_of_csInf_lt hAne hupper
    have htδ : |t - H.time| < δ := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt htA.1))]
      linarith
    exact (ne_of_gt htA.1) (hiso t htδ htA.2)
  have hzeroNext : sectionCrossingFunction D q tnext = 0 := by
    have htnextClosure : tnext ∈ closure A := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hupper : sInf A < tnext + ε := by dsimp [tnext]; linarith
      obtain ⟨t, htA, htlt⟩ := exists_lt_of_csInf_lt hAne hupper
      have hle : tnext ≤ t := csInf_le hAbdd htA
      refine ⟨t, htA, ?_⟩
      rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hle)]
      dsimp [tnext] at htlt ⊢
      linarith
    have hzeroMem : tnext ∈ {t | sectionCrossingFunction D q t = 0} :=
      closure_minimal (fun t ht => ht.2) (isClosed_sectionZeroSet D q) htnextClosure
    exact hzeroMem
  have hpoint : D.trajectory q tnext ∈ canonicalSection field q :=
    (sectionCrossingFunction_eq_zero_iff D q tnext).mp hzeroNext
  let u := canonicalSectionScalar field q (D.trajectory q tnext)
  have hrec : canonicalSectionPoint field q u = D.trajectory q tnext :=
    canonicalSectionPoint_scalar (M.equilibriumFree q hq) hpoint
  let H' : CanonicalSectionHit D q :=
    { time := tnext
      scalar := u
      time_pos := lt_trans H.time_pos hgt
      hit := hrec.symm }
  refine ⟨H', hgt, ?_⟩
  intro t h1 h2 hz
  have htA : t ∈ A := ⟨h1, hz⟩
  exact (not_lt_of_ge (csInf_le hAbdd htA)) h2

end Planar
end CRNT
