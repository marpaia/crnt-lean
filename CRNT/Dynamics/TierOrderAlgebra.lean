import CRNT.Dynamics.TierPersistence

/-!
# Algebra of tier comparisons

The tier relation is defined by limits of positive monomial ratios.  On a positive sequence the
expected preorder algebra is therefore ordinary multiplication/inversion of limits.  The original
paper uses these facts silently throughout Lemmas 4.4--4.6; keeping them explicit makes the
formal domination argument substantially cleaner.
-/

open Filter
open scoped Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem tierMonomial_pos_of_positiveSequence {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) (n : ℕ) (y : Complex S) :
    0 < tierMonomial (xs n) y := by
  simpa [tierMonomial, Complex.massActionMonomial] using Complex.massActionMonomial_pos (hpos n) y

/-- Same-tier comparison is reflexive on positive sequences. -/
theorem tierSame_refl {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    (y : Complex S) : TierSame xs y y := by
  refine ⟨1, zero_lt_one, ?_⟩
  have hdiv : ∀ n, tierMonomial (xs n) y / tierMonomial (xs n) y = 1 := fun n =>
    div_self (tierMonomial_pos_of_positiveSequence hpos n y).ne'
  simpa [hdiv] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- Same-tier comparison is symmetric. -/
theorem TierSame.symm {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y y' : Complex S} (h : TierSame xs y y') : TierSame xs y' y := by
  obtain ⟨c, hc, hlim⟩ := h
  refine ⟨c⁻¹, inv_pos.mpr hc, ?_⟩
  have hinv : Tendsto
      (fun n => (tierMonomial (xs n) y / tierMonomial (xs n) y')⁻¹)
      atTop (𝓝 c⁻¹) := hlim.inv₀ hc.ne'
  apply hinv.congr'
  exact Filter.Eventually.of_forall fun n => by
    have hy := tierMonomial_pos_of_positiveSequence hpos n y
    have hy' := tierMonomial_pos_of_positiveSequence hpos n y'
    field_simp [hy.ne', hy'.ne']

/-- Same-tier comparison is transitive. -/
theorem TierSame.trans {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y₁ y₂ y₃ : Complex S} (h12 : TierSame xs y₁ y₂) (h23 : TierSame xs y₂ y₃) :
    TierSame xs y₁ y₃ := by
  obtain ⟨c12, hc12, hlim12⟩ := h12
  obtain ⟨c23, hc23, hlim23⟩ := h23
  refine ⟨c12 * c23, mul_pos hc12 hc23, ?_⟩
  have hmul := hlim12.mul hlim23
  apply hmul.congr'
  exact Filter.Eventually.of_forall fun n => by
    have h1 := tierMonomial_pos_of_positiveSequence hpos n y₁
    have h2 := tierMonomial_pos_of_positiveSequence hpos n y₂
    have h3 := tierMonomial_pos_of_positiveSequence hpos n y₃
    field_simp [h1.ne', h2.ne', h3.ne']

/-- Strict-below comparison is transitive. -/
theorem TierStrictBelow.trans {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y₁ y₂ y₃ : Complex S} (h12 : TierStrictBelow xs y₁ y₂)
    (h23 : TierStrictBelow xs y₂ y₃) : TierStrictBelow xs y₁ y₃ := by
  have hmul := h12.mul h23
  simpa only [TierStrictBelow, zero_mul] using hmul.congr' (Filter.Eventually.of_forall fun n => by
    have h1 := tierMonomial_pos_of_positiveSequence hpos n y₁
    have h2 := tierMonomial_pos_of_positiveSequence hpos n y₂
    have h3 := tierMonomial_pos_of_positiveSequence hpos n y₃
    field_simp [h1.ne', h2.ne', h3.ne'])

/-- Strict-below followed by same-tier remains strict-below. -/
theorem TierStrictBelow.trans_same {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y₁ y₂ y₃ : Complex S} (h12 : TierStrictBelow xs y₁ y₂)
    (h23 : TierSame xs y₂ y₃) : TierStrictBelow xs y₁ y₃ := by
  obtain ⟨c, hc, h23lim⟩ := h23
  have hmul := h12.mul h23lim
  simpa only [TierStrictBelow, zero_mul] using hmul.congr' (Filter.Eventually.of_forall fun n => by
    have h1 := tierMonomial_pos_of_positiveSequence hpos n y₁
    have h2 := tierMonomial_pos_of_positiveSequence hpos n y₂
    have h3 := tierMonomial_pos_of_positiveSequence hpos n y₃
    field_simp [h1.ne', h2.ne', h3.ne'])

/-- Same-tier followed by strict-below remains strict-below. -/
theorem TierSame.trans_strict {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y₁ y₂ y₃ : Complex S} (h12 : TierSame xs y₁ y₂)
    (h23 : TierStrictBelow xs y₂ y₃) : TierStrictBelow xs y₁ y₃ := by
  obtain ⟨c, hc, h12lim⟩ := h12
  have hmul := h12lim.mul h23
  simpa only [TierStrictBelow, mul_zero] using hmul.congr' (Filter.Eventually.of_forall fun n => by
    have h1 := tierMonomial_pos_of_positiveSequence hpos n y₁
    have h2 := tierMonomial_pos_of_positiveSequence hpos n y₂
    have h3 := tierMonomial_pos_of_positiveSequence hpos n y₃
    field_simp [h1.ne', h2.ne', h3.ne'])

/-- Non-strict tier order is transitive on a positive sequence. -/
theorem TierLE.trans {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y₁ y₂ y₃ : Complex S} (h12 : TierLE xs y₁ y₂) (h23 : TierLE xs y₂ y₃) :
    TierLE xs y₁ y₃ := by
  rcases h12 with h12 | h12 <;> rcases h23 with h23 | h23
  · exact Or.inl (h12.trans hpos h23)
  · exact Or.inl (h12.trans_same hpos h23)
  · exact Or.inl (h12.trans_strict hpos h23)
  · exact Or.inr (h12.trans hpos h23)

/-- A strict comparison cannot hold in both directions on a positive sequence. -/
theorem TierStrictBelow.asymm {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    {y y' : Complex S} (h : TierStrictBelow xs y y') : ¬ TierStrictBelow xs y' y := by
  intro hrev
  have hprod := h.mul hrev
  have hone : Tendsto
      (fun n => (tierMonomial (xs n) y / tierMonomial (xs n) y') *
        (tierMonomial (xs n) y' / tierMonomial (xs n) y)) atTop (𝓝 1) := by
    apply tendsto_const_nhds.congr'
    exact Filter.Eventually.of_forall fun n => by
      have hy := tierMonomial_pos_of_positiveSequence hpos n y
      have hy' := tierMonomial_pos_of_positiveSequence hpos n y'
      field_simp [hy.ne', hy'.ne']
  have hzero : Tendsto
      (fun n => (tierMonomial (xs n) y / tierMonomial (xs n) y') *
        (tierMonomial (xs n) y' / tierMonomial (xs n) y)) atTop (𝓝 0) := by
    simpa using hprod
  have : (0 : ℝ) = 1 := tendsto_nhds_unique hzero hone
  norm_num at this

/-- The logarithm of a strict tier ratio tends to `-∞`. -/
theorem TierStrictBelow.log_tendsto_atBot {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (h : TierStrictBelow xs y y') :
    Tendsto (fun n => Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y'))
      atTop atBot := by
  let q : ℕ → ℝ := fun n => tierMonomial (xs n) y / tierMonomial (xs n) y'
  have hqpos : ∀ᶠ n in atTop, q n ∈ Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun n =>
      div_pos (tierMonomial_pos_of_positiveSequence hpos n y)
        (tierMonomial_pos_of_positiveSequence hpos n y')
  have hq : Tendsto q atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨h, hqpos⟩
  exact Real.tendsto_log_nhdsGT_zero.comp hq

/-- The logarithm of a same-tier ratio converges to the logarithm of its positive limit. -/
theorem TierSame.log_tendsto {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (h : TierSame xs y y') :
    ∃ c : ℝ, Tendsto
      (fun n => Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y'))
      atTop (𝓝 c) := by
  obtain ⟨q, hqpos, hq⟩ := h
  refine ⟨Real.log q, ?_⟩
  exact hq.log hqpos.ne'

/-- A non-strict tier ratio is eventually bounded above by a fixed positive constant. -/
theorem TierLE.eventually_ratio_le_const {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (h : TierLE xs y y') :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      tierMonomial (xs n) y / tierMonomial (xs n) y' ≤ C := by
  rcases h with hstrict | hsame
  · refine ⟨1, zero_lt_one, ?_⟩
    exact ((tendsto_order.1 hstrict).2 1 zero_lt_one).mono fun _ h => h.le
  · obtain ⟨c, hc, hlim⟩ := hsame
    refine ⟨c + 1, by linarith, ?_⟩
    exact ((tendsto_order.1 hlim).2 (c + 1) (by linarith)).mono fun _ h => h.le

/-- A same-tier log-ratio is eventually bounded in absolute value. -/
theorem TierSame.eventually_abs_log_le {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (h : TierSame xs y y') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop,
      |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y')| ≤ C := by
  obtain ⟨c, hlog⟩ := TierSame.log_tendsto hpos h
  refine ⟨|c| + 1, by positivity, ?_⟩
  have hev : ∀ᶠ n in atTop,
      |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') - c| < 1 := by
    have hball := hlog (Metric.ball_mem_nhds c zero_lt_one)
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  filter_upwards [hev] with n hn
  have hle : |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y')| ≤
      |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') - c| + |c| := by
    simpa [sub_add_cancel] using abs_add_le
      (Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') - c) c
  linarith

end Network
end CRNT

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A strict tier comparison excludes a same-tier comparison in the opposite direction. -/
theorem TierStrictBelow.not_same_reverse {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (h : TierStrictBelow xs y y') : ¬ TierSame xs y' y := by
  intro hsame
  obtain ⟨c, hc, hlim⟩ := hsame.symm hpos
  have hzero : (0 : ℝ) = c := tendsto_nhds_unique h hlim
  linarith

/-- A strict comparison excludes the full non-strict tier order in the opposite direction. -/
theorem TierStrictBelow.not_tierLE_reverse {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (h : TierStrictBelow xs y y') : ¬ TierLE xs y' y := by
  intro hle
  rcases hle with hrev | hsame
  · exact h.asymm hpos hrev
  · exact h.not_same_reverse hpos hsame

/-- If `y ≤ y'` in the tier preorder, the reverse logarithmic ratio can be shifted by a fixed
nonnegative constant so that it is eventually nonnegative.  This is the finite offset used in
Proposition 4.6 to compare a non-descending reaction against its descending partner. -/
theorem TierLE.exists_nonneg_reverse_log_shift {xs : ℕ → Concentration S}
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (h : TierLE xs y y') :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n in atTop,
      0 ≤ Real.log (tierMonomial (xs n) y' / tierMonomial (xs n) y) + B := by
  rcases h with hstrict | hsame
  · refine ⟨0, le_rfl, ?_⟩
    have hratio : ∀ᶠ n in atTop,
        tierMonomial (xs n) y / tierMonomial (xs n) y' < 1 :=
      (tendsto_order.1 hstrict).2 1 zero_lt_one
    filter_upwards [hratio] with n hn
    have hy : 0 < tierMonomial (xs n) y := tierMonomial_pos_of_positiveSequence hpos n y
    have hy' : 0 < tierMonomial (xs n) y' := tierMonomial_pos_of_positiveSequence hpos n y'
    have hone : 1 < tierMonomial (xs n) y' / tierMonomial (xs n) y := by
      rw [div_lt_one hy'] at hn
      exact (one_lt_div hy).2 hn
    simpa using (Real.log_nonneg hone.le)
  · obtain ⟨a, hlog⟩ := TierSame.log_tendsto hpos hsame
    let B : ℝ := |a| + 1
    refine ⟨B, by dsimp [B]; positivity, ?_⟩
    have hnear : ∀ᶠ n in atTop,
        |Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') - a| < 1 := by
      have hball := hlog (Metric.ball_mem_nhds a zero_lt_one)
      simpa [Metric.mem_ball, Real.dist_eq] using hball
    filter_upwards [hnear] with n hn
    have hy : 0 < tierMonomial (xs n) y := tierMonomial_pos_of_positiveSequence hpos n y
    have hy' : 0 < tierMonomial (xs n) y' := tierMonomial_pos_of_positiveSequence hpos n y'
    have hrevlog :
        Real.log (tierMonomial (xs n) y' / tierMonomial (xs n) y) =
          -Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') := by
      rw [Real.log_div hy'.ne' hy.ne', Real.log_div hy.ne' hy'.ne']
      ring
    rw [hrevlog]
    dsimp [B]
    -- `hn` gives a two-sided bound; the goal needs the *upper* one, plus `a ≤ |a|`.
    rw [abs_lt] at hn
    have ha : a ≤ |a| := le_abs_self a
    have ha' : -a ≤ |a| := neg_le_abs a
    linarith [hn.1, hn.2]

end Network
end CRNT
