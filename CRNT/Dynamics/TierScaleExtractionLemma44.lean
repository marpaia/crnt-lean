import CRNT.Dynamics.TierScaleDecomposition
import CRNT.Dynamics.ProperTierTransversal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Sequences

/-!
# Lemma 4.4: finite multiscale extraction for tier sequences

This file implements the finite-dimensional multiscale extraction underlying Lemma 4.4 of
Anderson--Cappelletti--Kim--Nguyen.

The construction is deliberately split into two layers.

* `RawScaleDecompositionOn U z` is a purely finite-dimensional statement about a real vector
  sequence `zₙ : S → ℝ` supported on a finite active set `U`.  After a subsequence, it writes

      zₙ = m₀(n) a₀ + ... + m_{p-1}(n) a_{p-1} + ρₙ,

  where `p ≤ |U|`, every `mᵢ → ∞`, later scales are `o` of earlier scales, and `ρₙ` is uniformly
  bounded.  The recursion kills one active coordinate exactly at every nonterminal step.

* Applying the raw theorem to `zₙ = log xₙ` gives a scale decomposition of a tier sequence.
  The tier-specific fields `same_gap_zero` and `strict_first` are *derived* from the asymptotic
  expansion.  They are not assumptions of the extractor.

The important implementation invariant is `scale_control`: every extracted scale is eventually
bounded by a fixed multiple of `1 + ‖zₙ‖`.  If the first-step remainder is `o(m₀)`, this invariant
immediately implies that every recursive scale is `o(m₀)`.  This is the clean mechanism behind
`scale_separated`.
-/

open Filter Set
open scoped BigOperators Topology ENNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Generic finite-dimensional extraction -/

/-- The real log vector associated to a concentration sequence. -/
noncomputable def tierLogVector (xs : ℕ → Concentration S) (n : ℕ) : Concentration S :=
  fun s => Real.log (xs n s)

/-- A vector sequence is supported on a finite active set.  Coordinates outside the active set
are identically zero, not merely asymptotically zero.  Exact support is what makes the recursive
cardinality argument terminate. -/
def SupportedOn (U : Finset S) (z : ℕ → Concentration S) : Prop :=
  ∀ n s, s ∉ U → z n s = 0

/-- Uniform norm boundedness of a vector sequence. -/
def UniformlyBoundedVectorSequence (z : ℕ → Concentration S) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ n, ‖z n‖ ≤ C

/-- Norm escape of a vector sequence. -/
def NormEscapes (z : ℕ → Concentration S) : Prop :=
  Tendsto (fun n => ‖z n‖) atTop atTop

/-- Normalization used at one extraction stage. -/
noncomputable def normalizeVector (z : ℕ → Concentration S) (n : ℕ) : Concentration S :=
  ‖z n‖⁻¹ • z n

/-- The one-step scale attached to a nonzero limiting normalized direction and a pivot coordinate.
Using the pivot coordinate, rather than simply the norm, makes the new residual exactly zero at the
pivot. -/
noncomputable def pivotScale (z : ℕ → Concentration S) (a : Concentration S) (s₀ : S)
    (n : ℕ) : ℝ :=
  z n s₀ / a s₀

/-- Remainder after removing one asymptotic scale. -/
noncomputable def pivotRemainder (z : ℕ → Concentration S) (a : Concentration S) (s₀ : S)
    (n : ℕ) : Concentration S :=
  z n - pivotScale z a s₀ n • a

/-- A raw finite multiscale expansion on an active coordinate set.  Unlike
`TierScaleDecomposition`, zero levels are allowed: that is precisely the terminal bounded case of
the recursion. -/
structure RawScaleDecompositionOn (U : Finset S) (z : ℕ → Concentration S) where
  levels : ℕ
  levels_le_active : levels ≤ U.card
  scale : Fin levels → ℕ → ℝ
  direction : Fin levels → Concentration S
  residual : ℕ → Concentration S
  scale_pos : ∀ i, ∀ᶠ n in atTop, 0 < scale i n
  scale_escape : ∀ i, Tendsto (scale i) atTop atTop
  scale_separated : ∀ i j, i < j →
    Tendsto (fun n => scale j n / scale i n) atTop (𝓝 0)
  reconstruction : ∀ n,
    z n = (∑ i : Fin levels, scale i n • direction i) + residual n
  residual_bounded : UniformlyBoundedVectorSequence residual
  direction_supported : ∀ i s, s ∉ U → direction i s = 0
  residual_supported : SupportedOn U residual
  /-- Quantitative recursion invariant.  No extracted scale can be larger than the input vector
  norm by more than a fixed multiplicative constant (up to the harmless `+1`). -/
  scale_control : ∀ i, ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
    |scale i n| ≤ C * (1 + ‖z n‖)

/-- Cofinal shifts are strictly increasing. -/
def shiftNat (N : ℕ) : ℕ → ℕ := fun n => n + N

theorem strictMono_shiftNat (N : ℕ) : StrictMono (shiftNat N) := by
  intro a b hab
  dsimp [shiftNat]
  omega

/-- Norm normalization lies in the closed unit ball whenever the vector is nonzero. -/
theorem normalizeVector_mem_closedBall (z : ℕ → Concentration S) (n : ℕ) :
    normalizeVector z n ∈ Metric.closedBall (0 : Concentration S) 1 := by
  rw [Metric.mem_closedBall, dist_zero_right]
  by_cases hz : ‖z n‖ = 0
  · simp [normalizeVector, hz]
  · simp [normalizeVector, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_nonneg (norm_nonneg _), hz]

/-- Along a norm-escaping sequence, normalized vectors eventually have norm exactly one. -/
theorem eventually_norm_normalizeVector_eq_one {z : ℕ → Concentration S}
    (hesc : NormEscapes z) :
    ∀ᶠ n in atTop, ‖normalizeVector z n‖ = 1 := by
  have hpos : ∀ᶠ n in atTop, 0 < ‖z n‖ := (tendsto_atTop.1 hesc 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  filter_upwards [hpos] with n hn
  simp [normalizeVector, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg _), hn.ne']

/-- Compactness of the finite-dimensional closed unit ball gives a convergent normalized
subsequence.  Its limit has norm one. -/
theorem exists_unit_normalized_subsequence {z : ℕ → Concentration S}
    (hesc : NormEscapes z) :
    ∃ a : Concentration S, ‖a‖ = 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a) := by
  have hball : ∀ n, normalizeVector z n ∈ Metric.closedBall (0 : Concentration S) 1 :=
    normalizeVector_mem_closedBall z
  obtain ⟨a, _ha, φ, hφ, hlim⟩ :=
    (isCompact_closedBall (0 : Concentration S) 1).tendsto_subseq hball
  have hone : Tendsto (fun n => ‖normalizeVector z (φ n)‖) atTop (𝓝 1) := by
    have hev : ∀ᶠ n in atTop, ‖normalizeVector z (φ n)‖ = 1 :=
      hφ.tendsto_atTop.eventually (eventually_norm_normalizeVector_eq_one hesc)
    exact (tendsto_congr' hev).mpr tendsto_const_nhds
  have hnorm : ‖a‖ = 1 := tendsto_nhds_unique hlim.norm hone
  exact ⟨a, hnorm, φ, hφ, hlim⟩

/-- A unit finite vector has a nonzero coordinate. -/
theorem exists_ne_zero_coord_of_norm_eq_one {a : Concentration S} (ha : ‖a‖ = 1) :
    ∃ s : S, a s ≠ 0 := by
  by_contra h
  push_neg at h
  have haz : a = 0 := funext h
  simp [haz] at ha

/-- Exact pivot elimination. -/
@[simp] theorem pivotRemainder_pivot_eq_zero (z : ℕ → Concentration S)
    (a : Concentration S) (s₀ : S) (ha : a s₀ ≠ 0) (n : ℕ) :
    pivotRemainder z a s₀ n s₀ = 0 := by
  simp [pivotRemainder, pivotScale, ha]

/-- If an input sequence is supported on `U`, then every pointwise limit of its normalized vectors
is also supported on `U`. -/
theorem normalized_limit_supported {U : Finset S} {z : ℕ → Concentration S}
    (hsupp : SupportedOn U z) {a : Concentration S} {φ : ℕ → ℕ}
    (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a)) :
    ∀ s, s ∉ U → a s = 0 := by
  intro s hs
  have hzero : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hcoord := (tendsto_pi_nhds.mp hlim) s
  have heq : (fun n => normalizeVector z (φ n) s) = fun _n => (0 : ℝ) := by
    funext n
    have hz := hsupp (φ n) s hs
    simp [normalizeVector, hz]
  rw [heq] at hcoord
  exact tendsto_nhds_unique hcoord hzero

/-- Therefore a nonzero pivot chosen from a normalized limit belongs to the active set. -/
theorem pivot_mem_active {U : Finset S} {z : ℕ → Concentration S}
    (hsupp : SupportedOn U z) {a : Concentration S} {φ : ℕ → ℕ}
    (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    {s₀ : S} (ha : a s₀ ≠ 0) : s₀ ∈ U := by
  by_contra hs
  exact ha (normalized_limit_supported hsupp hlim s₀ hs)

/-- The pivot scale is asymptotic to the norm used for normalization. -/
theorem pivotScale_div_norm_tendsto_one {z : ℕ → Concentration S}
    {a : Concentration S} {s₀ : S} (ha : a s₀ ≠ 0)
    {φ : ℕ → ℕ}
    (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    (hesc : NormEscapes (z ∘ φ)) :
    Tendsto (fun n => pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖) atTop (𝓝 1) := by
  have hcoord := (tendsto_pi_nhds.mp hlim) s₀
  have hnormpos : ∀ᶠ n in atTop, 0 < ‖z (φ n)‖ := (tendsto_atTop.1 hesc 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  have hratio : Tendsto
      (fun n => (normalizeVector z (φ n) s₀) / a s₀) atTop (𝓝 1) := by
    simpa [ha] using hcoord.div_const (a s₀)
  apply hratio.congr'
  filter_upwards [hnormpos] with n hn
  simp [pivotScale, normalizeVector, Function.comp_apply, Pi.smul_apply, smul_eq_mul,
    hn.ne', ha]
  field_simp [hn.ne', ha]

/-- The pivot scale is eventually positive. -/
theorem eventually_pivotScale_pos {z : ℕ → Concentration S}
    {a : Concentration S} {s₀ : S} (ha : a s₀ ≠ 0)
    {φ : ℕ → ℕ} (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    (hesc : NormEscapes (z ∘ φ)) :
    ∀ᶠ n in atTop, 0 < pivotScale (z ∘ φ) a s₀ n := by
  have hquot := pivotScale_div_norm_tendsto_one ha hlim hesc
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) < pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖ :=
    (tendsto_order.1 hquot).1 (1 / 2) (by norm_num)
  have hnormpos : ∀ᶠ n in atTop, 0 < ‖z (φ n)‖ := (tendsto_atTop.1 hesc 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  filter_upwards [hhalf, hnormpos] with n hq hn
  have hqpos : 0 < pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖ := by linarith
  have := mul_pos hqpos (show 0 < ‖z (φ n)‖ from hn)
  rwa [div_mul_cancel₀ _ hn.ne'] at this

/-- The pivot scale itself diverges. -/
theorem pivotScale_tendsto_atTop {z : ℕ → Concentration S}
    {a : Concentration S} {s₀ : S} (ha : a s₀ ≠ 0)
    {φ : ℕ → ℕ} (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    (hesc : NormEscapes (z ∘ φ)) :
    Tendsto (pivotScale (z ∘ φ) a s₀) atTop atTop := by
  have hquot := pivotScale_div_norm_tendsto_one ha hlim hesc
  have hhalf : ∀ᶠ n in atTop,
      (1 / 2 : ℝ) ≤ pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖ :=
    ((tendsto_order.1 hquot).1 (1 / 2) (by norm_num)).mono (fun _ h => h.le)
  rw [tendsto_atTop_atTop]
  intro R
  have hnormEv : ∀ᶠ n in atTop, max (2 * R) 1 ≤ ‖z (φ n)‖ :=
    tendsto_atTop.1 hesc (max (2 * R) 1)
  rw [eventually_atTop] at hnormEv hhalf
  obtain ⟨N, hN⟩ := hnormEv
  obtain ⟨M, hM⟩ := hhalf
  refine ⟨max N M, ?_⟩
  intro n hn
  have hnorm := hN n (le_trans (le_max_left _ _) hn)
  have hq := hM n (le_trans (le_max_right _ _) hn)
  have hnormpos : 0 < ‖z (φ n)‖ := lt_of_lt_of_le (by positivity) hnorm
  have hm : (1 / 2 : ℝ) * ‖z (φ n)‖ ≤ pivotScale (z ∘ φ) a s₀ n := by
    have := mul_le_mul_of_nonneg_right hq (norm_nonneg (z (φ n)))
    simpa [Function.comp_apply, hnormpos.ne'] using this
  have : R ≤ (1 / 2 : ℝ) * ‖z (φ n)‖ := by
    have : 2 * R ≤ ‖z (φ n)‖ := (le_max_left (2 * R) 1).trans hnorm
    linarith
  exact this.trans hm

/-- Subtracting the pivot scale times the limiting normalized direction leaves a remainder of
strictly smaller order than the pivot scale. -/
theorem norm_pivotRemainder_div_pivotScale_tendsto_zero
    {z : ℕ → Concentration S} {a : Concentration S} {s₀ : S}
    (ha : a s₀ ≠ 0)
    {φ : ℕ → ℕ} (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    (hesc : NormEscapes (z ∘ φ)) :
    Tendsto
      (fun n => ‖pivotRemainder (z ∘ φ) a s₀ n‖ /
        pivotScale (z ∘ φ) a s₀ n)
      atTop (𝓝 0) := by
  let m : ℕ → ℝ := pivotScale (z ∘ φ) a s₀
  have hmn := pivotScale_div_norm_tendsto_one ha hlim hesc
  have hnm : Tendsto (fun n => ‖z (φ n)‖ / m n) atTop (𝓝 1) := by
    have hinv := hmn.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa [m, inv_div] using hinv
  have hnormpos : ∀ᶠ n in atTop, 0 < ‖z (φ n)‖ := (tendsto_atTop.1 hesc 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  have hmpos : ∀ᶠ n in atTop, 0 < m n := eventually_pivotScale_pos ha hlim hesc
  have hscaled : Tendsto
      (fun n => (‖z (φ n)‖ / m n) •
        (normalizeVector z (φ n) - (m n / ‖z (φ n)‖) • a))
      atTop (𝓝 0) := by
    have hmm : Tendsto (fun n => m n / ‖z (φ n)‖) atTop (𝓝 1) := by
      simpa [m] using hmn
    have hinside : Tendsto
        (fun n => normalizeVector z (φ n) - (m n / ‖z (φ n)‖) • a)
        atTop (𝓝 0) := by
      simpa using hlim.sub (hmm.smul_const a)
    simpa using hnm.smul hinside
  have hnorm0 := hscaled.norm
  simp only [norm_zero] at hnorm0
  apply hnorm0.congr'
  filter_upwards [hnormpos, hmpos] with n hn hm
  -- `normalizeVector z (φ n) - (m n / ‖z (φ n)‖) • a = ‖z (φ n)‖⁻¹ • (z (φ n) - m n • a)`,
  -- so the two scalar factors cancel against each other.
  have hfac : normalizeVector z (φ n) - (m n / ‖z (φ n)‖) • a
      = ‖z (φ n)‖⁻¹ • (z (φ n) - m n • a) := by
    rw [normalizeVector, smul_sub, smul_smul]
    congr 2
    field_simp
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hn hm), hfac, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), pivotRemainder]
  field_simp
  simp only [m, Function.comp_apply]
  rw [mul_div_cancel_left₀ _ hm.ne']

/-- The new remainder stays supported after deleting the pivot coordinate. -/
theorem pivotRemainder_supported_on_erase {U : Finset S} {z : ℕ → Concentration S}
    (hsupp : SupportedOn U z) {a : Concentration S} {φ : ℕ → ℕ}
    (halim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    {s₀ : S} (ha : a s₀ ≠ 0) :
    SupportedOn (U.erase s₀) (pivotRemainder (z ∘ φ) a s₀) := by
  intro n s hs
  rw [Finset.mem_erase] at hs
  push_neg at hs
  -- `hs : s ≠ s₀ → s ∉ U`, so split on whether `s` is the pivot
  by_cases hs0 : s = s₀
  · rw [hs0]
    exact pivotRemainder_pivot_eq_zero (z ∘ φ) a s₀ ha n
  · have hsU : s ∉ U := hs hs0
    have hz : z (φ n) s = 0 := hsupp (φ n) s hsU
    have ha0 : a s = 0 := normalized_limit_supported hsupp halim s hsU
    simp [pivotRemainder, pivotScale, Function.comp_apply, hz, ha0]

/-- Every scalar scale produced from a pivot is eventually controlled by the input norm. -/
theorem pivotScale_control {z : ℕ → Concentration S} {a : Concentration S} {s₀ : S}
    (ha : a s₀ ≠ 0) {φ : ℕ → ℕ}
    (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    (hesc : NormEscapes (z ∘ φ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      |pivotScale (z ∘ φ) a s₀ n| ≤ C * (1 + ‖z (φ n)‖) := by
  refine ⟨2, by norm_num, ?_⟩
  have hq := pivotScale_div_norm_tendsto_one ha hlim hesc
  have hev : ∀ᶠ n in atTop,
      |pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖| ≤ 2 := by
    have hball := hq (Metric.ball_mem_nhds 1 zero_lt_one)
    filter_upwards [hball] with n hn
    rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hn
    have : |pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖| ≤ |1| + 1 := by
      calc
        |pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖|
            ≤ |pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖ - 1| + |1| := by
              simpa [sub_add_cancel] using abs_add_le
                (pivotScale (z ∘ φ) a s₀ n / ‖z (φ n)‖ - 1) 1
        _ ≤ |1| + 1 := by linarith
    norm_num at this ⊢
    exact this
  have hnormpos : ∀ᶠ n in atTop, 0 < ‖z (φ n)‖ := (tendsto_atTop.1 hesc 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  filter_upwards [hev, hnormpos] with n hn hp
  have hmul := mul_le_mul_of_nonneg_right hn (norm_nonneg (z (φ n)))
  rw [abs_div, abs_of_pos hp, div_mul_cancel₀ _ hp.ne'] at hmul
  calc
    |pivotScale (z ∘ φ) a s₀ n| ≤ 2 * ‖z (φ n)‖ := hmul
    _ ≤ 2 * (1 + ‖z (φ n)‖) := by linarith [norm_nonneg (z (φ n))]

/-! ### Compactified norm dichotomy -/

/-- Compactify the nonnegative norm in `ℝ≥0∞`. -/
noncomputable def ennNorm (z : ℕ → Concentration S) (n : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ‖z n‖

/-- Every vector sequence has a subsequence on which the norm either converges to a finite real
number or escapes to infinity. -/
theorem exists_subsequence_norm_bounded_or_escapes (z : ℕ → Concentration S) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (UniformlyBoundedVectorSequence (z ∘ φ) ∨ NormEscapes (z ∘ φ)) := by
  obtain ⟨L, _hL, φ, hφ, hlim⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set ℝ≥0∞)).tendsto_subseq
      (x := fun n => ennNorm z n) (fun _ => Set.mem_univ _)
  by_cases htop : L = ∞
  · refine ⟨φ, hφ, Or.inr ?_⟩
    -- no single Mathlib lemma transports `𝓝 ∞` in `ℝ≥0∞` to `atTop` in `ℝ` here, so do it
    -- directly: eventually the extended norm exceeds `ofReal b`, hence the real norm exceeds `b`.
    have hreal : Tendsto (fun n => ‖z (φ n)‖) atTop atTop := by
      rw [tendsto_atTop]
      intro b
      have hmem : Set.Ioi (ENNReal.ofReal b) ∈ 𝓝 (⊤ : ℝ≥0∞) :=
        Ioi_mem_nhds (by simp [ENNReal.ofReal_lt_top])
      have hlim' : Tendsto (fun n => ENNReal.ofReal ‖z (φ n)‖) atTop (𝓝 (⊤ : ℝ≥0∞)) := by
        simpa [ennNorm, htop, Function.comp_def, ofReal_norm_eq_enorm] using hlim
      filter_upwards [hlim' hmem] with n hn
      have hlt : ENNReal.ofReal b < ENNReal.ofReal ‖z (φ n)‖ := hn
      by_contra hcon
      push_neg at hcon
      exact absurd hlt (not_lt_of_ge (ENNReal.ofReal_le_ofReal hcon.le))
    exact hreal
  · have hreal : Tendsto (fun n => ‖z (φ n)‖) atTop (𝓝 L.toReal) := by
      have hto := (ENNReal.tendsto_toReal htop).comp hlim
      simpa [ennNorm, Function.comp_def, enorm_eq_nnnorm, ENNReal.toReal_ofReal (norm_nonneg _),
        coe_nnnorm] using hto
    let C : ℝ := |L.toReal| + 1
    have hev : ∀ᶠ n in atTop, ‖z (φ n)‖ ≤ C := by
      have hball := hreal (Metric.ball_mem_nhds L.toReal zero_lt_one)
      filter_upwards [hball] with n hn
      rw [Set.mem_preimage, Metric.mem_ball, Real.dist_eq] at hn
      calc
        ‖z (φ n)‖ ≤ |L.toReal| + |‖z (φ n)‖ - L.toReal| := by
          have := abs_add_le L.toReal (‖z (φ n)‖ - L.toReal)
          simpa [abs_of_nonneg (norm_nonneg _), add_sub_cancel_left, add_comm] using this
        _ ≤ C := by dsimp [C]; linarith
    rw [eventually_atTop] at hev
    obtain ⟨N, hN⟩ := hev
    let ψ : ℕ → ℕ := φ ∘ shiftNat N
    refine ⟨ψ, hφ.comp (strictMono_shiftNat N), Or.inl ?_⟩
    refine ⟨C, by dsimp [C]; positivity, ?_⟩
    intro n
    exact hN (n + N) (Nat.le_add_left N n)

/-! ### Prepending one scale to a recursively extracted tower -/

/-- Reindex a tail level as a positive level of `Fin (k+1)`. -/
def tailFin {k : ℕ} (j : Fin k) : Fin (k + 1) :=
  ⟨j.1 + 1, by omega⟩

/-- Split a `Fin (k+1)` into the head or a tail index. -/
def unconsFin {k : ℕ} (i : Fin (k + 1)) : Option (Fin k) :=
  if h : i.1 = 0 then none else some ⟨i.1 - 1, by omega⟩

/-- Scalar `o` plus the recursive scale-control invariant implies every tail scale is `o` of the
new head scale. -/
theorem tail_scale_div_head_tendsto_zero
    {r : ℕ → Concentration S} {m : ℕ → ℝ}
    (hm : Tendsto m atTop atTop)
    (hrm : Tendsto (fun n => ‖r n‖ / m n) atTop (𝓝 0))
    {q : ℕ → ℝ}
    (hq : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, |q n| ≤ C * (1 + ‖r n‖)) :
    Tendsto (fun n => q n / m n) atTop (𝓝 0) := by
  obtain ⟨C, hC, hq⟩ := hq
  have hinv : Tendsto (fun n => (m n)⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hm
  have hsum : Tendsto (fun n => C * ((m n)⁻¹ + ‖r n‖ / m n)) atTop (𝓝 0) := by
    simpa using (hinv.add hrm).const_mul C
  have hmpos : ∀ᶠ n in atTop, 0 < m n :=
    (tendsto_atTop.1 hm 1).mono fun _ h => lt_of_lt_of_le zero_lt_one h
  have habs : ∀ᶠ n in atTop,
      |q n / m n| ≤ C * ((m n)⁻¹ + ‖r n‖ / m n) := by
    filter_upwards [hq, hmpos] with n hqn hmn
    rw [abs_div, abs_of_pos hmn]
    have h := div_le_div_of_nonneg_right hqn hmn.le
    calc
      |q n| / m n ≤ (C * (1 + ‖r n‖)) / m n := h
      _ = C * ((m n)⁻¹ + ‖r n‖ / m n) := by
        field_simp [hmn.ne']
  -- `squeeze_zero'` wants a bound on the function itself; go through the norm version, which
  -- accepts the absolute-value bound directly.
  exact squeeze_zero_norm' (habs.mono fun n h => by simpa [Real.norm_eq_abs, abs_div] using h) hsum

/-- Prepend a first scale to a recursive decomposition of its remainder.  This is the algebraic
flattening step of the recursive construction. -/
noncomputable def RawScaleDecompositionOn.prepend
    {U : Finset S} {z : ℕ → Concentration S}
    {a : Concentration S} {s₀ : S} {φ ψ : ℕ → ℕ}
    (ha : a s₀ ≠ 0)
    (hψ : StrictMono ψ)
    (hlim : Tendsto (fun n => normalizeVector z (φ n)) atTop (𝓝 a))
    (hesc : NormEscapes (z ∘ φ))
    (hpivot : s₀ ∈ U)
    (hsupp : SupportedOn U z)
    (D : RawScaleDecompositionOn (U.erase s₀)
      (pivotRemainder (z ∘ φ) a s₀ ∘ ψ)) :
    RawScaleDecompositionOn U (z ∘ (φ ∘ ψ)) := by
  let m0 : ℕ → ℝ := fun n => pivotScale (z ∘ φ) a s₀ (ψ n)
  let r0 : ℕ → Concentration S := fun n => pivotRemainder (z ∘ φ) a s₀ (ψ n)
  let k := D.levels
  refine
    { levels := k + 1
      levels_le_active := by
        have hk : k ≤ (U.erase s₀).card := D.levels_le_active
        have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨s₀, hpivot⟩
        rw [Finset.card_erase_of_mem hpivot] at hk
        omega
      scale := fun i =>
        if hi : i.1 = 0 then m0 else D.scale ⟨i.1 - 1, by omega⟩
      direction := fun i =>
        if hi : i.1 = 0 then a else D.direction ⟨i.1 - 1, by omega⟩
      residual := D.residual
      scale_pos := ?_
      scale_escape := ?_
      scale_separated := ?_
      reconstruction := ?_
      residual_bounded := D.residual_bounded
      direction_supported := ?_
      residual_supported := ?_
      scale_control := ?_ }
  · intro i
    by_cases hi : i.1 = 0
    · simp only [hi, dite_true]
      exact hψ.tendsto_atTop.eventually (eventually_pivotScale_pos ha hlim hesc)
    · simp only [hi, dite_false]
      exact D.scale_pos ⟨i.1 - 1, by omega⟩
  · intro i
    by_cases hi : i.1 = 0
    · simp only [hi, dite_true, m0]
      exact (pivotScale_tendsto_atTop ha hlim hesc).comp hψ.tendsto_atTop
    · simp only [hi, dite_false]
      exact D.scale_escape ⟨i.1 - 1, by omega⟩
  · intro i j hij
    by_cases hi : i.1 = 0
    · have hij' : i.1 < j.1 := Fin.lt_def.mp hij
      have hj0 : j.1 ≠ 0 := by omega
      simp only [hi, hj0, dite_true, dite_false]
      let jt : Fin k := ⟨j.1 - 1, by omega⟩
      have hrm0 := norm_pivotRemainder_div_pivotScale_tendsto_zero ha hlim hesc
      have hrmψ : Tendsto (fun n => ‖r0 n‖ / m0 n) atTop (𝓝 0) := by
        simpa [r0, m0, Function.comp_def] using hrm0.comp hψ.tendsto_atTop
      have hmψ : Tendsto m0 atTop atTop := by
        simpa [m0, Function.comp_def] using
          (pivotScale_tendsto_atTop ha hlim hesc).comp hψ.tendsto_atTop
      exact tail_scale_div_head_tendsto_zero hmψ hrmψ (D.scale_control jt)
    · have hij' : i.1 < j.1 := Fin.lt_def.mp hij
      have hj : j.1 ≠ 0 := by omega
      simp only [hi, hj, dite_false]
      apply D.scale_separated
      -- both indices are shifted down by one; compare the underlying naturals
      refine Fin.mk_lt_mk.mpr ?_
      omega
  · intro n
    have hzstep : z (φ (ψ n)) = m0 n • a + r0 n := by
      simp [r0, m0, pivotRemainder, Function.comp_apply]
    have htail := D.reconstruction n
    -- `r0` is a local abbreviation for a composition; unfold both sides before rewriting
    simp only [Function.comp_apply] at htail
    simp only [r0, Function.comp_apply] at hzstep
    rw [htail] at hzstep
    -- the goal states the reconstruction with the composition unexpanded
    simp only [Function.comp_apply]
    rw [hzstep]
    ext s
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply]
    rw [Fin.sum_univ_succ]
    simp [m0, k, add_assoc]
  · intro i s hs
    by_cases hi : i.1 = 0
    · simp only [hi, dite_true]
      exact normalized_limit_supported hsupp hlim s hs
    · simp only [hi, dite_false]
      exact D.direction_supported ⟨i.1 - 1, by omega⟩ s (by
        intro hsErase
        exact hs (Finset.mem_of_mem_erase hsErase))
  · intro n s hs
    exact D.residual_supported n s (by
      intro hsErase
      exact hs (Finset.mem_of_mem_erase hsErase))
  · intro i
    by_cases hi : i.1 = 0
    · simp only [hi, dite_true]
      obtain ⟨C, hC, hCtl⟩ := pivotScale_control ha hlim hesc
      refine ⟨C, hC, ?_⟩
      have hCtlψ := hψ.tendsto_atTop.eventually hCtl
      simpa [m0, Function.comp_apply] using hCtlψ
    · simp only [hi, dite_false]
      let it : Fin k := ⟨i.1 - 1, by omega⟩
      obtain ⟨C, hC, hCtl⟩ := D.scale_control it
      have hrm0 := norm_pivotRemainder_div_pivotScale_tendsto_zero ha hlim hesc
      have hsmall : ∀ᶠ n in atTop,
          ‖pivotRemainder (z ∘ φ) a s₀ n‖ ≤ pivotScale (z ∘ φ) a s₀ n := by
        have hle : ∀ᶠ n in atTop,
            ‖pivotRemainder (z ∘ φ) a s₀ n‖ /
              pivotScale (z ∘ φ) a s₀ n ≤ 1 :=
          ((tendsto_order.1 hrm0).2 1 zero_lt_one).mono fun _ h => h.le
        filter_upwards [hle, eventually_pivotScale_pos ha hlim hesc] with n hn hm
        exact (div_le_one hm).mp hn
      obtain ⟨A, hA, hmCtl⟩ := pivotScale_control ha hlim hesc
      refine ⟨C * (1 + A), mul_pos hC (by linarith), ?_⟩
      have hCtl' := hCtl
      have hsmallψ := hψ.tendsto_atTop.eventually hsmall
      have hmCtlψ := hψ.tendsto_atTop.eventually hmCtl
      have hmposψ := hψ.tendsto_atTop.eventually (eventually_pivotScale_pos ha hlim hesc)
      filter_upwards [hCtl', hsmallψ, hmCtlψ, hmposψ] with n hq hr hm hmposn
      calc
        |D.scale it n| ≤ C * (1 + ‖r0 n‖) := hq
        _ ≤ C * (1 + |m0 n|) := by
          have hr' : ‖r0 n‖ ≤ |m0 n| := by
            simpa [r0, m0, Function.comp_apply, abs_of_pos hmposn] using hr
          exact mul_le_mul_of_nonneg_left (by linarith [hr']) hC.le
        _ ≤ (C * (1 + A)) * (1 + ‖z (φ (ψ n))‖) := by
          have hm' : |m0 n| ≤ A * (1 + ‖z (φ (ψ n))‖) := by
            simpa [m0, Function.comp_apply] using hm
          have hznonneg : 0 ≤ ‖z (φ (ψ n))‖ := norm_nonneg _
          nlinarith [hC.le, hA.le]

/-! ### Recursive extractor -/

/-- Terminal raw decomposition for a uniformly bounded sequence. -/
noncomputable def rawScaleDecomposition_bounded {U : Finset S} {z : ℕ → Concentration S}
    (hsupp : SupportedOn U z) (hbdd : UniformlyBoundedVectorSequence z) :
    RawScaleDecompositionOn U z where
  levels := 0
  levels_le_active := Nat.zero_le _
  scale := Fin.elim0
  direction := Fin.elim0
  residual := z
  scale_pos := by intro i; exact Fin.elim0 i
  scale_escape := by intro i; exact Fin.elim0 i
  scale_separated := by intro i; exact Fin.elim0 i
  reconstruction := by intro n; simp
  residual_bounded := hbdd
  direction_supported := by intro i; exact Fin.elim0 i
  residual_supported := hsupp
  scale_control := by intro i; exact Fin.elim0 i

/-- **Generic recursive finite-scale extraction.**  One coordinate is removed at every escaping
stage, so the construction terminates after at most `U.card` stages. -/
theorem exists_rawScaleDecompositionOn
    (U : Finset S) (z : ℕ → Concentration S) (hsupp : SupportedOn U z) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Nonempty (RawScaleDecompositionOn U (z ∘ φ)) := by
  classical
  let P : ℕ → Prop := fun k =>
    ∀ U : Finset S, U.card = k →
      ∀ z : ℕ → Concentration S, SupportedOn U z →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ Nonempty (RawScaleDecompositionOn U (z ∘ φ))
  have hP : ∀ k : ℕ, P k := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
        simp only [P] at ih ⊢
        intro U hUk z hsuppz
        obtain ⟨φ, hφ, hbdd | hesc⟩ := exists_subsequence_norm_bounded_or_escapes z
        · refine ⟨φ, hφ, ⟨rawScaleDecomposition_bounded ?_ hbdd⟩⟩
          intro m s hs
          exact hsuppz (φ m) s hs
        · obtain ⟨a, haNorm, θ, hθ, hlim0⟩ := exists_unit_normalized_subsequence hesc
          let φθ : ℕ → ℕ := φ ∘ θ
          have hφθ : StrictMono φθ := hφ.comp hθ
          have hlim : Tendsto (fun m => normalizeVector z (φθ m)) atTop (𝓝 a) := by
            simpa [φθ, normalizeVector, Function.comp_def] using hlim0
          have hesc0 : NormEscapes (z ∘ φθ) := by
            simpa [φθ, NormEscapes, Function.comp_def] using hesc.comp hθ.tendsto_atTop
          obtain ⟨s₀, ha0⟩ := exists_ne_zero_coord_of_norm_eq_one haNorm
          have hs₀U : s₀ ∈ U := pivot_mem_active hsuppz hlim ha0
          let r : ℕ → Concentration S := pivotRemainder (z ∘ φθ) a s₀
          have hrsupp : SupportedOn (U.erase s₀) r :=
            pivotRemainder_supported_on_erase hsuppz hlim ha0
          have hUpos : 0 < U.card := Finset.card_pos.mpr ⟨s₀, hs₀U⟩
          have hcardErase : (U.erase s₀).card < k := by
            rw [Finset.card_erase_of_mem hs₀U, hUk]
            omega
          obtain ⟨ψ, hψ, ⟨D⟩⟩ :=
            ih (U.erase s₀).card hcardErase (U.erase s₀) rfl r hrsupp
          refine ⟨φθ ∘ ψ, hφθ.comp hψ, ⟨?_⟩⟩
          exact RawScaleDecompositionOn.prepend ha0 hψ hlim hesc0 hs₀U hsuppz D
  exact hP U.card U rfl z hsupp

/-! ## Specialization to logarithmic concentration vectors -/

/-- Log escape in the tier sense forces the Pi norm of the log vector to infinity. -/
theorem norm_tierLogVector_tendsto_atTop {xs : ℕ → Concentration S}
    (hesc : LogEscapes xs) : NormEscapes (tierLogVector xs) := by
  classical
  by_cases hS : Nonempty S
  · have hcard : 0 < (Fintype.card S : ℝ) := by exact_mod_cast Fintype.card_pos
    rw [NormEscapes, tendsto_atTop_atTop]
    intro R
    obtain ⟨N, hN⟩ := hesc ((Fintype.card S : ℝ) * max R 0)
    refine ⟨N, ?_⟩
    intro n hn
    have hlarge := hN n hn
    have hnorm := sum_abs_le_card_mul_norm (tierLogVector xs n)
    have hmul : (Fintype.card S : ℝ) * max R 0 ≤
        (Fintype.card S : ℝ) * ‖tierLogVector xs n‖ := by
      simpa [tierLogVector] using hlarge.trans hnorm
    have hmax := le_of_mul_le_mul_left hmul hcard
    exact (le_max_left R 0).trans hmax
  · haveI : IsEmpty S := not_nonempty_iff.mp hS
    exfalso
    obtain ⟨N, hN⟩ := hesc 1
    have := hN N le_rfl
    exact absurd this (by norm_num)

/-- The log vector is trivially supported on the full species set. -/
theorem tierLogVector_supported_univ (xs : ℕ → Concentration S) :
    SupportedOn (Finset.univ : Finset S) (tierLogVector xs) := by
  intro n s hs
  simp at hs

/-- Raw extraction of an escaping log sequence has at least one scale. -/
theorem RawScaleDecompositionOn.levels_pos_of_normEscapes
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (hesc : NormEscapes z) : 0 < D.levels := by
  by_contra h
  have hz : D.levels = 0 := Nat.eq_zero_of_not_pos h
  obtain ⟨C, hC, hres⟩ := D.residual_bounded
  have hrec : ∀ n, z n = D.residual n := by
    intro n
    have := D.reconstruction n
    -- `simp [hz]` cannot rewrite inside the dependent `Fin D.levels` index type; instead note
    -- the index type is empty and let `simp` discharge the sum.
    have hsum : (∑ i : Fin D.levels, D.scale i n • D.direction i) = 0 := by
      haveI : IsEmpty (Fin D.levels) := hz ▸ (inferInstance : IsEmpty (Fin 0))
      simp
    simpa [hsum] using this
  have hev : ∀ᶠ n in atTop, C + 1 ≤ ‖z n‖ := tendsto_atTop.1 hesc (C + 1)
  obtain ⟨n, hn⟩ := hev.exists
  rw [hrec n] at hn
  have := hres n
  linarith

/-! ## Tier consequences of a raw logarithmic decomposition -/

/-- Pairing of an arbitrary vector with a complex difference. -/
def rawDirectionGap (a : Concentration S) (y y' : Complex S) : ℝ :=
  complexWValue a y - complexWValue a y'

/-- Residual contribution to the logarithm of a monomial ratio. -/
def rawResidualGap {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (y y' : Complex S) (n : ℕ) : ℝ :=
  ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * D.residual n s)

/-- Uniform vector boundedness implies a uniform bound on every fixed residual pairing. -/
theorem RawScaleDecompositionOn.residualGap_bounded
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (y y' : Complex S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n, |rawResidualGap D y y' n| ≤ C := by
  obtain ⟨B, hB, hres⟩ := D.residual_bounded
  let M : ℝ := ∑ s : S, |(y s : ℝ) - (y' s : ℝ)|
  refine ⟨M * B, mul_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _) hB, ?_⟩
  intro n
  calc
    |rawResidualGap D y y' n|
        ≤ ∑ s : S, |((y s : ℝ) - (y' s : ℝ)) * D.residual n s| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ s : S, |(y s : ℝ) - (y' s : ℝ)| * |D.residual n s| := by
          apply Finset.sum_congr rfl
          intro s _
          rw [abs_mul]
    _ ≤ ∑ s : S, |(y s : ℝ) - (y' s : ℝ)| * B := by
          apply Finset.sum_le_sum
          intro s _
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          calc
            |D.residual n s| = ‖D.residual n s‖ := by simp [Real.norm_eq_abs]
            _ ≤ ‖D.residual n‖ := norm_le_pi_norm _ _
            _ ≤ B := hres n
    _ = M * B := by simp [M, Finset.sum_mul]

/-- Exact expansion of a monomial log-ratio from a raw decomposition of the log vector. -/
theorem RawScaleDecompositionOn.logRatio_eq
    {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) (n : ℕ) (y y' : Complex S) :
    Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') =
      (∑ i : Fin D.levels, D.scale i n * rawDirectionGap (D.direction i) y y') +
        rawResidualGap D y y' n := by
  rw [Real.log_div]
  · rw [log_tierMonomial (hpos n), log_tierMonomial (hpos n), ← Finset.sum_sub_distrib]
    have hz := D.reconstruction n
    calc
      (∑ s : S, ((y s : ℝ) * Real.log (xs n s) -
          (y' s : ℝ) * Real.log (xs n s)))
          = ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) * tierLogVector xs n s) := by
              apply Finset.sum_congr rfl
              intro s _
              simp [tierLogVector]
              ring
      _ = ∑ s : S, (((y s : ℝ) - (y' s : ℝ)) *
          ((∑ i : Fin D.levels, D.scale i n • D.direction i) s + D.residual n s)) := by
              apply Finset.sum_congr rfl
              intro s _
              rw [hz]
              simp
      _ = (∑ i : Fin D.levels, D.scale i n * rawDirectionGap (D.direction i) y y') +
          rawResidualGap D y y' n := by
              simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_add,
                Finset.sum_add_distrib, rawResidualGap]
              -- distribute before swapping: `sum_comm` needs a literal double sum
              simp only [Finset.mul_sum]
              rw [Finset.sum_comm]
              congr 1
              apply Finset.sum_congr rfl
              intro i _
              simp only [rawDirectionGap, complexWValue, dotProduct, exponentVector]
              rw [← Finset.sum_sub_distrib, Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro s _
              ring
  · exact (tierMonomial_pos_of_positiveSequence hpos n y).ne'
  · exact (tierMonomial_pos_of_positiveSequence hpos n y').ne'

/-- Bounded residual divided by a divergent scale vanishes. -/
theorem RawScaleDecompositionOn.residualGap_div_scale_tendsto_zero
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (y y' : Complex S) (i : Fin D.levels) :
    Tendsto (fun n => rawResidualGap D y y' n / D.scale i n) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := D.residualGap_bounded y y'
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ fun n => rawResidualGap D y y' n) := by
    refine Filter.isBoundedUnder_of ⟨C, fun (n : ℕ) => ?_⟩
    simpa [Real.norm_eq_abs, Function.comp_apply] using hbound n
  have hinv : Tendsto (fun n => (D.scale i n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (D.scale_escape i)
  have hmul := Filter.isBoundedUnder_le_mul_tendsto_zero hbdd hinv
  apply hmul.congr'
  exact Filter.Eventually.of_forall fun n => by simp [div_eq_mul_inv]

/-- Multiplying a later scale by a fixed scalar does not change its `o` relation to an
earlier scale. -/
theorem RawScaleDecompositionOn.later_mul_div_earlier_tendsto_zero
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) {i j : Fin D.levels} (hij : i < j) (a : ℝ) :
    Tendsto (fun n => (D.scale j n * a) / D.scale i n) atTop (𝓝 0) := by
  have h := (D.scale_separated i j hij).mul_const a
  rw [zero_mul] at h
  apply h.congr'
  exact Filter.Eventually.of_forall fun n => by ring

/-- Later scale contributions vanish after normalization by an earlier scale. -/
theorem RawScaleDecompositionOn.laterGapSum_div_scale_tendsto_zero
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (i : Fin D.levels) (y y' : Complex S) :
    Tendsto
      (fun n =>
        (∑ j : Fin D.levels with i < j,
          D.scale j n * rawDirectionGap (D.direction j) y y') / D.scale i n)
      atTop (𝓝 0) := by
  classical
  let A : Finset (Fin D.levels) := Finset.univ.filter (fun j => i < j)
  have hsum : Tendsto
      (fun n => ∑ j ∈ A,
        (D.scale j n * rawDirectionGap (D.direction j) y y') / D.scale i n)
      atTop (𝓝 0) := by
    have := tendsto_finsetSum A (fun j hj => by
      have hij : i < j := by simpa [A] using (Finset.mem_filter.mp hj).2
      exact D.later_mul_div_earlier_tendsto_zero hij
        (rawDirectionGap (D.direction j) y y'))
    simpa using this
  apply hsum.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp only [A]
    rw [Finset.sum_div]

/-- If all gaps before `i` vanish, the raw logarithmic expansion starts exactly at `i`. -/
theorem RawScaleDecompositionOn.logRatio_eq_from_first
    {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) (n : ℕ) (y y' : Complex S) (i : Fin D.levels)
    (hbefore : ∀ j : Fin D.levels, j < i →
      rawDirectionGap (D.direction j) y y' = 0) :
    Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') =
      (∑ j : Fin D.levels with i ≤ j,
        D.scale j n * rawDirectionGap (D.direction j) y y') +
      rawResidualGap D y y' n := by
  rw [D.logRatio_eq hpos n y y']
  apply congrArg (fun z : ℝ => z + rawResidualGap D y y' n)
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset (Fin D.levels))
    (fun j => i ≤ j)]
  simp only [not_le]
  have hz : ∑ j ∈ Finset.univ.filter (fun j => j < i),
      D.scale j n * rawDirectionGap (D.direction j) y y' = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    simp [hbefore j (Finset.mem_filter.mp hj).2]
  rw [hz, add_zero]

/-- First nonzero direction scale controls the normalized monomial log-ratio. -/
theorem RawScaleDecompositionOn.logRatio_div_scale_tendsto_gap
    {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) (y y' : Complex S) (i : Fin D.levels)
    (hbefore : ∀ j : Fin D.levels, j < i → rawDirectionGap (D.direction j) y y' = 0) :
    Tendsto
      (fun n =>
        Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n)
      atTop (𝓝 (rawDirectionGap (D.direction i) y y')) := by
  classical
  let g := rawDirectionGap (D.direction i) y y'
  have hlater := D.laterGapSum_div_scale_tendsto_zero i y y'
  have hres := D.residualGap_div_scale_tendsto_zero y y' i
  have hlead : Tendsto (fun n => (D.scale i n * g) / D.scale i n) atTop (𝓝 g) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [D.scale_pos i] with n hn
    simp [hn.ne']
  have hsum := (hlead.add hlater).add hres
  -- the assembled limit is `g + 0 + 0`; normalise it to `g` before transferring
  rw [add_zero, add_zero] at hsum
  apply hsum.congr'
  filter_upwards [D.scale_pos i] with n hsi
  rw [D.logRatio_eq_from_first hpos n y y' i hbefore]
  have hsplit :
      (∑ j : Fin D.levels with i ≤ j,
        D.scale j n * rawDirectionGap (D.direction j) y y') =
        D.scale i n * g +
          ∑ j : Fin D.levels with i < j,
            D.scale j n * rawDirectionGap (D.direction j) y y' := by
    -- `{j | i ≤ j}` is `i` inserted into `{j | i < j}`, which splits the sum cleanly
    have hset : (Finset.univ.filter (fun j : Fin D.levels => i ≤ j))
        = insert i (Finset.univ.filter (fun j : Fin D.levels => i < j)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        rcases eq_or_lt_of_le h with h | h
        · exact Or.inl h.symm
        · exact Or.inr h
      · intro h
        rcases h with h | h
        · exact h ▸ le_rfl
        · exact le_of_lt h
    rw [hset, Finset.sum_insert (by simp)]
  rw [hsplit]
  field_simp [hsi.ne']

/-- A bounded real sequence divided by a divergent positive scale tends to zero. -/
theorem bounded_div_escaping_scale_tendsto_zero {f m : ℕ → ℝ}
    (hf : ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, |f n| ≤ C)
    (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => f n / m n) atTop (𝓝 0) := by
  obtain ⟨C, hC, hf⟩ := hf
  have hbdd : IsBoundedUnder (· ≤ ·) atTop (norm ∘ f) :=
    ⟨C, hf.mono fun n hn => by simpa [Function.comp_apply, Real.norm_eq_abs] using hn⟩
  have hinv : Tendsto (fun n => (m n)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hm
  have hmul := Filter.isBoundedUnder_le_mul_tendsto_zero hbdd hinv
  apply hmul.congr'
  exact Filter.Eventually.of_forall fun n => by simp [div_eq_mul_inv]

/-- Least finite scale carrying a nonzero gap. -/
noncomputable def RawScaleDecompositionOn.firstNonzeroGap
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (y y' : Complex S)
    (h : ∃ i : Fin D.levels, rawDirectionGap (D.direction i) y y' ≠ 0) : Fin D.levels :=
  Finset.min' ((Finset.univ : Finset (Fin D.levels)).filter
    (fun i => rawDirectionGap (D.direction i) y y' ≠ 0)) (by
      rcases h with ⟨i, hi⟩
      exact ⟨i, by simp [hi]⟩)

/-- The selected first gap is genuinely nonzero. -/
theorem RawScaleDecompositionOn.firstNonzeroGap_ne_zero
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (y y' : Complex S)
    (h : ∃ i : Fin D.levels, rawDirectionGap (D.direction i) y y' ≠ 0) :
    rawDirectionGap (D.direction (D.firstNonzeroGap y y' h)) y y' ≠ 0 := by
  let A : Finset (Fin D.levels) := (Finset.univ : Finset (Fin D.levels)).filter
    (fun i => rawDirectionGap (D.direction i) y y' ≠ 0)
  have hA : A.Nonempty := by
    rcases h with ⟨i, hi⟩
    exact ⟨i, by simp [A, hi]⟩
  have hmem : D.firstNonzeroGap y y' h ∈ A := by
    dsimp [RawScaleDecompositionOn.firstNonzeroGap]
    exact Finset.min'_mem A hA
  exact (Finset.mem_filter.mp hmem).2

/-- Every earlier gap before `firstNonzeroGap` is zero. -/
theorem RawScaleDecompositionOn.gap_zero_before_firstNonzero
    {U : Finset S} {z : ℕ → Concentration S}
    (D : RawScaleDecompositionOn U z) (y y' : Complex S)
    (h : ∃ i : Fin D.levels, rawDirectionGap (D.direction i) y y' ≠ 0)
    (j : Fin D.levels)
    (hj : j < D.firstNonzeroGap y y' h) :
    rawDirectionGap (D.direction j) y y' = 0 := by
  by_contra hj0
  let A := (Finset.univ : Finset (Fin D.levels)).filter
    (fun i => rawDirectionGap (D.direction i) y y' ≠ 0)
  have hjA : j ∈ A := by simp [A, hj0]
  have hmin := Finset.min'_le A j hjA
  exact (not_le_of_gt hj) hmin


/-- **Same-tier annihilation.**  If any scale gap were nonzero, take its least index.
The normalized log-ratio then converges to that nonzero gap by scale separation.  But the same-tier
log-ratio is bounded, so division by the divergent scale converges to zero. -/
theorem RawScaleDecompositionOn.same_gap_zero
    {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (hsame : TierSame xs y y') :
    ∀ i : Fin D.levels, rawDirectionGap (D.direction i) y y' = 0 := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨i0, hi0⟩ := hnot
  have hex : ∃ i : Fin D.levels,
      rawDirectionGap (D.direction i) y y' ≠ 0 := ⟨i0, hi0⟩
  let i := D.firstNonzeroGap y y' hex
  have hbefore : ∀ j : Fin D.levels, j < i →
      rawDirectionGap (D.direction j) y y' = 0 :=
    D.gap_zero_before_firstNonzero y y' hex
  have hfirst := D.logRatio_div_scale_tendsto_gap hpos y y' i hbefore
  obtain ⟨C, hC, hbounded⟩ := hsame.eventually_abs_log_le hpos
  have hzero : Tendsto
      (fun n =>
        Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n)
      atTop (𝓝 0) :=
    bounded_div_escaping_scale_tendsto_zero ⟨C, hC, hbounded⟩ (D.scale_escape i)
  have hgap0 : rawDirectionGap (D.direction i) y y' = 0 :=
    tendsto_nhds_unique hfirst hzero
  have hne : rawDirectionGap (D.direction i) y y' ≠ 0 :=
    D.firstNonzeroGap_ne_zero y y' hex
  exact hne hgap0

/-- If every scale gap vanished, the strict-tier log ratio would be uniformly bounded by the
residual, contradicting convergence to `-∞`. -/
theorem RawScaleDecompositionOn.exists_nonzero_gap_of_strict
    {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (hstrict : TierStrictBelow xs y y') :
    ∃ i : Fin D.levels, rawDirectionGap (D.direction i) y y' ≠ 0 := by
  by_contra hnone
  push_neg at hnone
  obtain ⟨C, hC, hres⟩ := D.residualGap_bounded y y'
  have heq : ∀ n,
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') =
        rawResidualGap D y y' n := by
    intro n
    rw [D.logRatio_eq hpos n y y']
    have hz : ∑ i : Fin D.levels,
        D.scale i n * rawDirectionGap (D.direction i) y y' = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      simp [hnone i]
    rw [hz, zero_add]
  have hatBot := hstrict.log_tendsto_atBot hpos
  have hsmall : ∀ᶠ n in atTop,
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') ≤ -(C + 1) :=
    tendsto_atBot.1 hatBot (-(C + 1))
  obtain ⟨n, hn⟩ := hsmall.exists
  rw [heq n] at hn
  have habs := hres n
  have hlo : -(C : ℝ) ≤ rawResidualGap D y y' n := (abs_le.mp habs).1
  linarith

/-- The least nonzero gap of a strict tier pair is negative. -/
theorem RawScaleDecompositionOn.firstNonzeroGap_neg_of_strict
    {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (hstrict : TierStrictBelow xs y y') :
    rawDirectionGap (D.direction
      (D.firstNonzeroGap y y' (D.exists_nonzero_gap_of_strict hpos hstrict))) y y' < 0 := by
  let hex := D.exists_nonzero_gap_of_strict hpos hstrict
  let i := D.firstNonzeroGap y y' hex
  have hbefore : ∀ j : Fin D.levels, j < i →
      rawDirectionGap (D.direction j) y y' = 0 :=
    D.gap_zero_before_firstNonzero y y' hex
  have hlim := D.logRatio_div_scale_tendsto_gap hpos y y' i hbefore
  have hnegEventually : ∀ᶠ n in atTop,
      Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n < 0 := by
    have hlogle : ∀ᶠ n in atTop,
        Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') ≤ -1 :=
      tendsto_atBot.1 (hstrict.log_tendsto_atBot hpos) (-1)
    filter_upwards [hlogle, D.scale_pos i] with n hn hm
    have hnneg : Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') < 0 := by
      linarith
    exact div_neg_of_neg_of_pos hnneg hm
  have hle : rawDirectionGap (D.direction i) y y' ≤ 0 := by
    by_contra hnot
    have hposGap : 0 < rawDirectionGap (D.direction i) y y' := lt_of_not_ge hnot
    have hevpos : ∀ᶠ n in atTop,
        0 < Real.log (tierMonomial (xs n) y / tierMonomial (xs n) y') / D.scale i n :=
      (tendsto_order.1 hlim).1 0 hposGap
    obtain ⟨n, hnneg, hnpos⟩ := (hnegEventually.and hevpos).exists
    linarith
  have hne : rawDirectionGap (D.direction i) y y' ≠ 0 :=
    D.firstNonzeroGap_ne_zero y y' hex
  exact lt_of_le_of_ne hle hne

/-- **Strict first-scale property.** -/
theorem RawScaleDecompositionOn.strict_first
    {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) {y y' : Complex S}
    (hstrict : TierStrictBelow xs y y') :
    ∃ i : Fin D.levels,
      (∀ j : Fin D.levels, j < i → rawDirectionGap (D.direction j) y y' = 0) ∧
      rawDirectionGap (D.direction i) y y' < 0 := by
  let hex := D.exists_nonzero_gap_of_strict hpos hstrict
  let i := D.firstNonzeroGap y y' hex
  exact ⟨i, D.gap_zero_before_firstNonzero y y' hex,
    D.firstNonzeroGap_neg_of_strict hpos hstrict⟩

/-! ## Packaging as `TierScaleDecomposition` -/

/-- Convert a positive-level raw logarithmic decomposition into the public Lemma-4.4 structure. -/
noncomputable def RawScaleDecompositionOn.toTierScaleDecomposition
    {N : Network S} {xs : ℕ → Concentration S} {U : Finset S}
    (D : RawScaleDecompositionOn U (tierLogVector xs))
    (hpos : PositiveSequence xs) (hlevels : 0 < D.levels) :
    N.TierScaleDecomposition xs where
  levels := D.levels
  levels_pos := hlevels
  levels_le_species := D.levels_le_active.trans (Finset.card_le_univ U)
  scale := D.scale
  direction := D.direction
  residual := D.residual
  scale_pos := D.scale_pos
  scale_escape := D.scale_escape
  scale_separated := D.scale_separated
  log_eq := by
    intro n s
    have h := congrFun (D.reconstruction n) s
    simpa [tierLogVector, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  residual_bounded := by
    obtain ⟨C, hC, hres⟩ := D.residual_bounded
    refine ⟨C, hC, ?_⟩
    intro n s
    calc
      |D.residual n s| = ‖D.residual n s‖ := by simp [Real.norm_eq_abs]
      _ ≤ ‖D.residual n‖ := norm_le_pi_norm _ _
      _ ≤ C := hres n
  same_gap_zero := by
    intro y y' _hy _hy' hsame i
    simpa [tierDirectionGap, rawDirectionGap] using D.same_gap_zero hpos hsame i
  strict_first := by
    intro y y' _hy _hy' hstrict
    obtain ⟨i, hbefore, hneg⟩ := D.strict_first hpos hstrict
    refine ⟨i, ?_, ?_⟩
    · intro j hj
      simpa [tierDirectionGap, rawDirectionGap] using hbefore j hj
    · simpa [tierDirectionGap, rawDirectionGap] using hneg

/-- **Lemma 4.4.** Every tier sequence has, after subsequence extraction, a finite multiscale
logarithmic decomposition. -/
theorem everyTierSequenceHasScaleDecomposition (N : Network S) :
    N.EveryTierSequenceHasScaleDecomposition := by
  intro xs htier
  let z : ℕ → Concentration S := tierLogVector xs
  obtain ⟨φ, hφ, ⟨Draw⟩⟩ :=
    exists_rawScaleDecompositionOn (Finset.univ : Finset S) z (tierLogVector_supported_univ xs)
  have hposφ : PositiveSequence (xs ∘ φ) := htier.1.comp φ
  have hescφ : LogEscapes (xs ∘ φ) := htier.2.1.comp_strictMono hφ
  have hnormφ : NormEscapes (tierLogVector (xs ∘ φ)) :=
    norm_tierLogVector_tendsto_atTop hescφ
  -- `tierLogVector` commutes with reindexing; transport the raw decomposition along that.
  have hcomp : (fun n => tierLogVector xs (φ n)) = tierLogVector (xs ∘ φ) := by
    funext n s
    simp [tierLogVector, Function.comp_apply]
  have hrawType : RawScaleDecompositionOn (Finset.univ : Finset S)
      (tierLogVector (xs ∘ φ)) := hcomp ▸ Draw
  have hlevels : 0 < hrawType.levels := hrawType.levels_pos_of_normEscapes hnormφ
  exact ⟨φ, hφ, ⟨hrawType.toTierScaleDecomposition hposφ hlevels⟩⟩

/-- Public claim alias, convenient for downstream permanence assembly. -/
theorem everyTierSequenceHasScaleDecomposition_claim (N : Network S) :
    N.EveryTierSequenceHasScaleDecomposition :=
  N.everyTierSequenceHasScaleDecomposition

end Network
end CRNT
