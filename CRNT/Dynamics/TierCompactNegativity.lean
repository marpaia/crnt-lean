import CRNT.Dynamics.VariableTierLyapunov
import CRNT.Dynamics.PermanenceAssembly

/-!
# Compact negativity from sequential tier exclusion

Corollary 5.1 of the tier-permanence route is fundamentally a compactness argument.  Once one
knows that an escaping positive sequence with uniformly bounded positive reaction coefficients
cannot keep nonnegative tier dissipation, all points where dissipation is nonnegative must lie in
one compact positive box inside the stoichiometric compatibility class.

This module isolates that network-independent compactness step.  It deliberately does *not* prove
the tier subsequence theorem or Proposition 4.6; those are the remaining CRNT-specific inputs.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Symmetric logarithmic coordinate box `exp(-R) ≤ x_s ≤ exp(R)` for all species. -/
def logBox (R : ℝ) : Set (Concentration S) :=
  coordinateBox (S := S) (Real.exp (-R)) (Real.exp R)

/-- Log boxes are compact. -/
theorem isCompact_logBox (R : ℝ) : IsCompact (logBox (S := S) R) := by
  simpa [logBox] using
    (isCompact_coordinateBox (S := S) (Real.exp (-R)) (Real.exp R))

/-- Every point of a log box is strictly positive. -/
theorem logBox_positive {R : ℝ} {x : Concentration S}
    (hx : x ∈ logBox (S := S) R) : x.Positive := by
  intro s
  exact lt_of_lt_of_le (Real.exp_pos (-R)) (hx s).1

/-- The fixed positive-rate band used by variable-k tier arguments. -/
def RateVectorInBand (N : Network S) (δ : ℝ) (k : N.R → ℝ) : Prop :=
  0 < δ ∧ ∀ r : N.R, δ ≤ k r ∧ k r ≤ δ⁻¹

/-- A sequence of coefficient vectors lies in one fixed positive band. -/
def RateSequenceInBand (N : Network S) (δ : ℝ) (ks : ℕ → N.R → ℝ) : Prop :=
  0 < δ ∧ ∀ n r, δ ≤ ks n r ∧ ks n r ≤ δ⁻¹

/-- Pointwise rate bands induce the sequence-level notion already used in
`UniformTierDissipationEventuallyNegative`. -/
theorem rateSequenceInBand_uniformPositive {N : Network S} {δ : ℝ} {ks : ℕ → N.R → ℝ}
    (h : N.RateSequenceInBand δ ks) : N.UniformPositiveRateSequence ks :=
  ⟨δ, h.1, h.2⟩

/-- A positive point outside the logarithmic box of nonnegative radius `R` has logarithmic
`L1`-size strictly greater than `R`. -/
theorem log_sum_abs_gt_of_not_mem_logBox {R : ℝ} (hR : 0 ≤ R)
    {x : Concentration S} (hxpos : x.Positive) (hx : x ∉ logBox (S := S) R) :
    R < ∑ s : S, |Real.log (x s)| := by
  classical
  simp only [logBox, coordinateBox, Set.mem_setOf_eq] at hx
  push_neg at hx
  obtain ⟨s, hs⟩ := hx
  rw [Set.mem_Icc] at hs
  have habss_nonneg : ∀ u : S, 0 ≤ |Real.log (x u)| := fun _ => abs_nonneg _
  have hterm_le : |Real.log (x s)| ≤ ∑ u : S, |Real.log (x u)| := by
    exact Finset.single_le_sum (fun u _ => habss_nonneg u) (Finset.mem_univ s)
  rcases not_and_or.mp hs with hlo | hhi
  · have hlog : Real.log (x s) < -R := by
      have hxl : x s < Real.exp (-R) := lt_of_not_ge hlo
      have := Real.strictMonoOn_log (Set.mem_Ioi.mpr (hxpos s))
        (Set.mem_Ioi.mpr (Real.exp_pos (-R))) hxl
      simpa using this
    have hneg : Real.log (x s) < 0 := lt_of_lt_of_le hlog (neg_nonpos.mpr hR)
    have : R < |Real.log (x s)| := by
      rw [abs_of_neg hneg]
      linarith
    exact this.trans_le hterm_le
  · have hlog : R < Real.log (x s) := by
      have hxu : Real.exp R < x s := lt_of_not_ge hhi
      have := Real.strictMonoOn_log (Set.mem_Ioi.mpr (Real.exp_pos R))
        (Set.mem_Ioi.mpr (hxpos s)) hxu
      simpa using this
    have hnonneg : 0 ≤ Real.log (x s) := le_trans hR hlog.le
    have : R < |Real.log (x s)| := by simpa [abs_of_nonneg hnonneg] using hlog
    exact this.trans_le hterm_le

/-- Leaving every integer-radius log box forces logarithmic escape.  The hypothesis is deliberately
stronger than `LogEscapes` because it is exactly what is produced by the compactness contradiction:
we choose the `n`th bad state outside the radius-`n` box. -/
theorem logEscapes_of_eventually_not_mem_logBox
    {xs : ℕ → Concentration S} (hpos : PositiveSequence xs)
    (hout : ∀ n : ℕ, xs n ∉ logBox (S := S) (n : ℝ)) : LogEscapes xs := by
  intro R
  obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (max R 0)
  refine ⟨N, ?_⟩
  intro n hn
  have hRn : R < (n : ℝ) := by
    have hNR : R < (N : ℝ) := lt_of_le_of_lt (le_max_left R 0) hN
    exact hNR.trans_le (by exact_mod_cast hn)
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hlog := log_sum_abs_gt_of_not_mem_logBox (S := S) hn0 (hpos n) (hout n)
  exact le_of_lt (hRn.trans hlog)

/-- Sequential exclusion principle needed for the compactness step: in one positive compatibility
class, an escaping state sequence with coefficients staying in one positive compact interval cannot
have nonnegative tier dissipation at every index. -/
def NoEscapingNonnegativeDissipationOnClass (N : Network S) (xref : Concentration S)
    (δ : ℝ) : Prop :=
  ∀ (ks : ℕ → N.R → ℝ) (xs : ℕ → Concentration S),
    N.RateSequenceInBand δ ks →
    (∀ n, xs n ∈ N.positiveCompatibilityClass xref) →
    LogEscapes xs →
    ∃ n : ℕ, N.tierDissipationWith (ks n) (xs n) < 0

/-- **Sequential exclusion implies one compact bad-region enclosure.**

If every logarithmically escaping sequence in the class must contain a point of negative
dissipation, then there is one integer-radius log box outside of which *every* coefficient vector
in the fixed rate band has negative dissipation. -/
theorem exists_logBox_negative_outside_of_noEscaping
    {N : Network S} {xref : Concentration S} {δ : ℝ}
    (hexcl : N.NoEscapingNonnegativeDissipationOnClass xref δ) :
    ∃ R : ℕ, ∀ (k : N.R → ℝ) (x : Concentration S),
      N.RateVectorInBand δ k → x ∈ N.positiveCompatibilityClass xref →
      x ∉ logBox (S := S) (R : ℝ) → N.tierDissipationWith k x < 0 := by
  classical
  by_contra hnot
  push_neg at hnot
  choose ks xs hks hxs hout hnonneg using hnot
  have hδ : 0 < δ := (hks 0).1
  have hks' : N.RateSequenceInBand δ ks := by
    refine ⟨hδ, ?_⟩
    intro n r
    exact (hks n).2 r
  have hpos : PositiveSequence xs := fun n => (hxs n).2
  have hesc : LogEscapes xs :=
    logEscapes_of_eventually_not_mem_logBox (S := S) hpos hout
  obtain ⟨n, hnneg⟩ := hexcl ks xs hks' hxs hesc
  exact (not_lt_of_ge (hnonneg n)) hnneg

/-- **Compact class region outside which tier dissipation is uniformly negative.**

This is the abstract compactness core of Corollary 5.1.  The returned set is a compact subset of
the positive compatibility class, and negativity holds outside it for every reaction coefficient
vector in the prescribed positive band. -/
theorem exists_compact_class_region_negative_outside_of_noEscaping
    {N : Network S} {xref : Concentration S} {δ : ℝ}
    (hexcl : N.NoEscapingNonnegativeDissipationOnClass xref δ) :
    ∃ K : Set (Concentration S), IsCompact K ∧
      K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ (k : N.R → ℝ) (x : Concentration S),
        N.RateVectorInBand δ k → x ∈ N.positiveCompatibilityClass xref → x ∉ K →
          N.tierDissipationWith k x < 0 := by
  obtain ⟨R, hR⟩ := N.exists_logBox_negative_outside_of_noEscaping hexcl
  let K : Set (Concentration S) :=
    N.compatibilityClass xref ∩ logBox (S := S) (R : ℝ)
  refine ⟨K, ?_, ?_, ?_⟩
  · exact (isCompact_logBox (S := S) (R : ℝ)).inter_left
      (N.isClosed_compatibilityClass xref)
  · intro x hx
    exact ⟨hx.1, logBox_positive hx.2⟩
  · intro k x hk hxclass hxnot
    apply hR k x hk hxclass
    intro hxbox
    exact hxnot ⟨hxclass.1, hxbox⟩

end Network
end CRNT
