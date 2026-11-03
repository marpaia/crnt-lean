import CRNT.Flux.PSemiflow
import CRNT.Equilibria.CompatibilityClass
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Compact stoichiometric classes in conservative CRNs

A strictly positive P-semiflow provides coordinatewise bounds on the nonnegative part
of every stoichiometric compatibility class.  Because that set is also closed in a
finite-dimensional Euclidean space, it is compact.  This is the standard compactness
input used throughout persistence/permanence theory for conservative CRNs.
-/

namespace CRNT
namespace Network

open Filter
open scoped Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Closed nonnegative stoichiometric class. -/
def nonnegativeCompatibilityClass (N : Network S) (x₀ : Concentration S) :
    Set (Concentration S) :=
  {x | N.StoichCompatible x₀ x ∧ x.Nonnegative}

/-- Its strictly positive part is the ordinary positive compatibility class. -/
theorem positiveCompatibilityClass_eq_inter_nonnegative
    (N : Network S) (x₀ : Concentration S) :
    N.positiveCompatibilityClass x₀ =
      N.nonnegativeCompatibilityClass x₀ ∩ {x | x.Positive} := by
  ext x
  constructor
  · intro hx
    exact ⟨⟨hx.1, hx.2.nonnegative⟩, hx.2⟩
  · intro hx
    exact ⟨hx.1.1, hx.2⟩

/-- Stoichiometric compatibility classes are closed affine subspaces. -/
theorem isClosed_compatibilityClass (N : Network S) (x₀ : Concentration S) :
    IsClosed (N.compatibilityClass x₀) := by
  -- the class is the preimage of the (finite-dimensional, hence closed) stoichiometric
  -- subspace under a continuous translation
  have hcont : Continuous (fun x : Concentration S => x - x₀) :=
    continuous_id.sub continuous_const
  exact (Submodule.closed_of_finiteDimensional N.stoichSubspace).preimage hcont

/-- The coordinatewise nonnegative orthant is closed. -/
theorem isClosed_nonnegativeConcentrations :
    IsClosed ({x : Concentration S | x.Nonnegative} : Set (Concentration S)) := by
  have h : IsClosed (⋂ s : S, {x : Concentration S | 0 ≤ x s}) :=
    isClosed_iInter fun s => isClosed_le continuous_const (continuous_apply s)
  simpa only [Concentration.Nonnegative, Set.setOf_forall] using h

/-- The nonnegative compatibility class is closed. -/
theorem isClosed_nonnegativeCompatibilityClass
    (N : Network S) (x₀ : Concentration S) :
    IsClosed (N.nonnegativeCompatibilityClass x₀) := by
  change IsClosed (N.compatibilityClass x₀ ∩ {x : Concentration S | x.Nonnegative})
  exact (N.isClosed_compatibilityClass x₀).inter isClosed_nonnegativeConcentrations

/-- A strict P-semiflow bounds the entire nonnegative compatibility class. -/
theorem isBounded_nonnegativeCompatibilityClass_of_strictPSemiflow
    (N : Network S) {w : S → ℝ} (hw : N.IsStrictPSemiflow w)
    {x₀ : Concentration S} (hx₀ : x₀.Nonnegative) :
    Bornology.IsBounded (N.nonnegativeCompatibilityClass x₀) := by
  apply isBounded_iff_forall_norm_le.2
  let B : ℝ := ∑ s : S, weightedTotal w x₀ / w s
  refine ⟨B, ?_⟩
  intro x hx
  have htot : 0 ≤ weightedTotal w x₀ := by
    unfold weightedTotal
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hw.2 s).le (hx₀ s)
  have hterm_nonneg : ∀ s : S, 0 ≤ weightedTotal w x₀ / w s :=
    fun s => div_nonneg htot (hw.2 s).le
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun s _ => hterm_nonneg s)).2
  intro s
  rw [Real.norm_eq_abs, abs_of_nonneg (hx.2 s)]
  exact (N.coordinate_le_of_strictPSemiflow hw hx₀ hx.2 hx.1 s).trans
    (Finset.single_le_sum (fun t _ => hterm_nonneg t) (Finset.mem_univ s))

/-- **Compactness of conservative stoichiometric classes.** -/
theorem isCompact_nonnegativeCompatibilityClass_of_strictPSemiflow
    (N : Network S) {w : S → ℝ} (hw : N.IsStrictPSemiflow w)
    {x₀ : Concentration S} (hx₀ : x₀.Nonnegative) :
    IsCompact (N.nonnegativeCompatibilityClass x₀) := by
  -- `IsClosed.isCompact_of_isBounded` does not exist; the mathlib 4.31 lemma is the
  -- standalone `isCompact_of_isClosed_isBounded`, taking both facts as arguments.
  exact Metric.isCompact_of_isClosed_isBounded
    (N.isClosed_nonnegativeCompatibilityClass x₀)
    (N.isBounded_nonnegativeCompatibilityClass_of_strictPSemiflow hw hx₀)

/-- Conservative networks have compact nonnegative classes through every nonnegative
initial state. -/
theorem IsConservative.compact_class
    {N : Network S} (hN : N.IsConservative)
    {x₀ : Concentration S} (hx₀ : x₀.Nonnegative) :
    IsCompact (N.nonnegativeCompatibilityClass x₀) := by
  rcases hN with ⟨w, hw⟩
  exact N.isCompact_nonnegativeCompatibilityClass_of_strictPSemiflow hw hx₀

/-- Every sequence in a conservative nonnegative compatibility class has a convergent
subsequence whose limit remains in the same class. -/
theorem exists_convergent_subsequence_in_class
    (N : Network S) {w : S → ℝ} (hw : N.IsStrictPSemiflow w)
    {x₀ : Concentration S} (hx₀ : x₀.Nonnegative)
    (u : ℕ → Concentration S)
    (hu : ∀ n, u n ∈ N.nonnegativeCompatibilityClass x₀) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ x ∈ N.nonnegativeCompatibilityClass x₀,
        Tendsto (u ∘ φ) atTop (𝓝 x) := by
  have hseq := (N.isCompact_nonnegativeCompatibilityClass_of_strictPSemiflow hw hx₀).isSeqCompact
  have hfreq : ∃ᶠ n in Filter.atTop, u n ∈ N.nonnegativeCompatibilityClass x₀ :=
    (Filter.Eventually.of_forall hu).frequently
  obtain ⟨x, hx, φ, hφ, hlim⟩ := hseq.subseq_of_frequently_in hfreq
  exact ⟨φ, hφ, x, hx, hlim⟩

/-- The omega-limit set of a precompact trajectory confined to a conservative class
cannot escape to infinity; all accumulation points remain in the compact class. -/
theorem accumulation_point_mem_conservative_class
    (N : Network S) {w : S → ℝ} (hw : N.IsStrictPSemiflow w)
    {x₀ : Concentration S} (hx₀ : x₀.Nonnegative)
    {x : Concentration S}
    (hacc : x ∈ closure (N.nonnegativeCompatibilityClass x₀)) :
    x ∈ N.nonnegativeCompatibilityClass x₀ := by
  rw [(N.isClosed_nonnegativeCompatibilityClass x₀).closure_eq] at hacc
  exact hacc

end Network
end CRNT
