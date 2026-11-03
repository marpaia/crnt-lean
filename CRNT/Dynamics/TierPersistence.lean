import CRNT.Dynamics.GlobalPermanence
import CRNT.Geometry.EndotacticGlobal
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Separation.Hausdorff

/-!
# Tier infrastructure for strongly-endotactic permanence

This module installs the definitions needed for the Anderson--Cappelletti--Kim--Nguyen tier
route.  It deliberately separates definitions from the hard compactness/dissipation theorem.
No theorem from the literature is installed as an axiom.

For a positive sequence `xₙ`, complexes are compared through their mass-action monomials.
`TierStrictBelow xs y y'` means `xₙ^y / xₙ^y' -> 0`; `TierSame` means the ratio tends to a
finite positive constant.  On a genuine tier sequence these alternatives induce the usual
total preorder of the network's finite occurring complex set.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Mass-action monomial of a complex, defined locally so tiers do not depend on a reaction
index. -/
def tierMonomial (x : Concentration S) (y : Complex S) : ℝ :=
  ∏ s : S, x s ^ y s

/-- `y` lies strictly below `y'` along `xs`: its monomial is asymptotically negligible. -/
def TierStrictBelow (xs : ℕ → Concentration S) (y y' : Complex S) : Prop :=
  Tendsto (fun n => tierMonomial (xs n) y / tierMonomial (xs n) y') atTop (𝓝 0)

/-- `y` and `y'` occupy the same tier: their monomial ratio tends to a finite positive
constant. -/
def TierSame (xs : ℕ → Concentration S) (y y' : Complex S) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Tendsto (fun n => tierMonomial (xs n) y / tierMonomial (xs n) y') atTop (𝓝 c)

/-- The non-strict tier order: `y` is in the same tier as, or a lower tier than, `y'`. -/
def TierLE (xs : ℕ → Concentration S) (y y' : Complex S) : Prop :=
  TierStrictBelow xs y y' ∨ TierSame xs y y'

/-- Every point of the sequence lies in the open positive orthant. -/
def PositiveSequence (xs : ℕ → Concentration S) : Prop :=
  ∀ n, (xs n).Positive

/-- Escape in logarithmic coordinates.  The finite-dimensional `L1` form is equivalent to the
`L∞` escape used in the tier literature and is convenient for a function-valued species vector. -/
def LogEscapes (xs : ℕ → Concentration S) : Prop :=
  ∀ R : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    R ≤ ∑ s : S, |Real.log (xs n s)|

/-- Pairwise tier comparability on the **finite complex set of the network**.  Tier theory
partitions the complexes that actually occur in `N`; it does not quantify over every imaginable
natural-number complex. -/
def TierComparable (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  ∀ y : Complex S, y ∈ N.complexes → ∀ y' : Complex S, y' ∈ N.complexes →
    TierLE xs y y' ∨ TierStrictBelow xs y' y

/-- A network tier sequence: positivity and logarithmic escape together with a total asymptotic
preorder on the finite occurring complex set. -/
def IsTierSequence (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  PositiveSequence xs ∧ LogEscapes xs ∧ N.TierComparable xs

/-- A proper tier sequence stays inside one affine stoichiometric compatibility class. -/
def IsProperTierSequence (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  N.IsTierSequence xs ∧
    ∀ n m : ℕ, (xs n - xs m : Concentration S) ∈ N.stoichSubspace

/-- A transversal tier sequence has a reaction joining two different tiers. -/
def IsTransversalTierSequence (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  N.IsTierSequence xs ∧
    ∃ r : N.R,
      TierStrictBelow xs (N.reaction r).source (N.reaction r).target ∨
      TierStrictBelow xs (N.reaction r).target (N.reaction r).source

/-- A reaction source is in source tier 1 when no reaction source asymptotically dominates it. -/
def IsTopSourceTier (N : Network S) (xs : ℕ → Concentration S) (r : N.R) : Prop :=
  ∀ r' : N.R, TierLE xs (N.reaction r').source (N.reaction r).source

/-- A transversal tier sequence is tier-descending when all reactions from top source tier do
not move upward and at least one moves strictly downward. -/
def IsTierDescendingSequence (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  (∀ r : N.R, N.IsTopSourceTier xs r →
      TierLE xs (N.reaction r).target (N.reaction r).source) ∧
    ∃ r : N.R, N.IsTopSourceTier xs r ∧
      TierStrictBelow xs (N.reaction r).target (N.reaction r).source

/-- Every transversal tier sequence is tier-descending. -/
def TierDescending (N : Network S) : Prop :=
  ∀ xs : ℕ → Concentration S,
    N.IsTransversalTierSequence xs → N.IsTierDescendingSequence xs


/-! ## Directional realization of tier orders

The difficult compactness/subsequence lemma in the tier proof can be isolated cleanly from the
CRNT geometry.  `TierRealizesDirection xs w` says that all asymptotic tier comparisons along `xs`
are represented by the linear functional `w` on complexes.  Once such a witness exists, the
strong-endotactic => tier-descending argument is finite order theory: maximal source tiers are
exactly `w`-maximal sources, and a strict negative `wRate` is exactly a reaction to a lower tier.
-/

/-- A linear functional `w` exactly realizes the tier preorder of a sequence. -/
structure TierRealizesDirection (N : Network S) (xs : ℕ → Concentration S) (w : S → ℝ) : Prop where
  same_iff : ∀ y : Complex S, y ∈ N.complexes → ∀ y' : Complex S, y' ∈ N.complexes →
    (TierSame xs y y' ↔ complexWValue w y = complexWValue w y')
  below_iff : ∀ y : Complex S, y ∈ N.complexes → ∀ y' : Complex S, y' ∈ N.complexes →
    (TierStrictBelow xs y y' ↔ complexWValue w y < complexWValue w y')

/-- A tier sequence has some linear direction representing all of its tier comparisons. -/
def HasTierDirectionWitness (N : Network S) (xs : ℕ → Concentration S) : Prop :=
  ∃ w : S → ℝ, N.TierRealizesDirection xs w

/-- Under an exact direction realization, the non-strict tier order is exactly the ordinary
order of complex potentials. -/
theorem TierRealizesDirection.tierLE_iff {N : Network S} {xs : ℕ → Concentration S}
    {w : S → ℝ} (h : N.TierRealizesDirection xs w)
    (y : Complex S) (hy : y ∈ N.complexes) (y' : Complex S) (hy' : y' ∈ N.complexes) :
    TierLE xs y y' ↔ complexWValue w y ≤ complexWValue w y' := by
  constructor
  · intro hle
    rcases hle with hlt | heq
    · exact ((h.below_iff y hy y' hy').mp hlt).le
    · exact ((h.same_iff y hy y' hy').mp heq).le
  · intro hle
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact Or.inl ((h.below_iff y hy y' hy').mpr hlt)
    · exact Or.inr ((h.same_iff y hy y' hy').mpr heq)

/-- A top source tier is exactly a source maximizing the realizing linear functional. -/
theorem TierRealizesDirection.topSource_iff_maxSource {N : Network S}
    {xs : ℕ → Concentration S} {w : S → ℝ} (h : N.TierRealizesDirection xs w)
    (r : N.R) : N.IsTopSourceTier xs r ↔ N.IsMaxSource w r := by
  constructor
  · intro htop r'
    have hle := (h.tierLE_iff (N.reaction r').source (N.source_mem_complexes r')
      (N.reaction r).source (N.source_mem_complexes r)).mp (htop r')
    simpa only [wValue_eq_complexWValue_source] using hle
  · intro hmax r'
    apply (h.tierLE_iff (N.reaction r').source (N.source_mem_complexes r')
      (N.reaction r).source (N.source_mem_complexes r)).mpr
    simpa only [wValue_eq_complexWValue_source] using hmax r'

/-- A strict tier comparison across one reaction makes the realizing direction
stoichiometrically active. -/
theorem TierRealizesDirection.stoichActive_of_transversal {N : Network S}
    {xs : ℕ → Concentration S} {w : S → ℝ} (h : N.TierRealizesDirection xs w)
    (htrans : N.IsTransversalTierSequence xs) : N.StoichActiveDirection w := by
  obtain ⟨r, hcross⟩ := htrans.2
  refine ⟨r, ?_⟩
  rw [N.wRate_eq_complexWValue_sub w r]
  rcases hcross with hst | hts
  · have hlt := (h.below_iff (N.reaction r).source (N.source_mem_complexes r)
      (N.reaction r).target (N.target_mem_complexes r)).mp hst
    linarith
  · have hlt := (h.below_iff (N.reaction r).target (N.target_mem_complexes r)
      (N.reaction r).source (N.source_mem_complexes r)).mp hts
    linarith

/-- **Finite geometric core of strongly-endotactic => tier descending.**  Once a transversal
tier sequence has an exact linear direction witness, standard strong endotacticity forces all
reactions from the top source tier weakly downward and at least one strictly downward. -/
theorem StronglyEndotacticStd.tierDescendingSequence_of_directionWitness {N : Network S}
    (hse : N.StronglyEndotacticStd) {xs : ℕ → Concentration S}
    (htrans : N.IsTransversalTierSequence xs) {w : S → ℝ}
    (hw : N.TierRealizesDirection xs w) : N.IsTierDescendingSequence xs := by
  have hactive : N.StoichActiveDirection w := hw.stoichActive_of_transversal htrans
  constructor
  · intro r htop
    have hmax : N.IsMaxSource w r := (hw.topSource_iff_maxSource r).mp htop
    have hrate : N.wRate w r ≤ 0 := hse.1 w r hmax
    apply (hw.tierLE_iff (N.reaction r).target (N.target_mem_complexes r)
      (N.reaction r).source (N.source_mem_complexes r)).mpr
    rw [N.wRate_eq_complexWValue_sub w r] at hrate
    linarith
  · obtain ⟨r, hmax, hneg⟩ := hse.2 w hactive
    refine ⟨r, (hw.topSource_iff_maxSource r).mpr hmax, ?_⟩
    apply (hw.below_iff (N.reaction r).target (N.target_mem_complexes r)
      (N.reaction r).source (N.source_mem_complexes r)).mpr
    rw [N.wRate_eq_complexWValue_sub w r] at hneg
    linarith

/-- The exact missing subsequence/direction statement needed to turn strong endotacticity into the
repo's current `TierDescending` definition.  In the literature this is supplied by the finite
logarithmic subsequence decomposition (the tier-direction lemma), not by CRNT-specific dynamics. -/
def EveryTransversalTierSequenceHasDirectionWitness (N : Network S) : Prop :=
  ∀ xs : ℕ → Concentration S, N.IsTransversalTierSequence xs → N.HasTierDirectionWitness xs

/-- Strong endotacticity implies tier descent once the general finite-dimensional tier-direction
subsequence lemma has been established.  This theorem isolates that analytic/compactness obligation
from all reaction-network geometry. -/
theorem StronglyEndotacticStd.tierDescending_of_directionWitnesses {N : Network S}
    (hse : N.StronglyEndotacticStd)
    (hdir : N.EveryTransversalTierSequenceHasDirectionWitness) : N.TierDescending := by
  intro xs htrans
  obtain ⟨w, hw⟩ := hdir xs htrans
  exact hse.tierDescendingSequence_of_directionWitness htrans hw

/-! ## The reverse characterization reduced to exponential-direction realizations -/

/-- A concrete tier sequence realizing one prescribed direction. -/
def HasDirectionalTierRealization (N : Network S) (w : S → ℝ) : Prop :=
  ∃ xs : ℕ → Concentration S,
    N.IsTransversalTierSequence xs ∧ N.TierRealizesDirection xs w

/-- If every stoichiometrically active direction admits a transversal tier realization, then
`TierDescending` implies standard strong endotacticity.  For the published characterization the
realization is the elementary exponential sequence `xₙ(s)=exp(n*w(s))`; separating that elementary
real-analysis lemma keeps the CRNT proof independent of implementation details of exponentials. -/
theorem TierDescending.stronglyEndotacticStd_of_directionalRealizations {N : Network S}
    (htd : N.TierDescending)
    (hreal : ∀ w : S → ℝ, N.StoichActiveDirection w → N.HasDirectionalTierRealization w) :
    N.StronglyEndotacticStd := by
  have hend : N.Endotactic := by
    intro w r hmax
    by_cases hactive : N.StoichActiveDirection w
    · obtain ⟨xs, htrans, hw⟩ := hreal w hactive
      have hdesc := htd xs htrans
      have htop : N.IsTopSourceTier xs r := (hw.topSource_iff_maxSource r).mpr hmax
      have hle := hdesc.1 r htop
      have hpot := (hw.tierLE_iff (N.reaction r).target (N.target_mem_complexes r)
        (N.reaction r).source (N.source_mem_complexes r)).mp hle
      rw [N.wRate_eq_complexWValue_sub w r]
      linarith
    · -- `StoichActiveDirection w` is `∃ r, N.wRate w r ≠ 0`; `push_neg` needs it unfolded
      -- before it can turn the negation into `∀ r, N.wRate w r = 0`.
      simp only [Network.StoichActiveDirection, not_exists, not_ne_iff] at hactive
      exact le_of_eq (hactive r)
  refine ⟨hend, ?_⟩
  intro w hactive
  obtain ⟨xs, htrans, hw⟩ := hreal w hactive
  obtain ⟨r, htop, hbelow⟩ := (htd xs htrans).2
  refine ⟨r, (hw.topSource_iff_maxSource r).mp htop, ?_⟩
  have hlt := (hw.below_iff (N.reaction r).target (N.target_mem_complexes r)
    (N.reaction r).source (N.source_mem_complexes r)).mp hbelow
  rw [N.wRate_eq_complexWValue_sub w r]
  linarith

/-! ## Explicit exponential directional realization

The reverse implication `TierDescending → StronglyEndotacticStd` does not need the difficult
subsequence theorem.  A prescribed direction `w` is realized by the elementary positive sequence

`xₙ(s) = exp(n * w(s))`.

For this sequence every monomial ratio is exactly an exponential of the difference of the two
`w`-potentials.  Hence equal potentials give a finite positive ratio, smaller potential gives ratio
`→ 0`, and larger potential gives ratio `→ +∞`.  A stoichiometrically active `w` is nonzero in at
least one coordinate, so this sequence also escapes in logarithmic coordinates and is transversal.
-/

/-- Exponential concentration sequence realizing a prescribed linear direction.

`noncomputable` because `Real.exp` is. -/
noncomputable def exponentialDirectionSequence (w : S → ℝ) (n : ℕ) : Concentration S :=
  fun s => Real.exp ((n : ℝ) * w s)

/-- Every point of an exponential direction sequence is strictly positive. -/
theorem exponentialDirectionSequence_positive (w : S → ℝ) :
    PositiveSequence (exponentialDirectionSequence w) := by
  intro n s
  exact Real.exp_pos _

/-- The mass-action monomial of an exponential direction sequence is the exponential of the
linear complex potential. -/
theorem tierMonomial_exponentialDirectionSequence (w : S → ℝ) (n : ℕ) (y : Complex S) :
    tierMonomial (exponentialDirectionSequence w n) y =
      Real.exp ((n : ℝ) * complexWValue w y) := by
  simp only [tierMonomial, exponentialDirectionSequence]
  calc
    (∏ s : S, Real.exp ((n : ℝ) * w s) ^ y s)
        = ∏ s : S, Real.exp ((y s : ℝ) * ((n : ℝ) * w s)) := by
            apply Finset.prod_congr rfl
            intro s _
            -- `Real.exp_nat_mul : exp (n * x) = exp x ^ n`; we need the reverse direction to
            -- turn `exp (n * w s) ^ y s` into `exp (y s * (n * w s))`.
            rw [← Real.exp_nat_mul]
    _ = Real.exp (∑ s : S, (y s : ℝ) * ((n : ℝ) * w s)) := by
          simpa using (Real.exp_sum (Finset.univ : Finset S)
            (fun s => (y s : ℝ) * ((n : ℝ) * w s))).symm
    _ = Real.exp ((n : ℝ) * complexWValue w y) := by
          congr 1
          rw [complexWValue, dotProduct, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          simp only [exponentVector]
          ring

/-- Exact monomial-ratio formula for the exponential direction sequence. -/
theorem tierRatio_exponentialDirectionSequence (w : S → ℝ) (n : ℕ)
    (y y' : Complex S) :
    tierMonomial (exponentialDirectionSequence w n) y /
        tierMonomial (exponentialDirectionSequence w n) y' =
      Real.exp ((n : ℝ) * (complexWValue w y - complexWValue w y')) := by
  rw [tierMonomial_exponentialDirectionSequence, tierMonomial_exponentialDirectionSequence]
  rw [← Real.exp_sub]
  congr 1
  ring

/-- Elementary exponential limit classification: `exp(n*d) → 0` exactly when `d < 0`. -/
theorem tendsto_exp_nat_mul_zero_iff (d : ℝ) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * d)) atTop (𝓝 0) ↔ d < 0 := by
  constructor
  · intro h
    rcases lt_trichotomy d 0 with hd | hd | hd
    · exact hd
    · subst d
      have hc : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 0) := by
        simpa using h
      have h10 : (1 : ℝ) = 0 := (tendsto_const_nhds_iff.mp hc)
      norm_num at h10
    · have htop : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * d)) atTop atTop := by
        have hp := tendsto_pow_atTop_atTop_of_one_lt ((Real.one_lt_exp_iff).2 hd)
        simpa only [← Real.exp_nat_mul] using hp
      exact ((not_tendsto_nhds_of_tendsto_atTop htop 0) h).elim
  · intro hd
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one
      (Real.exp_pos d).le ((Real.exp_lt_one_iff).2 hd)
    simpa only [← Real.exp_nat_mul] using hp

/-- `exp(n*d)` has a finite strictly positive limit exactly in the zero-slope case. -/
theorem exists_pos_tendsto_exp_nat_mul_iff (d : ℝ) :
    (∃ c : ℝ, 0 < c ∧ Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * d)) atTop (𝓝 c)) ↔
      d = 0 := by
  constructor
  · rintro ⟨c, hcpos, hc⟩
    rcases lt_trichotomy d 0 with hd | hd | hd
    · have h0 : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * d)) atTop (𝓝 0) :=
        (tendsto_exp_nat_mul_zero_iff d).2 hd
      have hcz : c = 0 := tendsto_nhds_unique hc h0
      linarith
    · exact hd
    · have htop : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * d)) atTop atTop := by
        have hp := tendsto_pow_atTop_atTop_of_one_lt ((Real.one_lt_exp_iff).2 hd)
        simpa only [← Real.exp_nat_mul] using hp
      exact ((not_tendsto_nhds_of_tendsto_atTop htop c) hc).elim
  · intro hd
    subst d
    refine ⟨1, zero_lt_one, ?_⟩
    simpa using (tendsto_const_nhds : Tendsto (fun _n : ℕ => (1 : ℝ)) atTop (𝓝 1))

/-- The exponential sequence exactly realizes all tier comparisons induced by `w`. -/
theorem exponentialDirectionSequence_realizes (N : Network S) (w : S → ℝ) :
    N.TierRealizesDirection (exponentialDirectionSequence w) w := by
  constructor
  · intro y _hy y' _hy'
    rw [TierSame]
    have hfun :
        (fun n : ℕ => tierMonomial (exponentialDirectionSequence w n) y /
          tierMonomial (exponentialDirectionSequence w n) y') =
        (fun n : ℕ => Real.exp ((n : ℝ) *
          (complexWValue w y - complexWValue w y'))) := by
      funext n
      exact tierRatio_exponentialDirectionSequence w n y y'
    rw [hfun, exists_pos_tendsto_exp_nat_mul_iff]
    constructor <;> intro h <;> linarith
  · intro y _hy y' _hy'
    rw [TierStrictBelow]
    have hfun :
        (fun n : ℕ => tierMonomial (exponentialDirectionSequence w n) y /
          tierMonomial (exponentialDirectionSequence w n) y') =
        (fun n : ℕ => Real.exp ((n : ℝ) *
          (complexWValue w y - complexWValue w y'))) := by
      funext n
      exact tierRatio_exponentialDirectionSequence w n y y'
    rw [hfun, tendsto_exp_nat_mul_zero_iff]
    constructor <;> intro h <;> linarith

/-- A stoichiometrically active direction is nonzero in at least one species coordinate. -/
theorem StoichActiveDirection.exists_coord_ne_zero {N : Network S} {w : S → ℝ}
    (hactive : N.StoichActiveDirection w) : ∃ s : S, w s ≠ 0 := by
  obtain ⟨r, hr⟩ := hactive
  by_contra h
  push_neg at h
  apply hr
  simp [wRate, dotProduct, h]

/-- An active exponential direction sequence escapes every bounded set in log coordinates. -/
theorem exponentialDirectionSequence_logEscapes {N : Network S} {w : S → ℝ}
    (hactive : N.StoichActiveDirection w) : LogEscapes (exponentialDirectionSequence w) := by
  obtain ⟨s0, hs0⟩ := hactive.exists_coord_ne_zero
  have habs : 0 < |w s0| := abs_pos.mpr hs0
  intro R
  obtain ⟨N0, hN0⟩ := exists_nat_gt (R / |w s0|)
  refine ⟨N0, ?_⟩
  intro n hn
  have hRN0 : R < (N0 : ℝ) * |w s0| := by
    have := (div_lt_iff₀ habs).mp hN0
    simpa [mul_comm] using this
  have hNn : (N0 : ℝ) * |w s0| ≤ (n : ℝ) * |w s0| := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) habs.le
  have hterm : |Real.log (exponentialDirectionSequence w n s0)| =
      (n : ℝ) * |w s0| := by
    -- the type of the `0 ≤ ↑n` side condition is not determined by unification here,
    -- so state it at `ℝ` explicitly.
    simp [exponentialDirectionSequence, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (n : ℝ) from Nat.cast_nonneg n)]
  have hleSum : |Real.log (exponentialDirectionSequence w n s0)| ≤
      ∑ s : S, |Real.log (exponentialDirectionSequence w n s)| := by
    -- `single_le_sum` cannot infer the summand from the goal alone; name it.
    exact Finset.single_le_sum
      (f := fun s => |Real.log (exponentialDirectionSequence w n s)|)
      (fun s _ => abs_nonneg _) (Finset.mem_univ s0)
  rw [hterm] at hleSum
  linarith

/-- The exponential sequence is tier-comparable on every finite network. -/
theorem exponentialDirectionSequence_tierComparable (N : Network S) (w : S → ℝ) :
    N.TierComparable (exponentialDirectionSequence w) := by
  intro y hy y' hy'
  let hw := N.exponentialDirectionSequence_realizes w
  rcases le_total (complexWValue w y) (complexWValue w y') with hle | hle
  · exact Or.inl ((hw.tierLE_iff y hy y' hy').2 hle)
  · rcases eq_or_lt_of_le hle with heq | hlt
    · exact Or.inl ((hw.tierLE_iff y hy y' hy').2 heq.symm.le)
    · exact Or.inr ((hw.below_iff y' hy' y hy).2 hlt)

/-- An active direction makes its exponential sequence transversal. -/
theorem exponentialDirectionSequence_transversal {N : Network S} {w : S → ℝ}
    (hactive : N.StoichActiveDirection w) :
    ∃ r : N.R,
      TierStrictBelow (exponentialDirectionSequence w) (N.reaction r).source
        (N.reaction r).target ∨
      TierStrictBelow (exponentialDirectionSequence w) (N.reaction r).target
        (N.reaction r).source := by
  obtain ⟨r, hr⟩ := hactive
  refine ⟨r, ?_⟩
  have hpot : complexWValue w (N.reaction r).target ≠
      complexWValue w (N.reaction r).source := by
    intro heq
    apply hr
    rw [N.wRate_eq_complexWValue_sub w r, heq, sub_self]
  let hw := N.exponentialDirectionSequence_realizes w
  rcases lt_or_gt_of_ne hpot with hlt | hgt
  · exact Or.inr ((hw.below_iff (N.reaction r).target (N.target_mem_complexes r)
      (N.reaction r).source (N.source_mem_complexes r)).2 hlt)
  · exact Or.inl ((hw.below_iff (N.reaction r).source (N.source_mem_complexes r)
      (N.reaction r).target (N.target_mem_complexes r)).2 hgt)

/-- **Completed exponential realization lemma.** Every stoichiometrically active direction admits
an explicit transversal tier realization. -/
theorem hasDirectionalTierRealization_exponential (N : Network S) (w : S → ℝ)
    (hactive : N.StoichActiveDirection w) : N.HasDirectionalTierRealization w := by
  refine ⟨exponentialDirectionSequence w, ?_, N.exponentialDirectionSequence_realizes w⟩
  refine ⟨?_, exponentialDirectionSequence_transversal hactive⟩
  exact ⟨exponentialDirectionSequence_positive w,
    exponentialDirectionSequence_logEscapes hactive,
    N.exponentialDirectionSequence_tierComparable w⟩

/-- **Unconditional reverse half of the tier characterization.**  The former realization premise is
now discharged by the explicit exponential sequence. -/
theorem TierDescending.stronglyEndotacticStd {N : Network S} (htd : N.TierDescending) :
    N.StronglyEndotacticStd :=
  htd.stronglyEndotacticStd_of_directionalRealizations
    (fun w hw => N.hasDirectionalTierRealization_exponential w hw)

/-- A convenient exact decomposition of the published strong-endotactic/tier characterization:
prove the general direction-witness subsequence lemma and the exponential directional-realization
lemma, and the CRNT equivalence follows automatically. -/
theorem stronglyEndotacticStd_iff_tierDescending_of_directionLemmas (N : Network S)
    (hdir : N.EveryTransversalTierSequenceHasDirectionWitness)
    (hreal : ∀ w : S → ℝ, N.StoichActiveDirection w → N.HasDirectionalTierRealization w) :
    N.StronglyEndotacticStd ↔ N.TierDescending := by
  constructor
  · intro hse
    exact hse.tierDescending_of_directionWitnesses hdir
  · intro htd
    exact htd.stronglyEndotacticStd_of_directionalRealizations hreal

end Network
end CRNT
