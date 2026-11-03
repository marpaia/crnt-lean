import CRNT.Oscillation.PlanarReturnSequence

/-!
# One-sided recurrent section sequences

A canonical return sequence has scalar coordinates tending to zero.  If any scalar is zero, the
trajectory is already periodic.  Otherwise every return lies strictly on one side or the other of
the base point, and at least one side occurs infinitely often.  This module extracts an increasing
subsequence entirely on that side.
-/

namespace CRNT
namespace Planar

open Filter Topology

/-- Which side of the oriented scalar transversal is visited infinitely often. -/
inductive SectionSide
  | positive
  | negative
  deriving DecidableEq, Repr

/-- A one-sided subsequence of canonical section returns converging to the base point. -/
structure OneSidedReturnSequence {field : Phase2 → Phase2}
    {D : FlowTrappingData field} {q : Phase2}
    (R : CanonicalReturnSequence D q) : Type where
  side : SectionSide
  index : ℕ → ℕ
  index_strictMono : StrictMono index
  side_condition : ∀ n,
    match side with
    | .positive => 0 < (R.hit (index n)).scalar
    | .negative => (R.hit (index n)).scalar < 0

namespace OneSidedReturnSequence

variable {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}
  {R : CanonicalReturnSequence D q}

/-- The extracted scalar subsequence still converges to zero. -/
theorem scalar_tendsto_zero (S : OneSidedReturnSequence R) :
    Tendsto (fun n => (R.hit (S.index n)).scalar) Filter.atTop (𝓝 0) :=
  R.scalar_tendsto_zero.comp S.index_strictMono.tendsto_atTop

/-- Return times along the subsequence remain strictly increasing and diverge along the sequence. -/
theorem time_strictMono (S : OneSidedReturnSequence R) :
    StrictMono (fun n => (R.hit (S.index n)).time) :=
  R.time_strictMono.comp S.index_strictMono

end OneSidedReturnSequence

/-- Indices whose section scalar is positive. -/
def positiveReturnIndices {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}
    (R : CanonicalReturnSequence D q) : Set ℕ :=
  {n | 0 < (R.hit n).scalar}

/-- Indices whose section scalar is negative. -/
def negativeReturnIndices {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}
    (R : CanonicalReturnSequence D q) : Set ℕ :=
  {n | (R.hit n).scalar < 0}

/-- If no scalar is zero, every return index belongs to exactly one side. -/
theorem mem_positive_or_negative
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}
    (R : CanonicalReturnSequence D q)
    (hzero : ∀ n, (R.hit n).scalar ≠ 0) (n : ℕ) :
    n ∈ positiveReturnIndices R ∨ n ∈ negativeReturnIndices R := by
  exact lt_or_gt_of_ne (hzero n).symm

/-- At least one side occurs infinitely often when no return hits the base exactly. -/
theorem infinite_positive_or_negative
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}
    (R : CanonicalReturnSequence D q)
    (hzero : ∀ n, (R.hit n).scalar ≠ 0) :
    (positiveReturnIndices R).Infinite ∨ (negativeReturnIndices R).Infinite := by
  by_contra h
  push_neg at h
  have hfinite : (Set.univ : Set ℕ).Finite := by
    have hcover : (Set.univ : Set ℕ) = positiveReturnIndices R ∪ negativeReturnIndices R := by
      ext n
      simp only [Set.mem_univ, Set.mem_union, true_iff]
      exact mem_positive_or_negative R hzero n
    rw [hcover]
    exact h.1.union h.2
  exact Set.infinite_univ hfinite

/-- Every infinite subset of `ℕ` admits a strictly increasing enumeration. -/
theorem exists_strictMono_enumeration {A : Set ℕ} (hA : A.Infinite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, φ n ∈ A := by
  classical
  let φ : ℕ → ℕ := fun n => Nat.rec
    (Nat.find (hA.exists_gt 0))
    (fun _ k => Nat.find (hA.exists_gt (k + 1))) n
  have hmem : ∀ n, φ n ∈ A := by
    intro n
    cases n with
    | zero => exact (Nat.find_spec (hA.exists_gt 0)).1
    | succ n => exact (Nat.find_spec (hA.exists_gt (φ n + 1))).1
  have hstep : ∀ n, φ n < φ (n+1) := by
    intro n
    have hgt := (Nat.find_spec (hA.exists_gt (φ n + 1))).2
    change φ n < Nat.find (hA.exists_gt (φ n + 1))
    exact lt_trans (Nat.lt_succ_self (φ n)) hgt
  exact ⟨φ, strictMono_nat_of_lt_succ hstep, hmem⟩

/-- **One-sided extraction dichotomy.**  Either a return hits the base point exactly (the periodic
case), or there is an infinite one-sided subsequence approaching it. -/
theorem zeroReturn_or_exists_oneSided
    {field : Phase2 → Phase2} {D : FlowTrappingData field} {q : Phase2}
    (R : CanonicalReturnSequence D q) :
    (∃ n, (R.hit n).scalar = 0) ∨ Nonempty (OneSidedReturnSequence R) := by
  classical
  by_cases hzero : ∃ n, (R.hit n).scalar = 0
  · exact Or.inl hzero
  · right
    have hne : ∀ n, (R.hit n).scalar ≠ 0 := by simpa using hzero
    rcases infinite_positive_or_negative R hne with hpos | hneg
    · obtain ⟨φ, hφ, hmem⟩ := exists_strictMono_enumeration hpos
      exact ⟨{
        side := .positive
        index := φ
        index_strictMono := hφ
        side_condition := fun n => hmem n }⟩
    · obtain ⟨φ, hφ, hmem⟩ := exists_strictMono_enumeration hneg
      exact ⟨{
        side := .negative
        index := φ
        index_strictMono := hφ
        side_condition := fun n => hmem n }⟩

end Planar
end CRNT
