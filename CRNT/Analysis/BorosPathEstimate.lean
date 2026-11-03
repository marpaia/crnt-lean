import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Logic.Relation

/-!
# A finite path estimate for Boros's single-linkage bound

Along a directed path, Boros's proof accumulates terms of the form
`exp (-y i) * y (i + 1)`. This file gives an explicit finite bound: if the endpoint is
larger than the recursively defined threshold, at least one path term exceeds any prescribed
positive bound. The result is the discrete estimate needed before applying it to a shortest
positive bound. The result is the discrete estimate needed for finite reaction graphs.
-/

namespace CRNT
namespace Analysis

/-- The endpoint bound obtained by iterating `x ↦ b * exp x` from zero. -/
noncomputable def borosWeightedPathBound (b : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => b * Real.exp (borosWeightedPathBound b n)

/-- A directed path equipped with its finite number of edges. -/
inductive BorosDirectedPath {α : Type*} (R : α → α → Prop) : α → α → ℕ → Prop
  | refl (a : α) : BorosDirectedPath R a a 0
  | tail {a b c : α} {n : ℕ} :
      BorosDirectedPath R a b n → R b c → BorosDirectedPath R a c (n + 1)

/-- Forgetting the edge count gives the corresponding reflexive-transitive path. -/
theorem BorosDirectedPath.toReflTransGen {α : Type*} {R : α → α → Prop}
    {a c : α} {n : ℕ} (p : BorosDirectedPath R a c n) :
    Relation.ReflTransGen R a c := by
  induction p with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b c n p hbc ih => exact ih.tail hbc

/-- Every reflexive-transitive reachability witness carries a finite path length. -/
theorem exists_borosDirectedPath_of_reflTransGen {α : Type*} {R : α → α → Prop}
    {a c : α} (h : Relation.ReflTransGen R a c) :
    ∃ n, BorosDirectedPath R a c n := by
  induction h with
  | refl => exact ⟨0, BorosDirectedPath.refl _⟩
  | @tail b c hab hbc ih =>
      rcases ih with ⟨n, p⟩
      exact ⟨n + 1, BorosDirectedPath.tail p hbc⟩

/-- A chosen finite path length for each reachable ordered pair. -/
noncomputable def borosReachabilityPathLength {α : Type*} [Fintype α]
    (R : α → α → Prop) (a c : α) : ℕ := by
  classical
  exact if h : Relation.ReflTransGen R a c then
    Classical.choose (exists_borosDirectedPath_of_reflTransGen h) else 0

/-- A uniform finite path-length bound for every reachable pair in a finite relation. -/
noncomputable def borosUniformReachabilityPathLength {α : Type*} [Fintype α]
    (R : α → α → Prop) : ℕ := by
  classical
  exact Finset.univ.sup fun p : α × α =>
    if h : Relation.ReflTransGen R p.1 p.2 then
      Classical.choose (exists_borosDirectedPath_of_reflTransGen h) else 0

/-- Every reachable pair in a finite type has a path whose length is bounded uniformly over all
ordered pairs. -/
theorem exists_borosDirectedPath_of_reflTransGen_length_le
    {α : Type*} [Fintype α] {R : α → α → Prop} {a c : α}
    (h : Relation.ReflTransGen R a c) :
    ∃ n, n ≤ borosUniformReachabilityPathLength R ∧ BorosDirectedPath R a c n := by
  classical
  let n := borosReachabilityPathLength R a c
  have hpath : BorosDirectedPath R a c n := by
    dsimp [n, borosReachabilityPathLength]
    simp only [dif_pos h]
    exact Classical.choose_spec (exists_borosDirectedPath_of_reflTransGen h)
  have hn : n ≤ borosUniformReachabilityPathLength R := by
    dsimp [n, borosReachabilityPathLength]
    unfold borosUniformReachabilityPathLength
    apply Finset.le_sup (s := Finset.univ) (f := fun p : α × α =>
      if h' : Relation.ReflTransGen R p.1 p.2 then
        Classical.choose (exists_borosDirectedPath_of_reflTransGen h') else 0)
      (Finset.mem_univ (a, c))
  exact ⟨n, hn, hpath⟩

/-- The iterated endpoint thresholds are nondecreasing when the increment bound is
nonnegative. -/
theorem monotone_borosWeightedPathBound (b : ℝ) (hb : 0 ≤ b) :
    Monotone (borosWeightedPathBound b) := by
  have hstep : ∀ n, borosWeightedPathBound b n ≤ borosWeightedPathBound b (n + 1) := by
    intro n
    induction n with
    | zero =>
        simpa [borosWeightedPathBound, Real.exp_zero] using hb
    | succ n ih =>
        have h := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ih) hb
        simpa [borosWeightedPathBound] using h
  intro n m hnm
  induction hnm with
  | refl => rfl
  | step h ih => exact le_trans ih (hstep _)

/-- If every weighted increment on a finite path is at most `b`, then its endpoint is bounded
by the corresponding iterate of `x ↦ b * exp x`. -/
theorem boros_endpoint_le_weightedPathBound
    (b : ℝ) (hb : 0 ≤ b) (y : ℕ → ℝ) (hy0 : y 0 = 0) :
    ∀ n, (∀ i, i < n → Real.exp (-y i) * y (i + 1) ≤ b) →
      y n ≤ borosWeightedPathBound b n := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [borosWeightedPathBound, hy0]
  | succ n ih =>
      intro hstep
      have hprev := ih (fun i hi => hstep i (Nat.lt_succ_of_lt hi))
      have hlast := hstep n (Nat.lt_succ_self n)
      have hexppos : 0 < Real.exp (y n) := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hlast (le_of_lt hexppos)
      have hexpcancel : Real.exp (-y n) * Real.exp (y n) = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hrewrite : y (n + 1) =
          (Real.exp (-y n) * y (n + 1)) * Real.exp (y n) := by
        calc
          y (n + 1) = 1 * y (n + 1) := by ring
          _ = (Real.exp (-y n) * Real.exp (y n)) * y (n + 1) := by
            rw [hexpcancel]
          _ = (Real.exp (-y n) * y (n + 1)) * Real.exp (y n) := by ring
      calc
        y (n + 1) = (Real.exp (-y n) * y (n + 1)) * Real.exp (y n) := hrewrite
        _ ≤ b * Real.exp (y n) := hmul
        _ ≤ b * Real.exp (borosWeightedPathBound b n) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hprev) hb
        _ = borosWeightedPathBound b (n + 1) := rfl

/-- Along a directed path, bounding each weighted edge term bounds the endpoint gap. -/
theorem boros_pathEndpoint_le_weightedPathBound
    {α : Type*} {R : α → α → Prop} (b : ℝ) (hb : 0 ≤ b)
    (gap : α → ℝ) {a c : α} {n : ℕ}
    (p : BorosDirectedPath R a c n) (ha : gap a = 0)
    (hstep : ∀ u v, R u v → Real.exp (-gap u) * gap v ≤ b) :
    gap c ≤ borosWeightedPathBound b n := by
  induction p with
  | refl => simp [ha, borosWeightedPathBound]
  | @tail b' c n p hab ih =>
      have hlast := hstep b' c hab
      have hexppos : 0 < Real.exp (gap b') := Real.exp_pos _
      have hmul := mul_le_mul_of_nonneg_right hlast (le_of_lt hexppos)
      have hexpcancel : Real.exp (-gap b') * Real.exp (gap b') = 1 := by
        rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
      have hrewrite : gap c =
          (Real.exp (-gap b') * gap c) * Real.exp (gap b') := by
        calc
          gap c = 1 * gap c := by ring
          _ = (Real.exp (-gap b') * Real.exp (gap b')) * gap c := by
            rw [hexpcancel]
          _ = (Real.exp (-gap b') * gap c) * Real.exp (gap b') := by ring
      calc
        gap c = (Real.exp (-gap b') * gap c) * Real.exp (gap b') := hrewrite
        _ ≤ b * Real.exp (gap b') := hmul
        _ ≤ b * Real.exp (borosWeightedPathBound b n) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ih) hb
        _ = borosWeightedPathBound b (n + 1) := rfl

/-- If a path endpoint exceeds the iterated bound, some directed edge on the path has a large
weighted increment. -/
theorem exists_borosPath_edge_weightedIncrement_gt
    {α : Type*} {R : α → α → Prop} (b : ℝ) (hb : 0 ≤ b)
    (gap : α → ℝ) {a c : α} {n : ℕ}
    (p : BorosDirectedPath R a c n) (ha : gap a = 0)
    (hend : borosWeightedPathBound b n < gap c) :
    ∃ u v, R u v ∧ b < Real.exp (-gap u) * gap v := by
  by_contra hnone
  have hstep : ∀ u v, R u v → Real.exp (-gap u) * gap v ≤ b := by
    intro u v huv
    by_contra hnot
    exact hnone ⟨u, v, huv, lt_of_not_ge hnot⟩
  have hbound := boros_pathEndpoint_le_weightedPathBound b hb gap p ha hstep
  exact (not_lt_of_ge hbound) hend

/-- The large edge can be chosen with its path prefix and suffix retained. -/
theorem exists_borosPath_edge_weightedIncrement_gt_with_context
    {α : Type*} {R : α → α → Prop} (b : ℝ) (hb : 0 ≤ b)
    (gap : α → ℝ) {a c : α} {n : ℕ}
    (p : BorosDirectedPath R a c n) (ha : gap a = 0)
    (hend : borosWeightedPathBound b n < gap c) :
    ∃ u v, R u v ∧ Relation.ReflTransGen R a u ∧
      Relation.ReflTransGen R v c ∧ b < Real.exp (-gap u) * gap v := by
  induction p with
  | refl =>
      norm_num [ha, borosWeightedPathBound] at hend
  | @tail d c n p hdc ih =>
      by_cases hprev : borosWeightedPathBound b n < gap d
      · obtain ⟨u, v, huv, hau, hvd, hlarge⟩ := ih hprev
        exact ⟨u, v, huv, hau, hvd.tail hdc, hlarge⟩
      · have hgapd : gap d ≤ borosWeightedPathBound b n := le_of_not_gt hprev
        have hlast : b < Real.exp (-gap d) * gap c := by
          by_contra hnot
          have hlastle : Real.exp (-gap d) * gap c ≤ b := le_of_not_gt hnot
          have hexppos : 0 < Real.exp (gap d) := Real.exp_pos _
          have hmul := mul_le_mul_of_nonneg_right hlastle hexppos.le
          have hcancel : Real.exp (-gap d) * Real.exp (gap d) = 1 := by
            rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
          have hrewrite : gap c =
              (Real.exp (-gap d) * gap c) * Real.exp (gap d) := by
            calc
              gap c = 1 * gap c := by ring
              _ = (Real.exp (-gap d) * Real.exp (gap d)) * gap c := by rw [hcancel]
              _ = (Real.exp (-gap d) * gap c) * Real.exp (gap d) := by ring
          have hstep : gap c ≤ b * Real.exp (gap d) := by
            calc
              gap c = (Real.exp (-gap d) * gap c) * Real.exp (gap d) := hrewrite
              _ ≤ b * Real.exp (gap d) := hmul
          have hmono : Real.exp (gap d) ≤
              Real.exp (borosWeightedPathBound b n) :=
            Real.exp_le_exp.mpr hgapd
          have hstep' : b * Real.exp (gap d) ≤
              b * Real.exp (borosWeightedPathBound b n) :=
            mul_le_mul_of_nonneg_left hmono hb
          have hbound : gap c ≤ borosWeightedPathBound b (n + 1) := by
            calc
              gap c ≤ b * Real.exp (gap d) := hstep
              _ ≤ b * Real.exp (borosWeightedPathBound b n) := hstep'
              _ = borosWeightedPathBound b (n + 1) := rfl
          exact (not_lt_of_ge hbound) hend
        exact ⟨d, c, hdc, p.toReflTransGen, Relation.ReflTransGen.refl, hlast⟩

/-- One threshold works for all directed paths whose lengths are at most `M`. -/
theorem exists_borosPath_edge_weightedIncrement_gt_of_length_le
    {α : Type*} {R : α → α → Prop} (b : ℝ) (hb : 0 ≤ b)
    (gap : α → ℝ) {a c : α} {n M : ℕ}
    (p : BorosDirectedPath R a c n) (hlen : n ≤ M) (ha : gap a = 0)
    (hend : borosWeightedPathBound b M < gap c) :
    ∃ u v, R u v ∧ b < Real.exp (-gap u) * gap v := by
  apply exists_borosPath_edge_weightedIncrement_gt b hb gap p ha
  exact lt_of_le_of_lt
    (monotone_borosWeightedPathBound b hb hlen) hend

/-- For a finite directed relation, one threshold works for every reachable pair: a sufficiently
large endpoint gap forces a weighted increment above `b` along any chosen reachability path. -/
theorem exists_reachable_edge_weightedIncrement_gt
    {α : Type*} [Fintype α] {R : α → α → Prop} (b : ℝ) (hb : 0 ≤ b)
    (gap : α → ℝ) {a c : α}
    (hreach : Relation.ReflTransGen R a c) (ha : gap a = 0)
    (hend : borosWeightedPathBound b (borosUniformReachabilityPathLength R) < gap c) :
    ∃ u v, R u v ∧ b < Real.exp (-gap u) * gap v := by
  obtain ⟨n, hn, p⟩ := exists_borosDirectedPath_of_reflTransGen_length_le hreach
  exact exists_borosPath_edge_weightedIncrement_gt_of_length_le b hb gap p hn ha hend

/-- For a reachable pair, a large endpoint gives an edge on a witnessing path together with its
prefix and suffix. This form preserves linkage-class information for network applications. -/
theorem exists_reachable_edge_weightedIncrement_gt_with_context
    {α : Type*} [Fintype α] {R : α → α → Prop} (b : ℝ) (hb : 0 ≤ b)
    (gap : α → ℝ) {a c : α}
    (hreach : Relation.ReflTransGen R a c) (ha : gap a = 0)
    (hend : borosWeightedPathBound b (borosUniformReachabilityPathLength R) < gap c) :
    ∃ u v, R u v ∧ Relation.ReflTransGen R a u ∧
      Relation.ReflTransGen R v c ∧ b < Real.exp (-gap u) * gap v := by
  obtain ⟨n, hn, p⟩ := exists_borosDirectedPath_of_reflTransGen_length_le hreach
  have hbound : borosWeightedPathBound b n < gap c :=
    lt_of_le_of_lt (monotone_borosWeightedPathBound b hb hn) hend
  exact exists_borosPath_edge_weightedIncrement_gt_with_context b hb gap p ha hbound

/-- A sufficiently large endpoint forces a large weighted increment somewhere along the path. -/
theorem exists_weightedPath_increment_gt_of_endpoint_gt
    (b : ℝ) (hb : 0 ≤ b) (y : ℕ → ℝ) (hy0 : y 0 = 0) (n : ℕ)
    (hend : borosWeightedPathBound b n < y n) :
    ∃ i, i < n ∧ b < Real.exp (-y i) * y (i + 1) := by
  by_contra hnone
  have hstep : ∀ i, i < n → Real.exp (-y i) * y (i + 1) ≤ b := by
    intro i hi
    by_contra hnot
    exact hnone ⟨i, hi, lt_of_not_ge hnot⟩
  have hbound := boros_endpoint_le_weightedPathBound b hb y hy0 n hstep
  exact (not_lt_of_ge hbound) hend

/-- A single threshold works for every path of length at most `M`. -/
theorem exists_weightedPath_increment_gt_of_endpoint_gt_of_length_le
    (b : ℝ) (hb : 0 ≤ b) (y : ℕ → ℝ) (hy0 : y 0 = 0)
    (n M : ℕ) (hlen : n ≤ M)
    (hend : borosWeightedPathBound b M < y n) :
    ∃ i, i < n ∧ b < Real.exp (-y i) * y (i + 1) := by
  apply exists_weightedPath_increment_gt_of_endpoint_gt b hb y hy0 n
  exact lt_of_le_of_lt
    (monotone_borosWeightedPathBound b hb hlen) hend

end Analysis
end CRNT
