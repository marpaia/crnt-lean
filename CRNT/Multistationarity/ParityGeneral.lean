import CRNT.Multistationarity.ParityOfSteadyStates

/-!
# Conditional degree/parity consequences and restricted total-degree examples

The finite signed-count arguments use the displayed boundary, regularity,
finiteness and total-degree inputs. Explicit affine/rank-restricted computations
are available where stated. Full openness alone does not force odd parity; the
general total-degree theorem under dissipativity and boundary conditions remains
incomplete. See `ParityOfSteadyStates` and `test.SemanticCorrespondence`.
An earlier parity attribution with no verifiable source has been removed.
-/

set_option maxHeartbeats 800000

namespace CRNT

/-! ## A finset lemma: the signed sum over a finite set -/

/-- **The signed sum over a finset, split by the sign of the summand.**  The sum of the signs
`sign (f y)` over a finite set `s` is the number of the strictly positive values of `f` minus
the number of the strictly negative ones; the values that vanish contribute `0`. -/
theorem sum_sign_eq_card_pos_sub_card_neg {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → ℝ) :
    (∑ y ∈ s, ((SignType.sign (f y) : SignType) : ℤ))
      = ((s.filter fun y => 0 < f y).card : ℤ) - ((s.filter fun y => f y < 0).card : ℤ) := by
  classical
  have hsplit : (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
      ∪ s.filter (fun y => f y = 0) = s := by
    ext y
    rw [Finset.mem_union, Finset.mem_union, Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      rcases h with h | h
      · rcases h with h | h
        · exact h.1
        · exact h.1
      · exact h.1
    · intro hy
      rcases lt_trichotomy (f y) 0 with h | h | h
      · exact Or.inl (Or.inr ⟨hy, h⟩)
      · exact Or.inr ⟨hy, h⟩
      · exact Or.inl (Or.inl ⟨hy, h⟩)
  have hdisjAB : Disjoint (s.filter (fun y => 0 < f y)) (s.filter (fun y => f y < 0)) := by
    refine Finset.disjoint_left.2 fun y hyA hyB => ?_
    have h1 := Finset.mem_filter.mp hyA
    have h2 := Finset.mem_filter.mp hyB
    linarith [h1.2, h2.2]
  have hdisjAC : Disjoint (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
      (s.filter (fun y => f y = 0)) := by
    refine Finset.disjoint_left.2 fun y hyAB hyC => ?_
    have h2 := Finset.mem_filter.mp hyC
    rcases Finset.mem_union.mp hyAB with hyA | hyB
    · have h1 := Finset.mem_filter.mp hyA
      linarith [h1.2, h2.2]
    · have h1 := Finset.mem_filter.mp hyB
      linarith [h1.2, h2.2]
  have h1' : (∑ y ∈ (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
        ∪ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ))
      = (∑ y ∈ s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0),
        ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ)) :=
    Finset.sum_union hdisjAC
  have h2' : (∑ y ∈ s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0),
        ((SignType.sign (f y) : SignType) : ℤ))
      = (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ)) :=
    Finset.sum_union hdisjAB
  have hsum : (∑ y ∈ s, ((SignType.sign (f y) : SignType) : ℤ))
      = (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ))
        + (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ)) := by
    have h1 : (∑ y ∈ (s.filter (fun y => 0 < f y) ∪ s.filter (fun y => f y < 0))
        ∪ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ))
        = (∑ y ∈ s, ((SignType.sign (f y) : SignType) : ℤ)) :=
      Finset.sum_congr hsplit (fun y _ => rfl)
    rw [← h1, h1', h2']
  have hA : (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
      = ((s.filter (fun y => 0 < f y)).card : ℤ) := by
    calc (∑ y ∈ s.filter (fun y => 0 < f y), ((SignType.sign (f y) : SignType) : ℤ))
        = ∑ y ∈ s.filter (fun y => 0 < f y), (1 : ℤ) := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          have hy' := Finset.mem_filter.mp hy
          rw [sign_pos hy'.2]
          rfl
      _ = ((s.filter (fun y => 0 < f y)).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have hB : (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ))
      = -((s.filter (fun y => f y < 0)).card : ℤ) := by
    calc (∑ y ∈ s.filter (fun y => f y < 0), ((SignType.sign (f y) : SignType) : ℤ))
        = ∑ y ∈ s.filter (fun y => f y < 0), (-1 : ℤ) := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          have hy' := Finset.mem_filter.mp hy
          rw [sign_neg hy'.2]
          rfl
      _ = -((s.filter (fun y => f y < 0)).card : ℤ) := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_neg, mul_one]
  have hC : (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ)) = 0 := by
    calc (∑ y ∈ s.filter (fun y => f y = 0), ((SignType.sign (f y) : SignType) : ℤ))
        = ∑ y ∈ s.filter (fun y => f y = 0), (0 : ℤ) := by
          refine Finset.sum_congr rfl (fun y hy => ?_)
          have hy' := Finset.mem_filter.mp hy
          rw [hy'.2, sign_zero]
          rfl
      _ = 0 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_zero]
  rw [hsum, hA, hB, hC]
  ring

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The parity of the count is the parity of the class degree -/

/-- **The parity of the number of positive steady states is the parity of the class degree.**
This is the general form of the parity theorem: it does *not* require the class degree to be
`(-1)^s`, only the relation `degree = count − 2 · (number of negative local degrees)` of
`Network.classDegree_eq_card_sub_two_mul_negCount`.  Equivalently, the parity of the count is
determined by the class degree alone. -/
theorem card_positiveSteadyStates_odd_iff_classDegree_odd
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0) :
    Odd (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Odd (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_sub_two_mul_negCount κ c hfinN hfinP hbd hnd
  have hcount : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-- **A class whose degree is even carries an even number of positive steady states.** -/
theorem card_positiveSteadyStates_even_iff_classDegree_even
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0) :
    Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Even (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_sub_two_mul_negCount κ c hfinN hfinP hbd hnd
  have hcount : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-! ## The "counted with multiplicity" reading -/

/-- **The weighted count of the positive steady states of a class is the class degree.**
The *weighted count* is the sum of the local degrees `sign (det (reducedJacobian y))` over the
positive steady states of the class; the class degree is the same sum over the zeros of the
steady-state map in the nonnegative class.  Under the "no boundary steady state" hypothesis the
two sets of zeros coincide, so the two sums are equal *exactly* — and this holds **without** the
nondegeneracy hypothesis, since the two sums are the same sum. -/
theorem weightedCount_eq_classDegree (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = N.nonnegativeClassDegree κ c hfinN := by
  classical
  have hset : hfinN.toFinset = hfinP.toFinset := by
    ext y
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hz, hnn⟩
      refine ⟨hz, ?_⟩
      by_contra hnpos
      exact hbd y ⟨(mem_nonnegativeClassRegion_iff N c y).mp hnn, hnpos⟩
        (Set.mem_preimage.mp hz)
    · rintro ⟨hz, hp⟩
      exact ⟨hz, (mem_nonnegativeClassRegion_iff N c y).mp
        ((mem_positiveClassRegion_iff N c y).mp hp).nonnegative⟩
  unfold nonnegativeClassDegree localDegreeOn
  rw [hset]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]

set_option linter.style.haveILetI false in
/-- **The weighted count of the positive steady states of a class is the class degree**, in the
form that uses the finset of the *set* of positive steady states rather than the finset attached
to the finiteness witness.  (The two finsets coincide, by
`Set.Finite.toFinset_eq_toFinset`.) -/
theorem weightedCount_eq_classDegree_of_set (N : Network S) (κ : N.RateConstants)
    (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    letI := hfinP.fintype
    (∑ y ∈ (N.positiveSteadyStates_in_class κ c).toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = N.nonnegativeClassDegree κ c hfinN := by
  letI := hfinP.fintype
  rw [← Set.Finite.toFinset_eq_toFinset hfinP]
  exact weightedCount_eq_classDegree N κ c hfinN hfinP hbd

/-! ## The parity theorem without the nondegeneracy hypothesis -/

/-- **The number of positive steady states of the class at which the reduced Jacobian is
nondegenerate** (i.e. invertible, so that the local degree there is `±1`). -/
noncomputable def card_nondegeneratePositiveSteadyStates_in_class (N : Network S)
    (κ : N.RateConstants) (c : Concentration S)
    (hfin : (N.positiveSteadyStates_in_class κ c).Finite) : ℕ :=
  (hfin.toFinset.filter fun y => (N.reducedJacobian κ c y).det ≠ 0).card

/-- **The class degree is the number of the nondegenerate positive steady states minus twice the
number of those at which the reduced Jacobian determinant is negative.**

This is the identity behind the parity theorem, and it holds **without** the nondegeneracy
hypothesis: the degenerate zeros contribute `0` to the class degree (their local degree, in the
sense of the degree machinery, is `sign 0 = 0`), and they are not counted on the left-hand side.
With the nondegeneracy hypothesis the statement specializes to
`Network.classDegree_eq_card_sub_two_mul_negCount`. -/
theorem classDegree_eq_card_nondeg_sub_two_mul_negCount
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    N.nonnegativeClassDegree κ c hfinN =
      (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ) -
        2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
  classical
  have hset : hfinN.toFinset = hfinP.toFinset := by
    ext y
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hz, hnn⟩
      refine ⟨hz, ?_⟩
      by_contra hnpos
      exact hbd y ⟨(mem_nonnegativeClassRegion_iff N c y).mp hnn, hnpos⟩
        (Set.mem_preimage.mp hz)
    · rintro ⟨hz, hp⟩
      exact ⟨hz, (mem_nonnegativeClassRegion_iff N c y).mp
        ((mem_positiveClassRegion_iff N c y).mp hp).nonnegative⟩
  -- the class degree is the signed count of the signs of the reduced determinants
  have hdeg : N.nonnegativeClassDegree κ c hfinN =
      (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    unfold nonnegativeClassDegree localDegreeOn
    rw [hset]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
  -- the signed count is the number of the positive signs minus the number of the negative ones
  have hsign := sum_sign_eq_card_pos_sub_card_neg (hfinP.toFinset)
    (fun y => (N.reducedJacobian κ c y).det)
  -- the nondegenerate zeros are the positive ones and the negative ones
  have hfilter : hfinP.toFinset.filter (fun y => (N.reducedJacobian κ c y).det ≠ 0)
      = (hfinP.toFinset.filter fun y => 0 < (N.reducedJacobian κ c y).det) ∪
        (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0) := by
    ext y
    rw [Finset.mem_filter, Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    constructor
    · rintro ⟨hy, hne⟩
      rcases lt_trichotomy (N.reducedJacobian κ c y).det 0 with h | h | h
      · exact Or.inr ⟨hy, h⟩
      · exact absurd h hne
      · exact Or.inl ⟨hy, h⟩
    · rintro (h | h)
      · exact ⟨h.1, ne_of_gt h.2⟩
      · exact ⟨h.1, ne_of_lt h.2⟩
  have hdisj : Disjoint (hfinP.toFinset.filter fun y => 0 < (N.reducedJacobian κ c y).det)
      (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0) := by
    refine Finset.disjoint_left.2 fun y hyP hyM => ?_
    have h1 := Finset.mem_filter.mp hyP
    have h2 := Finset.mem_filter.mp hyM
    linarith [h1.2, h2.2]
  have hcard : (hfinP.toFinset.filter (fun y => (N.reducedJacobian κ c y).det ≠ 0)).card
      = (hfinP.toFinset.filter fun y => 0 < (N.reducedJacobian κ c y).det).card
        + (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card := by
    rw [hfilter, Finset.card_union_of_disjoint hdisj]
  have hneg : (N.card_negativeReducedDet_in_class κ c hfinP : ℤ)
      = ((hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card : ℤ) := by
    have h1 : N.card_negativeReducedDet_in_class κ c hfinP
        = (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card := rfl
    rw [h1]
  have h1 : N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP
      = (hfinP.toFinset.filter (fun y => (N.reducedJacobian κ c y).det ≠ 0)).card := rfl
  rw [hdeg, hsign, h1, hcard, hneg]
  rw [Nat.cast_add]
  ring

/-- **The parity of the number of nondegenerate positive steady states is the parity of the class
degree.**  This is the form of the parity theorem that survives *without* the nondegeneracy
hypothesis: the count is that of the positive steady states at which the reduced Jacobian is
invertible, and the class degree is the signed count of the local degrees over all the zeros of
the class. -/
theorem card_nondegenerate_positiveSteadyStates_odd_iff_classDegree_odd
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    Odd (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Odd (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_nondeg_sub_two_mul_negCount κ c hfinN hfinP hbd
  have hcount : (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-- **The even case of the parity theorem without the nondegeneracy hypothesis.** -/
theorem card_nondegenerate_positiveSteadyStates_even_iff_classDegree_even
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0) :
    Even (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ) ↔
      Even (N.nonnegativeClassDegree κ c hfinN) := by
  have hkey := N.classDegree_eq_card_nondeg_sub_two_mul_negCount κ c hfinN hfinP hbd
  have hcount : (N.card_nondegeneratePositiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  constructor
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k - (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hkey, hk]
    ring
  · intro h
    obtain ⟨k, hk⟩ := h
    refine ⟨k + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ), ?_⟩
    rw [hcount, hk]
    ring

/-! ## Two positive steady states of opposite signs -/

/-- **The two opposite local degrees cancel in the class degree.**

Let `y₁` and `y₂` be two positive steady states of the class with opposite signs of the reduced
Jacobian determinant.  Their local degrees are `+1` and `−1`, so they cancel: the class degree is
the signed count of the local degrees over the *remaining* zeros of the class.

This is the exact content of the "the two opposite local degrees cancel" argument.  Note that it
does *not* force the number of positive steady states to be even: the remaining zeros contribute
the class degree, whose parity is the parity of the number of positive steady states
(`Network.card_positiveSteadyStates_odd_iff_classDegree_odd`), and the class degree may well be
odd.  See the namespace `CRNT.Network.OppositeSignsCounterexample` in this module for the
ingredients of an explicit counterexample. -/
theorem classDegree_eq_sum_erase_two_opposite_signs
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (hneg : (N.reducedJacobian κ c y₂).det < 0) :
    N.nonnegativeClassDegree κ c hfinN =
      (∑ y ∈ (hfinP.toFinset.erase y₁).erase y₂,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
  classical
  have hset : hfinN.toFinset = hfinP.toFinset := by
    ext y
    rw [Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨hz, hnn⟩
      refine ⟨hz, ?_⟩
      by_contra hnpos
      exact hbd y ⟨(mem_nonnegativeClassRegion_iff N c y).mp hnn, hnpos⟩
        (Set.mem_preimage.mp hz)
    · rintro ⟨hz, hp⟩
      exact ⟨hz, (mem_nonnegativeClassRegion_iff N c y).mp
        ((mem_positiveClassRegion_iff N c y).mp hp).nonnegative⟩
  have hdeg : N.nonnegativeClassDegree κ c hfinN =
      (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    unfold nonnegativeClassDegree localDegreeOn
    rw [hset]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
  have hy₁mem : y₁ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₁
  have hy₂mem : y₂ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₂
  have hy₂mem' : y₂ ∈ hfinP.toFinset.erase y₁ := by
    rw [Finset.mem_erase]
    exact ⟨fun h => hne h.symm, hy₂mem⟩
  have h1 : (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = ((SignType.sign (N.reducedJacobian κ c y₁).det : SignType) : ℤ)
        + (∑ y ∈ hfinP.toFinset.erase y₁,
          ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    have h := Finset.sum_erase_add hfinP.toFinset
      (fun y : ClassCoord N => ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      hy₁mem
    linarith
  have h2 : (∑ y ∈ hfinP.toFinset.erase y₁,
        ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      = ((SignType.sign (N.reducedJacobian κ c y₂).det : SignType) : ℤ)
        + (∑ y ∈ (hfinP.toFinset.erase y₁).erase y₂,
          ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ)) := by
    have h := Finset.sum_erase_add (hfinP.toFinset.erase y₁)
      (fun y : ClassCoord N => ((SignType.sign (N.reducedJacobian κ c y).det : SignType) : ℤ))
      hy₂mem'
    linarith
  have hg₁ : ((SignType.sign (N.reducedJacobian κ c y₁).det : SignType) : ℤ) = 1 := by
    rw [sign_pos hpos]
    rfl
  have hg₂ : ((SignType.sign (N.reducedJacobian κ c y₂).det : SignType) : ℤ) = -1 := by
    rw [sign_neg hneg]
    rfl
  rw [hdeg, h1, h2, hg₁, hg₂]
  ring

/-- **A class whose only positive steady states are two with opposite signs has class degree
zero.**  The two local degrees `+1` and `−1` cancel, and there is nothing else. -/
theorem classDegree_eq_zero_of_exactly_two_opposite_signs
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hexact : hfinP.toFinset = {y₁, y₂}) :
    N.nonnegativeClassDegree κ c hfinN = 0 := by
  have h := N.classDegree_eq_sum_erase_two_opposite_signs κ c hfinN hfinP hbd y₁ y₂
    hy₁ hy₂ hne hpos hneg
  rw [h, hexact]
  have hempty : ((({y₁, y₂} : Finset (ClassCoord N)).erase y₁).erase y₂) = ∅ := by
    ext z
    rw [Finset.mem_erase, Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hz2, hz1, hz⟩
      rcases hz with rfl | rfl
      · exact absurd hz1 (fun h => h rfl)
      · exact absurd hz2 (fun h => h rfl)
    · intro hz
      exact absurd hz (by simp)
  rw [hempty]
  simp

/-- **A class with exactly two positive steady states of opposite reduced-Jacobian signs carries
an even number of positive steady states.**  This is the form of the statement that holds when
the two opposite-sign steady states are *all* the positive steady states of the class: the class
degree is then zero (`Network.classDegree_eq_zero_of_exactly_two_opposite_signs`), and the parity
theorem gives that the number of positive steady states is even. -/
theorem card_positiveSteadyStates_even_of_exactly_two_opposite_signs
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hexact : hfinP.toFinset = {y₁, y₂}) :
    Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := by
  have hdeg : N.nonnegativeClassDegree κ c hfinN = 0 :=
    N.classDegree_eq_zero_of_exactly_two_opposite_signs κ c hfinN hfinP hbd y₁ y₂
      hy₁ hy₂ hne hpos hneg hexact
  have hiff := N.card_positiveSteadyStates_even_iff_classDegree_even κ c hfinN hfinP hbd hnd
  rw [hiff]
  refine ⟨0, by rw [hdeg]; ring⟩

/-- **Two distinct positive steady states of the class give at least two positive steady
states.** -/
theorem card_positiveSteadyStates_ge_two_of_two_mem
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂) :
    2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
  have hy₁mem : y₁ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₁
  have hy₂mem : y₂ ∈ hfinP.toFinset := by
    rw [Set.Finite.mem_toFinset]
    exact hy₂
  have hsub : ({y₁, y₂} : Finset (ClassCoord N)) ⊆ hfinP.toFinset := by
    intro y hy
    have hy' : y = y₁ ∨ y = y₂ := by
      simpa only [Finset.mem_insert, Finset.mem_singleton] using hy
    rcases hy' with rfl | rfl
    · exact hy₁mem
    · exact hy₂mem
  have hcard : ({y₁, y₂} : Finset (ClassCoord N)).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hne]), Finset.card_singleton]
  have h1 : N.card_positiveSteadyStates_in_class κ c hfinP = hfinP.toFinset.card := rfl
  rw [h1]
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  exact hle

/-- **A class with two positive steady states of opposite reduced-Jacobian signs and an even
class degree carries an even number of positive steady states.**

This is the *corrected* form of the "two opposite signs ⇒ even count" statement: the two opposite
local degrees cancel in the class degree, but the class degree itself need not be even — the
remaining zeros of the class contribute the class degree, and the parity of the count is the
parity of the class degree.  With the hypothesis that the class degree is even, the count is
even as well (and there are at least two positive steady states). -/
theorem card_positiveSteadyStates_even_of_two_opposite_signs_of_even_classDegree
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (_hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (_hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hdeg : Even (N.nonnegativeClassDegree κ c hfinN)) :
    Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ∧
      2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
  have hiff := N.card_positiveSteadyStates_even_iff_classDegree_even κ c hfinN hfinP hbd hnd
  have heven : Even (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := hiff.mpr hdeg
  have hcard2 : 2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP :=
    N.card_positiveSteadyStates_ge_two_of_two_mem κ c hfinP y₁ y₂ hy₁ hy₂ hne
  exact ⟨heven, hcard2⟩

/-- **The parity refinement of the Conradi–Feliu–Mincheva–Wiuf "exceptional local degree"
criterion.**  Suppose that the class degree is odd (as it is for a fully open network, where it is
the total degree `(-1)^s`) and that the class contains two positive steady states with opposite
signs of the reduced Jacobian determinant (an "exceptional local degree").  Then the number of
positive steady states of the class is **odd**, and it is at least **three**.

This is the statement that holds in place of the "two opposite signs ⇒ even count": the two
opposite local degrees cancel in the class degree, so the *remaining* zeros contribute the class
degree, and the parity theorem (`Network.card_positiveSteadyStates_odd_iff_classDegree_odd`)
gives that the count is odd. -/
theorem card_positiveSteadyStates_odd_of_two_opposite_signs_of_odd_classDegree
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (y₁ y₂ : ClassCoord N)
    (hy₁ : y₁ ∈ N.positiveSteadyStates_in_class κ c)
    (hy₂ : y₂ ∈ N.positiveSteadyStates_in_class κ c)
    (hne : y₁ ≠ y₂)
    (_hpos : 0 < (N.reducedJacobian κ c y₁).det)
    (_hneg : (N.reducedJacobian κ c y₂).det < 0)
    (hdeg : Odd (N.nonnegativeClassDegree κ c hfinN)) :
    Odd (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) ∧
      3 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
  have hiff := N.card_positiveSteadyStates_odd_iff_classDegree_odd κ c hfinN hfinP hbd hnd
  have hodd : Odd (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := hiff.mpr hdeg
  have hcard2 : 2 ≤ N.card_positiveSteadyStates_in_class κ c hfinP :=
    N.card_positiveSteadyStates_ge_two_of_two_mem κ c hfinP y₁ y₂ hy₁ hy₂ hne
  obtain ⟨k, hk⟩ := hodd
  have h2 : (2 : ℤ) ≤ (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := by
    exact_mod_cast hcard2
  have hk0 : 0 ≤ k := by
    have hnonneg : (0 : ℤ) ≤ (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) :=
      Nat.cast_nonneg _
    rw [hk] at hnonneg
    omega
  have h3 : (3 : ℤ) ≤ (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) := by
    omega
  have h3' : 3 ≤ N.card_positiveSteadyStates_in_class κ c hfinP := by
    exact_mod_cast h3
  exact ⟨hiff.mpr hdeg, h3'⟩

/-! ## A concrete instance: the two-species fully open network -/

namespace DegreeExampleParity

open DegreeExample

/-- **The parity relation of the count and the class degree for the two-species fully open
network.**  The network is the fully open extension of the reaction-free network on two species:
the four flow reactions `0 → A`, `A → 0`, `0 → B`, `B → 0`.  Its class degree is `+1`
(`DegreeExample.nonnegativeClassDegree_eq_one`), hence odd, and it has exactly one positive
steady state (`DegreeExampleParity.card_positiveSteadyStates_eq_one`), hence an odd number of
them. -/
theorem card_positiveSteadyStates_odd_iff_classDegree_odd :
    Odd (N.card_positiveSteadyStates_in_class rates 0 hfinP : ℤ) ↔
      Odd (N.nonnegativeClassDegree rates 0 hfinN) :=
  N.card_positiveSteadyStates_odd_iff_classDegree_odd rates 0 hfinN hfinP boundary_ne_zero hnd

/-- **The even case of the parity relation for the two-species fully open network.**  Both sides
are false here (the class degree is `+1` and the count is `1`), as they should be. -/
theorem card_positiveSteadyStates_even_iff_classDegree_even :
    Even (N.card_positiveSteadyStates_in_class rates 0 hfinP : ℤ) ↔
      Even (N.nonnegativeClassDegree rates 0 hfinN) :=
  N.card_positiveSteadyStates_even_iff_classDegree_even rates 0 hfinN hfinP boundary_ne_zero hnd

/-- **The weighted count of the positive steady states of the two-species fully open network is
its class degree.** -/
theorem weightedCount_eq_classDegree :
    (∑ y ∈ hfinP.toFinset,
        ((SignType.sign (N.reducedJacobian rates 0 y).det : SignType) : ℤ))
      = N.nonnegativeClassDegree rates 0 hfinN :=
  N.weightedCount_eq_classDegree rates 0 hfinN hfinP boundary_ne_zero

/-- Conditional degree/parity consequence under the hypotheses displayed below. -/
theorem card_positiveSteadyStates_is_odd :
    Odd (N.card_positiveSteadyStates_in_class rates 0 hfinP : ℤ) :=
  (card_positiveSteadyStates_odd_iff_classDegree_odd).mpr (by
    rw [nonnegativeClassDegree_eq_one]
    refine ⟨0, by ring⟩)

end DegreeExampleParity

/-! ## A counterexample to the "two opposite signs ⇒ even count" reading

The statement "a class with two positive steady states of opposite reduced-Jacobian signs carries
an **even** number of positive steady states" is **false**: the two opposite local degrees cancel
in the *class degree*, but the class degree is the signed count of the local degrees of the
*remaining* zeros, and its parity is the parity of the number of positive steady states
(`Network.card_positiveSteadyStates_odd_iff_classDegree_odd`).  The following is the
counterexample; the ingredients that are machine-checked here are the field, its zeros, and the
geometry of the class.

The network is the **one-species network** `∅ → A`, `A → ∅`, `2A → 3A`, `3A → 2A` with the rate
constants `6`, `11`, `6`, `1`.  Its mass-action field is

```
f(x) = 6 − 11 x + 6 x² − x³ = −(x − 1)(x − 2)(x − 3),
```

so it has exactly the three **positive** zeros `x = 1`, `x = 2`, `x = 3`
(`OppositeSignsCounterexample.massActionVectorField_eq_zero_iff`).  The stoichiometric subspace
is the whole species space (`OppositeSignsCounterexample.stoichSubspace_eq_top`) and the
stoichiometric rank is one (`OppositeSignsCounterexample.stoichRank_eq`), so the compatibility
class of the origin is the whole concentration space: all three zeros are positive steady states
of that class, and the number of positive steady states of the class is **three**, an odd
number.

In rank one the reduced Jacobian determinant is the derivative of the scalar reduced field along
the class (`Network.reducedJacobian_det_eq_deriv`), i.e. `f′(x) = −11 + 12 x − 3 x²`; at the
three steady states it is `−2`, `+1`, `−2`.  Hence the class contains two positive steady states
of **opposite** signs (at `x = 2` and at `x = 1`), while the number of positive steady states is
`3`, which is **odd**.  The class degree is the signed count `−1 + 1 − 1 = −1`, which is odd as
well — exactly as the parity theorem of this module predicts. -/

namespace OppositeSignsCounterexample


/-- The source multiplicities of the four reactions `∅ → A`, `A → ∅`, `2A → 3A`, `3A → 2A`. -/
def sourceCount : Fin 4 → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3

/-- The target multiplicities of the four reactions. -/
def targetCount : Fin 4 → ℕ
  | 0 => 1
  | 1 => 0
  | 2 => 3
  | 3 => 2

/-- **The one-species network `∅ → A`, `A → ∅`, `2A → 3A`, `3A → 2A`.** -/
def N : Network (Fin 1) where
  R := Fin 4
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r => { source := fun _ => sourceCount r, target := fun _ => targetCount r }

/-- The rate constants of the network: `6`, `11`, `6`, `1`. -/
def k : Fin 4 → ℝ
  | 0 => 6
  | 1 => 11
  | 2 => 6
  | 3 => 1

/-- The rate constants of the network. -/
def rates : N.RateConstants where
  k := k
  positive r := by
    fin_cases r <;> norm_num [k]

/-- The unit vector of the species space. -/
def e₀ : Concentration (Fin 1) := fun _ => 1

/-- **The mass-action field of the network**: `x ↦ 6 − 11 x + 6 x² − x³`. -/
theorem massActionVectorField_eq (x : Concentration (Fin 1)) :
    N.massActionVectorField rates x = fun _ => 6 - 11 * x 0 + 6 * (x 0)^2 - (x 0)^3 := by
  funext s
  fin_cases s
  simp [N, sourceCount, targetCount, rates, k, Network.massActionVectorField_apply,
    Network.massActionRate, Complex.massActionMonomial, Fin.sum_univ_succ]
  ring

/-- **The polynomial `6 − 11 t + 6 t² − t³` vanishes exactly at `1`, `2`, `3`.** -/
theorem poly_eq_zero_iff (t : ℝ) :
    6 - 11 * t + 6 * t ^ 2 - t ^ 3 = 0 ↔ t = 1 ∨ t = 2 ∨ t = 3 := by
  have hid : 6 - 11 * t + 6 * t ^ 2 - t ^ 3 = -((t - 1) * (t - 2) * (t - 3)) := by
    ring
  rw [hid, neg_eq_zero]
  constructor
  · intro h
    have h' : ((t - 1) = 0 ∨ (t - 2) = 0) ∨ (t - 3) = 0 := by
      rw [mul_eq_zero, mul_eq_zero] at h
      exact h
    cases h' with
    | inl h =>
      cases h with
      | inl h =>
        left
        linarith
      | inr h =>
        right
        left
        linarith
    | inr h =>
      right
      right
      linarith
  · intro h
    cases h with
    | inl h =>
      subst h
      ring
    | inr h =>
      cases h with
      | inl h =>
        subst h
        ring
      | inr h =>
        subst h
        ring

/-- **The field vanishes exactly at the concentrations `1`, `2`, `3`.** -/
theorem massActionVectorField_eq_zero_iff (x : Concentration (Fin 1)) :
    N.massActionVectorField rates x = 0 ↔ x 0 = 1 ∨ x 0 = 2 ∨ x 0 = 3 := by
  constructor
  · intro h
    have h' := congrFun h (0 : Fin 1)
    rw [massActionVectorField_eq] at h'
    simp only [Pi.zero_apply] at h'
    exact (poly_eq_zero_iff (x 0)).mp h'
  · intro h
    have h0 : 6 - 11 * x 0 + 6 * (x 0)^2 - (x 0)^3 = 0 := by
      cases h with
      | inl h =>
        have := (poly_eq_zero_iff (x 0)).mpr (Or.inl h)
        linarith [this]
      | inr h =>
        cases h with
        | inl h =>
          have := (poly_eq_zero_iff (x 0)).mpr (Or.inr (Or.inl h))
          linarith [this]
        | inr h =>
          have := (poly_eq_zero_iff (x 0)).mpr (Or.inr (Or.inr h))
          linarith [this]
    rw [massActionVectorField_eq]
    funext s
    simp only [Pi.zero_apply]
    exact h0

/-- The reaction vector of the first reaction `∅ → A` is the unit vector. -/
theorem reactionVector_zero : N.reactionVector (0 : Fin 4) = fun _ => (1 : ℝ) := by
  funext s
  fin_cases s
  simp [N, sourceCount, targetCount, Network.reactionVector_apply]

/-- **The stoichiometric subspace is the whole space.** -/
theorem stoichSubspace_eq_top : N.stoichSubspace = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x = x 0 • N.reactionVector (0 : Fin 4) := by
    funext s
    fin_cases s
    simp [reactionVector_zero, Pi.smul_apply, smul_eq_mul]
  rw [hx]
  exact Submodule.smul_mem _ _
    (N.reactionVector_mem_stoichSubspace (0 : Fin 4))

/-- **The stoichiometric rank is one.** -/
theorem stoichRank_eq : N.stoichRank = 1 := by
  rw [Network.stoichRank, stoichSubspace_eq_top, finrank_top, Module.finrank_fin_fun]

/-- **The stoichiometric subspace is the span of the unit vector.** -/
theorem stoichSubspace_eq_span : N.stoichSubspace = Submodule.span ℝ {e₀} := by
  rw [stoichSubspace_eq_top]
  ext x
  constructor
  · intro _
    refine Submodule.mem_span_singleton.mpr ⟨x 0, ?_⟩
    funext s
    fin_cases s
    simp [e₀, Pi.smul_apply, smul_eq_mul]
  · intro _
    exact Submodule.mem_top

end OppositeSignsCounterexample

#print axioms CRNT.Network.card_positiveSteadyStates_odd_iff_classDegree_odd
#print axioms CRNT.Network.card_positiveSteadyStates_even_iff_classDegree_even
#print axioms CRNT.Network.weightedCount_eq_classDegree
#print axioms CRNT.Network.classDegree_eq_card_nondeg_sub_two_mul_negCount
#print axioms CRNT.Network.card_nondegenerate_positiveSteadyStates_odd_iff_classDegree_odd
#print axioms CRNT.Network.classDegree_eq_sum_erase_two_opposite_signs
#print axioms CRNT.Network.card_positiveSteadyStates_odd_of_two_opposite_signs_of_odd_classDegree

end Network

end CRNT
