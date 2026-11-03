import CRNT.Multistationarity.DegreeStructural
import CRNT.Multistationarity.DegreeMultistationarity
import CRNT.Multistationarity.TwoReactionAtoms
import CRNT.Open.Augmentation

/-!
# Parity from a prescribed odd class degree

For finite nondegenerate zeros, with boundary zeros excluded, a signed count of
odd total degree implies an odd number of positive steady states. Full openness
supplies boundary exclusion, but does not supply the required total degree.
For example `∅ → A`, `A → ∅`, `2A → 3A` at rates 1, 3, 2 has two simple
positive equilibria. This counterexample is checked in `test.SemanticCorrespondence`.

The total-degree theorem under dissipativity and boundary assumptions is not
proved here. See Conradi–Feliu–Mincheva–Wiuf (2017),
https://pmc.ncbi.nlm.nih.gov/articles/PMC5626113/ . An earlier attribution to
"the conditional odd-degree argument 2006" lacked a verifiable source and has been removed.
-/

set_option maxHeartbeats 800000

namespace CRNT

namespace Network

open scoped BigOperators Topology Classical

open Set Filter

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The positive steady states of a compatibility class -/

/-- **The positive steady states of `N` in the compatibility class of `c`, in chart
coordinates.**  A chart coordinate `y` belongs to this set when the reduced field
`N.steadyStateMap κ c` vanishes at `y` and the corresponding concentration `N.affineChart c y` is
strictly positive.  These are exactly the positive mass-action steady states of the compatibility
class of `c` (`Network.mem_positiveSteadyStates_in_class_iff`). -/
def positiveSteadyStates_in_class (N : Network S) (κ : N.RateConstants) (c : Concentration S) :
    Set (ClassCoord N) :=
  N.steadyStateMap κ c ⁻¹' {0} ∩ N.positiveClassRegion c

/-- **The number of positive steady states of `N` in the compatibility class of `c`.** -/
noncomputable def card_positiveSteadyStates_in_class (N : Network S) (κ : N.RateConstants)
    (c : Concentration S) (hfin : (N.positiveSteadyStates_in_class κ c).Finite) : ℕ :=
  hfin.toFinset.card

/-- **The number of positive steady states of `N` in the compatibility class of `c` at which the
reduced Jacobian determinant is negative.**  These are the steady states contributing `-1` to the
class degree. -/
noncomputable def card_negativeReducedDet_in_class (N : Network S) (κ : N.RateConstants)
    (c : Concentration S) (hfin : (N.positiveSteadyStates_in_class κ c).Finite) : ℕ :=
  (hfin.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card

/-- **The chart coordinates of the positive steady states of the class of `c` are exactly the
chart coordinates of the positive steady states of `N` in that class.**  This is the bridge
between the chart-based count and the ambient notion of a positive steady state. -/
theorem mem_positiveSteadyStates_in_class_iff (N : Network S) (κ : N.RateConstants)
    (c : Concentration S) (y : ClassCoord N) :
    y ∈ N.positiveSteadyStates_in_class κ c ↔
      Concentration.Positive (N.affineChart c y) ∧ N.IsMassActionSteadyState κ (N.affineChart c y) := by
  constructor
  · intro hy
    refine ⟨(mem_positiveClassRegion_iff N c y).mp hy.2, ?_⟩
    obtain ⟨hcompat, hsteady⟩ :=
      N.isMassActionSteadyState_affineChart_of_reducedField_eq_zero κ c hy.1
    exact hsteady
  · rintro ⟨hp, hsteady⟩
    have hF : N.massActionVectorField κ (N.affineChart c y) = 0 := by
      funext s
      exact hsteady s
    have hzero : N.steadyStateMap κ c y = 0 := by
      simp only [Network.steadyStateMap, reducedField, hF, map_zero]
    exact ⟨hzero, (mem_positiveClassRegion_iff N c y).mpr hp⟩

/-! ## The class degree is the count minus twice the number of negative local degrees -/

/-- **The class degree is the number of positive steady states minus twice the number of those
at which the reduced Jacobian determinant is negative.**

This is the *parity* form of the signed count performed by the degree machinery: the class degree
is `∑ y, sign (det (reducedJacobian y))` over the zeros of the reduced field in the nonnegative
class, and each summand is `+1` or `-1` when the zero is nondegenerate.  Consequently the number
of positive steady states and the class degree differ by an even number. -/
theorem classDegree_eq_card_sub_two_mul_negCount
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0) :
    N.nonnegativeClassDegree κ c hfinN =
      (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) -
        2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
  classical
  -- the two finiteness witnesses describe the same set of chart coordinates
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
  -- every zero of the reduced field in the nonnegative class is nondegenerate
  have hnd' : ∀ y ∈ hfinN.toFinset, (N.reducedJacobian κ c y).det ≠ 0 := by
    intro y hy
    apply hnd y
    have hy' : y ∈ N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c :=
      hfinN.mem_toFinset.mp hy
    show y ∈ N.positiveSteadyStates_in_class κ c
    refine ⟨hy'.1, ?_⟩
    by_contra hnpos
    exact hbd y ⟨(mem_nonnegativeClassRegion_iff N c y).mp hy'.2, hnpos⟩
      (Set.mem_preimage.mp hy'.1)
  -- the zero set splits into the positive and the negative determinant part
  have hsplit : hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det) ∪
      hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0) = hfinN.toFinset := by
    ext y
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro hyS
      have hne : (N.reducedJacobian κ c y).det ≠ 0 := hnd' y hyS
      rcases lt_trichotomy (N.reducedJacobian κ c y).det 0 with h | h | h
      · exact Or.inr ⟨hyS, h⟩
      · exact absurd h hne
      · exact Or.inl ⟨hyS, h⟩
  have hdisj : Disjoint (hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det))
      (hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0)) := by
    refine Finset.disjoint_left.2 fun y hyP hyM => ?_
    have hpos : 0 < (N.reducedJacobian κ c y).det := (Finset.mem_filter.mp hyP).2
    have hneg : (N.reducedJacobian κ c y).det < 0 := (Finset.mem_filter.mp hyM).2
    exact (not_lt_of_ge (le_of_lt hpos)) hneg
  -- the degree is the signed count of the local degrees
  have hdeg : N.nonnegativeClassDegree κ c hfinN =
      (∑ y ∈ hfinN.toFinset,
        ((SignType.sign ((N.reducedJacobian κ c y).det) : SignType) : ℤ)) := by
    unfold nonnegativeClassDegree localDegreeOn
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [N.det_fderiv_steadyStateMap_eq_reducedJacobian_det]
  -- the signed count is the number of positive local degrees minus the number of negative ones
  have hsign : (∑ y ∈ hfinN.toFinset,
        ((SignType.sign ((N.reducedJacobian κ c y).det) : SignType) : ℤ))
      = ((hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det)).card : ℤ) -
        ((hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0)).card : ℤ) := by
    have h1 : (∑ y ∈ hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det) ∪
        hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0),
        ((SignType.sign ((N.reducedJacobian κ c y).det) : SignType) : ℤ))
        = (∑ y ∈ hfinN.toFinset,
          ((SignType.sign ((N.reducedJacobian κ c y).det) : SignType) : ℤ)) :=
      Finset.sum_congr hsplit (fun y _ => rfl)
    rw [h1.symm, Finset.sum_union hdisj]
    have hP : (∑ y ∈ hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det),
        ((SignType.sign ((N.reducedJacobian κ c y).det) : SignType) : ℤ))
        = (∑ y ∈ hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det), (1 : ℤ)) := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hy' := Finset.mem_filter.mp hy
      rw [sign_pos hy'.2]
      rfl
    have hM : (∑ y ∈ hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0),
        ((SignType.sign ((N.reducedJacobian κ c y).det) : SignType) : ℤ))
        = (∑ y ∈ hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0), (-1 : ℤ)) := by
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have hy' := Finset.mem_filter.mp hy
      rw [sign_neg hy'.2]
      rfl
    rw [hP, hM, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.sum_const, nsmul_eq_mul,
      mul_neg, mul_one]
    ring
  -- the count is the total number of zeros
  have hcardN : hfinN.toFinset.card =
      (hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det)).card +
        (hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0)).card := by
    have h1 : (hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det) ∪
        hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0)).card
        = hfinN.toFinset.card := by
      rw [hsplit]
    rw [h1.symm, Finset.card_union_of_disjoint hdisj]
  have hcard : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
      = ((hfinN.toFinset.filter (fun y => 0 < (N.reducedJacobian κ c y).det)).card : ℤ) +
        ((hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0)).card : ℤ) := by
    have h1 : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
        = ((hfinP.toFinset.card : ℕ) : ℤ) := rfl
    rw [h1, ← hset, ← Nat.cast_add]
    exact congrArg (fun n : ℕ => (n : ℤ)) hcardN
  -- the count of the negative local degrees is the one of the definition
  have hneg : (N.card_negativeReducedDet_in_class κ c hfinP : ℤ)
      = ((hfinN.toFinset.filter (fun y => (N.reducedJacobian κ c y).det < 0)).card : ℤ) := by
    have h1 : N.card_negativeReducedDet_in_class κ c hfinP
        = (hfinP.toFinset.filter fun y => (N.reducedJacobian κ c y).det < 0).card := rfl
    rw [h1, ← hset]
  rw [hdeg, hsign, hcard, hneg]
  ring

/-! ## The parity theorem -/

/-- **The number of positive steady states of a class is odd when the class degree is odd.**

This is the parity theorem of the conditional odd-degree argument in the form supported by the repository: the class
degree is the signed count of the zeros of the steady-state map in the class, and each
nondegenerate zero contributes `±1`; hence the parity of the number of positive steady states is
the parity of the class degree. -/
theorem card_positiveSteadyStates_odd (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (hdeg : ∃ j : ℤ, N.nonnegativeClassDegree κ c hfinN = 2 * j + 1) :
    (N.card_positiveSteadyStates_in_class κ c hfinP) % 2 = 1 := by
  obtain ⟨j, hj⟩ := hdeg
  have hkey := N.classDegree_eq_card_sub_two_mul_negCount κ c hfinN hfinP hbd hnd
  have hcount : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
      = N.nonnegativeClassDegree κ c hfinN
        + 2 * (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    rw [hkey]
    ring
  have hmain : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
      = 2 * (j + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ)) + 1 := by
    rw [hcount, hj]
    ring
  have hnonneg : 0 ≤ j + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) := by
    have hpos : 0 ≤ (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ) :=
      Nat.cast_nonneg _
    rw [hmain] at hpos
    omega
  have hcast : ((j + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ)).toNat : ℤ)
      = j + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ) :=
    Int.toNat_of_nonneg hnonneg
  have hnat : N.card_positiveSteadyStates_in_class κ c hfinP
      = 2 * (j + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ)).toNat + 1 := by
    have h1 : (N.card_positiveSteadyStates_in_class κ c hfinP : ℤ)
        = 2 * ((j + (N.card_negativeReducedDet_in_class κ c hfinP : ℤ)).toNat : ℤ) + 1 := by
      rw [hmain, hcast]
    exact_mod_cast h1
  rw [hnat]
  omega

/-- **An odd power of `-1` is of the form `2 * j + 1`.** -/
theorem exists_j_eq_two_mul_add_one_of_neg_one_pow (s : ℕ) :
    ∃ j : ℤ, (-1 : ℤ)^s = 2 * j + 1 := by
  induction s with
  | zero => exact ⟨0, by simp⟩
  | succ s ih =>
    obtain ⟨j, hj⟩ := ih
    refine ⟨-(j + 1), ?_⟩
    rw [pow_succ, hj]
    ring

/-- **The parity theorem in the Conradi–Feliu–Mincheva–Wiuf form.**  If the class degree of the
class of `c` is the total degree `(-1)^s` of the published theorem, then the number of positive
steady states in the class is odd.  Since `(-1)^s` is odd for every `s`, this is the the conditional odd-degree argument
parity theorem: an odd total degree forces an odd number of nondegenerate positive steady
states. -/
theorem card_positiveSteadyStates_odd_of_classDegree_eq_pow_neg_one
    (N : Network S) (κ : N.RateConstants) (c : Concentration S) (s : ℕ) (_hs : N.stoichRank = s)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (hdeg : N.nonnegativeClassDegree κ c hfinN = (-1)^s) :
    (N.card_positiveSteadyStates_in_class κ c hfinP) % 2 = 1 := by
  have hodd : ∃ j : ℤ, (-1)^s = 2 * j + 1 := exists_j_eq_two_mul_add_one_of_neg_one_pow s
  refine N.card_positiveSteadyStates_odd κ c hfinN hfinP hbd hnd ?_
  obtain ⟨j, hj⟩ := hodd
  refine ⟨j, ?_⟩
  rw [hdeg, hj]

/-- **The parity theorem with the class degree `±1`.**  This is the version in which the
hypothesis is the one suggested for the field-map leaf: the degree of the steady-state map on the
class is `+1` or `-1`, hence odd, and the number of positive steady states is odd. -/
theorem card_positiveSteadyStates_odd_of_classDegree_eq_one_or_neg_one
    (N : Network S) (κ : N.RateConstants) (c : Concentration S)
    (hfinN : (N.steadyStateMap κ c ⁻¹' {0} ∩ N.nonnegativeClassRegion c).Finite)
    (hfinP : (N.positiveSteadyStates_in_class κ c).Finite)
    (hbd : ∀ y ∈ N.classBoundary c, N.steadyStateMap κ c y ≠ 0)
    (hnd : ∀ y ∈ N.positiveSteadyStates_in_class κ c, (N.reducedJacobian κ c y).det ≠ 0)
    (hdeg : N.nonnegativeClassDegree κ c hfinN = 1 ∨ N.nonnegativeClassDegree κ c hfinN = -1) :
    (N.card_positiveSteadyStates_in_class κ c hfinP) % 2 = 1 := by
  rcases hdeg with h | h
  · refine N.card_positiveSteadyStates_odd κ c hfinN hfinP hbd hnd ⟨0, ?_⟩
    rw [h]
    ring
  · refine N.card_positiveSteadyStates_odd κ c hfinN hfinP hbd hnd ⟨-1, ?_⟩
    rw [h]
    ring

/-! ## A fully open network has no boundary steady state -/

/-- **The mass-action field of the fully open extension.**  The original reactions contribute the
first sum, the inflow pseudo-reaction `0 → s` contributes the constant `κ.k (inflow s)`, and the
outflow pseudo-reaction `s → 0` contributes `-κ.k (outflow s) * x s`. -/
theorem fullyOpen_massActionVectorField_eq (N : Network S) (κ : N.fullyOpen.RateConstants)
    (x : Concentration S) (s : S) :
    N.fullyOpen.massActionVectorField κ x s =
      (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
          N.reactionVector r s)
      + κ.k (Sum.inr (Sum.inl s))
      - κ.k (Sum.inr (Sum.inr s)) * x s := by
  rw [massActionVectorField_apply]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [massActionRate]
  have h1 : (∑ r : N.R, κ.k (Sum.inl r) *
      (N.fullyOpen.reaction (Sum.inl r)).source.massActionMonomial x *
        N.fullyOpen.reactionVector (Sum.inl r) s) =
      (∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
        N.reactionVector r s) := by
    refine Finset.sum_congr rfl (fun r _ => ?_)
    rw [fullyOpen_reaction_inl]
    rfl
  have h2 : (∑ s' : S, κ.k (Sum.inr (Sum.inl s')) *
      (N.fullyOpen.reaction (Sum.inr (Sum.inl s'))).source.massActionMonomial x *
        N.fullyOpen.reactionVector (Sum.inr (Sum.inl s')) s) = κ.k (Sum.inr (Sum.inl s)) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_inflow]; simp [Ne.symm hs']) (by simp)]
    erw [reactionVector_inflow, fullyOpen_reaction_inflow]
    simp [inflowReaction]
  have h3 : (∑ s' : S, κ.k (Sum.inr (Sum.inr s')) *
      (N.fullyOpen.reaction (Sum.inr (Sum.inr s'))).source.massActionMonomial x *
        N.fullyOpen.reactionVector (Sum.inr (Sum.inr s')) s) =
      -(κ.k (Sum.inr (Sum.inr s)) * x s) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_outflow]; simp [Ne.symm hs']) (by simp)]
    erw [reactionVector_outflow, fullyOpen_reaction_outflow]
    simp [outflowReaction, Complex.massActionMonomial, singletonComplex, Pi.single_apply]
  rw [h1, h2, h3]
  ring

/-- **The field of a fully open network points strictly inwards on the coordinate faces.**

At a nonnegative concentration `x` with `x s = 0`, the `s`-component of the mass-action field of
the fully open extension is at least the inflow rate constant of `s`, and hence positive.  The
inflow pseudo-reaction `0 → s` is responsible for the strict positivity; the outflow
pseudo-reaction `s → 0` contributes `0` because `x s = 0`; and the original reactions contribute
nonnegatively, because a reaction consuming `s` has a vanishing rate at `x s = 0` while a
reaction producing `s` has a nonnegative reaction vector. -/
theorem fullyOpen_field_pos_of_nonneg_of_eq_zero (N : Network S) (κ : N.fullyOpen.RateConstants)
    (x : Concentration S) (hx : x.Nonnegative) (s : S) (hxs : x s = 0) :
    0 < N.fullyOpen.massActionVectorField κ x s := by
  rw [fullyOpen_massActionVectorField_eq]
  have h1 : 0 ≤ ∑ r : N.R, κ.k (Sum.inl r) * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r s := by
    refine Finset.sum_nonneg fun r _ => ?_
    by_cases hs0 : (N.reaction r).source s = 0
    · have hmono : 0 ≤ (N.reaction r).source.massActionMonomial x :=
        Complex.massActionMonomial_nonneg hx _
      have hvec : 0 ≤ N.reactionVector r s := by
        rw [reactionVector_apply]
        have hzero : ((N.reaction r).source s : ℝ) = 0 := by exact_mod_cast hs0
        simp only [hzero, sub_zero]
        have : 0 ≤ ((N.reaction r).target s : ℝ) := by
          exact_mod_cast (Nat.zero_le ((N.reaction r).target s))
        exact this
      exact mul_nonneg (mul_nonneg (κ.positive _).le hmono) hvec
    · have hpos : 0 < (N.reaction r).source s := by omega
      have hmono : (N.reaction r).source.massActionMonomial x = 0 := by
        unfold Complex.massActionMonomial
        refine Finset.prod_eq_zero (Finset.mem_univ s) ?_
        rw [hxs]
        exact zero_pow (by omega)
      rw [hmono, mul_zero, zero_mul]
  have h2 : 0 < κ.k (Sum.inr (Sum.inl s)) := κ.positive _
  have h3 : κ.k (Sum.inr (Sum.inr s)) * x s = 0 := by rw [hxs, mul_zero]
  linarith

/-- **A fully open network has no boundary steady state.**  The field of a fully open network does
not vanish at any nonnegative concentration which is not strictly positive.  This is the
"no boundary steady states" hypothesis of the conditional odd-degree argument, and it is *automatic* for fully open
networks. -/
theorem fullyOpen_noBoundarySteadyState (N : Network S) (κ : N.fullyOpen.RateConstants)
    (x : Concentration S) (hx : x.Nonnegative) (hnpos : ¬ x.Positive) :
    N.fullyOpen.massActionVectorField κ x ≠ 0 := by
  by_contra hcon
  obtain ⟨s, hs⟩ : ∃ s, x s = 0 := by
    by_contra hcon2
    push Not at hcon2
    refine hnpos (fun s' => ?_)
    exact lt_of_le_of_ne (hx s') (Ne.symm (hcon2 s'))
  have hzero : N.fullyOpen.massActionVectorField κ x s = 0 := congrFun hcon s
  have hpos := N.fullyOpen_field_pos_of_nonneg_of_eq_zero κ x hx s hs
  rw [hzero] at hpos
  exact absurd hpos (lt_irrefl _)

/-- **The projection is injective when the stoichiometric subspace is everything.** -/
theorem stoichProj_injective_of_stoichSubspace_eq_top (N : Network S)
    (h : N.stoichSubspace = ⊤) : Function.Injective N.stoichProj := by
  intro a b hab
  have ha : a ∈ N.stoichSubspace := by rw [h]; exact Submodule.mem_top
  have hb : b ∈ N.stoichSubspace := by rw [h]; exact Submodule.mem_top
  have h1 : N.stoichChart (N.stoichProj a) = a := N.stoichChart_stoichProj ha
  have h2 : N.stoichChart (N.stoichProj b) = b := N.stoichChart_stoichProj hb
  have h3 : N.stoichChart (N.stoichProj a) = N.stoichChart (N.stoichProj b) :=
    congrArg N.stoichChart hab
  rw [h1, h2] at h3
  exact h3

/-- **The reduced field of a fully open network does not vanish on the class boundary.**  This is
the chart-coordinate form of `Network.fullyOpen_noBoundarySteadyState`: a fully open network has
no boundary steady state in any compatibility class, so the "no boundary steady states" hypothesis
of the parity theorem is discharged for fully open networks. -/
theorem fullyOpen_steadyStateMap_ne_zero_on_classBoundary (N : Network S)
    (κ : N.fullyOpen.RateConstants) (c : Concentration S) (y : ClassCoord (N.fullyOpen))
    (hy : y ∈ N.fullyOpen.classBoundary c) :
    N.fullyOpen.steadyStateMap κ c y ≠ 0 := by
  intro hzero
  have hxnn : Concentration.Nonnegative (N.fullyOpen.affineChart c y) :=
    (mem_nonnegativeClassRegion_iff (N.fullyOpen) c y).mp hy.1
  have hxnp : ¬ Concentration.Positive (N.fullyOpen.affineChart c y) := hy.2
  have hF : N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y) ≠ 0 :=
    N.fullyOpen_noBoundarySteadyState κ (N.fullyOpen.affineChart c y) hxnn hxnp
  have hinj := stoichProj_injective_of_stoichSubspace_eq_top (N.fullyOpen)
    (stoichSubspace_fullyOpen_eq_top N)
  have hproj : N.fullyOpen.stoichProj
      (N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y)) ≠ 0 := by
    intro hz
    have hz' : N.fullyOpen.stoichProj
        (N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y))
        = N.fullyOpen.stoichProj 0 := by rw [hz, map_zero]
    exact hF (hinj hz')
  have hred : N.fullyOpen.steadyStateMap κ c y =
      N.fullyOpen.stoichProj (N.fullyOpen.massActionVectorField κ (N.fullyOpen.affineChart c y)) := by
    simp only [Network.steadyStateMap, reducedField]
  rw [hred] at hzero
  exact hproj hzero

/-! ## The parity theorem for a fully open network -/

/-- **The parity theorem for a fully open network (the conditional odd-degree argument).**

Let `N.fullyOpen` be the fully open extension of `N` with rate constants `κ`, and let `c` be a
compatibility class representative.  Suppose that the zeros of the reduced field in the
nonnegative part of the class are finite, that every positive zero is nondegenerate, and that the
class degree is the total degree `(-1)^{card S}` of the Conradi–Feliu–Mincheva–Wiuf theorem (the
dimension of the class of a fully open network is `card S`, because its stoichiometric subspace
is the whole space).  Then the number of positive steady states in the class is **odd**.

The "no boundary steady states" hypothesis of the conditional odd-degree argument is *not* needed here: it is automatic
for a fully open network, because the inflow pseudo-reactions make the field point strictly
inwards on the coordinate faces (`Network.fullyOpen_steadyStateMap_ne_zero_on_classBoundary`). -/
theorem fullyOpen_card_positiveSteadyStates_odd (N : Network S) (κ : N.fullyOpen.RateConstants)
    (c : Concentration S)
    (hfinN : (N.fullyOpen.steadyStateMap κ c ⁻¹' {0} ∩
      N.fullyOpen.nonnegativeClassRegion c).Finite)
    (hfinP : (N.fullyOpen.positiveSteadyStates_in_class κ c).Finite)
    (hnd : ∀ y ∈ N.fullyOpen.positiveSteadyStates_in_class κ c,
      (N.fullyOpen.reducedJacobian κ c y).det ≠ 0)
    (hdeg : N.fullyOpen.nonnegativeClassDegree κ c hfinN = (-1) ^ (Fintype.card S)) :
    (N.fullyOpen.card_positiveSteadyStates_in_class κ c hfinP) % 2 = 1 := by
  refine N.fullyOpen.card_positiveSteadyStates_odd_of_classDegree_eq_pow_neg_one κ c
    (Fintype.card S) (stoichRank_fullyOpen N) hfinN hfinP ?_ hnd hdeg
  intro y hy
  exact N.fullyOpen_steadyStateMap_ne_zero_on_classBoundary κ c y hy

/-! ## Concrete instances -/

/-- **The fully open network without non-flow reactions has exactly one positive steady state,
hence an odd number of them.**

The network `emptyNet.fullyOpen` is the purely linear flow network `0 → s → 0` on every species:
its field is `κ_in(s) - κ_out(s) * x s`, so the positive steady state is unique
(`Network.emptyNet_unique_steadyState`) and the number of positive steady states is `1`. -/
theorem emptyNet_fullyOpen_card_positiveSteadyStates_eq_one
    (κ : emptyNet.fullyOpen.RateConstants) (T : Finset (Concentration S))
    (hT : ∀ x ∈ T, x.Positive ∧ emptyNet.fullyOpen.IsMassActionSteadyState κ x)
    (hcompl : ∀ x, x.Positive ∧ emptyNet.fullyOpen.IsMassActionSteadyState κ x → x ∈ T) :
    T.card = 1 := by
  -- the explicit positive steady state
  set xstar : Concentration S := fun s =>
    κ.k (Sum.inr (Sum.inl s)) / κ.k (Sum.inr (Sum.inr s)) with hxstar
  have hxstarpos : xstar.Positive := by
    intro s
    dsimp only [xstar]
    exact div_pos (κ.positive _) (κ.positive _)
  have hxstarsteady : emptyNet.fullyOpen.IsMassActionSteadyState κ xstar := by
    intro s
    have h1 := emptyNet_fullyOpen_field (κ := κ) (x := xstar) s
    rw [h1]
    have hx : xstar s = κ.k (Sum.inr (Sum.inl s)) / κ.k (Sum.inr (Sum.inr s)) :=
      congrFun hxstar s
    have hout : κ.k (Sum.inr (Sum.inr s)) ≠ 0 := (κ.positive _).ne'
    rw [hx]
    field_simp [hout]
    ring
  have hxstarT : xstar ∈ T := hcompl xstar ⟨hxstarpos, hxstarsteady⟩
  -- all the positive steady states coincide
  have hsub : T.card ≤ 1 := (Finset.card_le_one).2 fun a ha b hb => by
    obtain ⟨ha1, ha2⟩ := hT a ha
    obtain ⟨hb1, hb2⟩ := hT b hb
    exact emptyNet_unique_steadyState κ ha1 hb1 ha2 hb2
  have hone : 1 ≤ T.card := by
    have hT1 : T = {xstar} := by
      ext y
      simp only [Finset.mem_singleton]
      constructor
      · intro hy
        obtain ⟨hy1, hy2⟩ := hT y hy
        exact emptyNet_unique_steadyState κ hy1 hxstarpos hy2 hxstarsteady
      · intro hy
        subst hy
        exact hxstarT
    rw [hT1]
    simp
  omega

/-- **The number of positive steady states of the fully open network without non-flow reactions is
odd.**  This is the parity theorem of the conditional odd-degree argument in the simplest fully open instance: the
purely linear flow network has exactly one positive steady state. -/
theorem emptyNet_fullyOpen_card_positiveSteadyStates_odd
    (κ : emptyNet.fullyOpen.RateConstants) (T : Finset (Concentration S))
    (hT : ∀ x ∈ T, x.Positive ∧ emptyNet.fullyOpen.IsMassActionSteadyState κ x)
    (hcompl : ∀ x, x.Positive ∧ emptyNet.fullyOpen.IsMassActionSteadyState κ x → x ∈ T) :
    T.card % 2 = 1 := by
  rw [emptyNet_fullyOpen_card_positiveSteadyStates_eq_one κ T hT hcompl]

/-! ### A degree-theoretic instance: the two-species fully open network -/

namespace DegreeExampleParity

open DegreeExample

/-- **The positive steady states of the two-species network are finite.**  The positive part of
the class of the origin is contained in the nonnegative part, whose zero set is finite
(`DegreeExample.hfinN`). -/
theorem hfinP : (N.positiveSteadyStates_in_class rates 0).Finite :=
  hfinN.subset fun y hy =>
    ⟨hy.1, (mem_positiveClassRegion_iff N 0 y).mp hy.2 |>.nonnegative⟩

/-- **Every positive steady state of the two-species network is nondegenerate.**  The reduced
field is the invertible affine map `y ↦ b - y`, so its only zero is `b`, and the reduced Jacobian
determinant there is `1`. -/
theorem hnd : ∀ y ∈ N.positiveSteadyStates_in_class rates 0, (N.reducedJacobian rates 0 y).det ≠ 0 := by
  intro y hy
  have hy0 : N.steadyStateMap rates 0 y = 0 := Set.mem_preimage.mp hy.1
  have hyb : y = b := by
    have hy' : y ∈ N.steadyStateMap rates 0 ⁻¹' {0} := Set.mem_preimage.mpr hy0
    rw [steadyStateMap_preimage_zero] at hy'
    exact Set.mem_singleton_iff.mp hy'
  subst hyb
  rw [DegreeExampleCheck.reducedJacobian_det_at_b]
  norm_num

/-- **The class degree of the two-species network is odd.**  The degree is `+1`
(`DegreeExample.nonnegativeClassDegree_eq_one`). -/
theorem hdeg : ∃ j : ℤ, N.nonnegativeClassDegree rates 0 hfinN = 2 * j + 1 :=
  ⟨0, by rw [nonnegativeClassDegree_eq_one]; ring⟩

/-- **The number of positive steady states of the two-species fully open network is odd.**

This is the parity theorem with all its hypotheses checked: the zero set in the nonnegative class
is finite (`DegreeExample.hfinN`), the field does not vanish on the class boundary
(`DegreeExample.boundary_ne_zero`), the unique positive steady state is nondegenerate
(`reducedJacobian_det_at_b`), and the class degree is `+1`, hence odd.  The network is the fully
open extension of the reaction-free network on two species: the four flow reactions
`0 → A`, `A → 0`, `0 → B`, `B → 0`. -/
theorem card_positiveSteadyStates_odd :
    (N.card_positiveSteadyStates_in_class rates 0 hfinP) % 2 = 1 :=
  N.card_positiveSteadyStates_odd rates 0 hfinN hfinP boundary_ne_zero hnd hdeg

/-- **The two-species fully open network has exactly one positive steady state.** -/
theorem card_positiveSteadyStates_eq_one :
    N.card_positiveSteadyStates_in_class rates 0 hfinP = 1 := by
  have htf : hfinP.toFinset = {b} := by
    ext y
    rw [Set.Finite.mem_toFinset]
    constructor
    · intro hy
      have hy0 : N.steadyStateMap rates 0 y = 0 := Set.mem_preimage.mp hy.1
      have hy' : y ∈ N.steadyStateMap rates 0 ⁻¹' {0} := Set.mem_preimage.mpr hy0
      rw [steadyStateMap_preimage_zero] at hy'
      exact Finset.mem_singleton.mpr (Set.mem_singleton_iff.mp hy')
    · intro hyb
      have hyb' : y = b := Finset.mem_singleton.mp hyb
      subst hyb'
      refine ⟨?_, ?_⟩
      · exact Set.mem_preimage.mpr (by rw [steadyStateMap_eq]; simp)
      · exact (mem_positiveClassRegion_iff N 0 b).mpr affineChart_b_positive
  have h1 : N.card_positiveSteadyStates_in_class rates 0 hfinP = hfinP.toFinset.card := rfl
  rw [h1, htf]
  simp

end DegreeExampleParity

end Network

end CRNT
