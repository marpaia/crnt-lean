import CRNT.Stochastic.EndotacticTierPositiveRecurrence
import CRNT.Stochastic.EndotacticTierDomination

/-!
# The count-lattice tier estimate

This module adds the **quantitative** part of the count-lattice tier theory of leaf **P7**
(positive recurrence and non-explosivity of stochastic mass-action systems on infinite state
spaces): the finiteness of the set of counts in a tier band, and the explicit cardinality bound
of that set.

## 1. The Anderson--Cappelletti--Kim--Nguyen tier construction

Anderson--Cappelletti--Kim--Nguyen (2020, _Persistence and absence of infinite trajectories for
strongly endotactic chemical reaction networks_) organise the complexes of a network into
**tiers** by the level sets of a linear functional `w ↦ ∑_s w_s y_s` read on the complexes `y`.
The *top tier* is the `w`-maximal face of the Newton polytope; the reactions out of the top
tier do not ascend the tier potential, and at least one of them descends it strictly.  The tier
construction is what produces the **strictly negative drift** of the Lyapunov function
`V (x) = ∑_s w_s x_s` of the stochastic mass-action chain, and hence the
Anderson--Cappelletti--Kim--Nguyen conclusions: non-explosion, a Foster hitting-time bound,
positive recurrence with a strictly positive stationary law, and geometric ergodicity.

The *count-lattice* reading of that construction is the repository's
`CRNT.Network.CountTier` (`CRNT.Stochastic.EndotacticTierPositiveRecurrence`):

* `countTierPotential` is the tier potential of a complex, `countTierTop` is the `w`-maximal
  face of the Newton polytope, and `countTierDescent_of_stronglyEndotacticStd` transfers the
  descent from the repository's `StronglyEndotacticStd`;
* `CountTier` collects the tier weight (strictly positive), the tier chain, the top-tier
  descent, the **tier separation** `inflow` (an ascending reaction has the empty source
  complex, hence a count-independent propensity) and the **coverage** (every species is
  consumed by a strictly descending top-tier reaction);
* the drift of the tier Lyapunov function is then computed exactly
  (`tierDrift_multiplicative`), and the Foster conclusions follow: `tierDrift_le_of`,
  `tier_nonExplosion`, `tierFoster_hitting_time`, `tier_positiveRecurrence`,
  `tier_geometricErgodic`.

## 2. What this module adds: the quantitative tier estimate

In the continuous theory the role of the tier potential is played by a **bounded** function on
the orthant: the Anderson--Cappelletti--Kim--Nguyen proof controls the drift outside a
**compact** set, and the compactness is what makes the exceptional set harmless.  On the count
lattice `ℕ^S` there is no compactness; the replacement is the **tier estimate**: the set of
counts whose tier value lies in a bounded band is a **finite** set, and its size is bounded
explicitly by the number of lattice points of the corresponding box.

This module provides it:

* `countTierValue` -- the tier of a **count**, `∑_s w_s n_s`: the count-lattice counterpart of
  the tier potential of a complex;
* `countTier_card_le` -- the tier band `[a, b]` contains only finitely many counts;
* `countTier_card_le'` -- the number of counts in the tier band `[a, b]` is at most
  `∏_s (⌊b / w s⌋₊ + 1)`, the number of lattice points of the box `∏_s [0, ⌊b / w s⌋₊]`
  (`countTier_toFinset_card_le'` is the variant in which the finiteness hypothesis is explicit and
  the left-hand side is the genuine cardinality of the band);
* `countTierValue_ge_complexTier` -- the tier of a count dominates the tier potential of every
  complex that is *enabled* at that count;
* `countTierDrift_exceptional_card_le` -- the exceptional set of the count-lattice tier drift
  certificate is a **tier band**, hence finite, with the explicit bound of the tier estimate;
* `countTierBalance_exceptional_card_le` -- the same for the balanced tier structure;
* `Examples.EndotacticCounterexample.countTier_card_le_net` -- an instance, on the very network
  for which the tier domination fails.

## 3. The `CountTierBalance` correction

`CRNT.Network.CountTierBalance` (`CRNT.Stochastic.EndotacticTierDomination`) replaces the tier
*separation* of `CountTier` by the weaker **balance** condition: an ascending reaction with a
nonempty source complex is cancelled by a descending reaction with the **same** source complex
(the two have the same falling factorial, so the truncation obstruction cannot occur), and every
species is consumed by a strictly descending top-tier reaction.  The Lyapunov function is the
same linear functional `∑_s w_s n_s`, so the tier estimate of this module applies verbatim to
the balanced structure as well (`countTierBalance_exceptional_card_le`).

## 4. What remains open

* **The general multispecies Anderson--Cappelletti--Kim--Nguyen theorem is still open.**  The
  hypothesis `CRNT.Network.StronglyEndotacticStd` alone does not produce a tier weight `w` with
  either the tier domination or the balance property: that *deterministic tier-weight
  construction* is the genuinely new input of the Anderson--Cappelletti--Kim--Nguyen paper and
  it is missing here.
* **The naive tier-domination route is refuted.**
  `CRNT.Examples.EndotacticCounterexample.topTier_does_not_dominate` exhibits a
  `StronglyEndotacticStd` network (the two-species network `0 → A`, `A → 0`, `0 → B`, `B → 0`)
  for which, along the escape direction `n k = (0, k)`, the count-lattice falling factorial of
  the lower tier `B` is `k` while that of the top tier `A` is `0`: the top tier does **not**
  dominate the lower tiers, so the "top-tier monomial dominates the lower-tier monomials" step
  of the continuous proof has no count-lattice analogue.
* What *is* proved here is the quantitative part of the count-lattice tier theory: the tier
  estimate (finiteness and the explicit cardinality bound of a tier band), the relation between
  the tier of a count and the tier potential of a complex, and the consequence that the
  exceptional set of the tier drift certificate is a finite tier band.

Depends on: `CRNT.Stochastic.EndotacticTierPositiveRecurrence`,
`CRNT.Stochastic.EndotacticTierDomination`.
-/

open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. The tier of a count -/

omit [DecidableEq S] in
/-- **The tier value of a count.**  For a strictly positive weight `w`, the tier of a count `n`
is the value of the tier potential read at the count, `∑_s w s * n s`.  This is the count-lattice
analogue of the tier of a complex. -/
noncomputable def countTierValue (w : S → ℝ) (n : S → ℕ) : ℝ := linearObservable w n

omit [DecidableEq S] in
/-- **The tier value of a count is a sum.**  The tier of a count is the weighted sum of the
counts. -/
theorem countTierValue_eq_sum (w : S → ℝ) (n : S → ℕ) :
    countTierValue w n = ∑ s, w s * (n s : ℝ) := rfl

omit [DecidableEq S] in
/-- **The tier potential of a complex is a sum.**  The tier potential of a complex is the
weighted sum of its multiplicities. -/
theorem countTierPotential_eq_sum (w : S → ℝ) (y : Complex S) :
    countTierPotential w y = ∑ s, w s * (y s : ℝ) := by
  simp [countTierPotential, complexWValue, dotProduct, exponentVector]

omit [DecidableEq S] in
/-- **The tier of a count is the tier potential read at the count.**  The two notions coincide:
`Complex S = S → ℕ`, so a complex *is* a count, and the tier value of a count and the tier
potential of a complex are the same functional `∑_s w_s (·) s`. -/
theorem countTierValue_eq_countTierPotential (w : S → ℝ) (y : Complex S) :
    countTierValue w y = countTierPotential w y := by
  rw [countTierValue_eq_sum, countTierPotential_eq_sum]

/-- **The tier value of a count is nonnegative.** -/
theorem countTierValue_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s) (n : S → ℕ) :
    0 ≤ countTierValue w n :=
  linearObservable_nonneg_of_positive hw n

/-! ## 2. The count-lattice tier estimate -/

/-- **The sublevel sets of the tier value are finite.**  This is the count-lattice counterpart
of the fact that the tier potential is bounded on a compact set of the orthant. -/
theorem countTierValue_finiteSublevel {w : S → ℝ} (hw : ∀ s, 0 < w s) (R : ℝ) :
    {n : S → ℕ | countTierValue w n ≤ R}.Finite :=
  finite_linearObservable_le w hw R

set_option linter.unusedVariables false in
/-- **The count-lattice tier estimate.**  For a strictly positive weight `w`, the set of counts
whose tier value lies in a bounded interval `[a, b]` is finite. -/
theorem countTier_card_le {w : S → ℝ} (hw : ∀ s, 0 < w s) {a b : ℝ} (hab : a ≤ b) :
    {n : S → ℕ | a ≤ countTierValue w n ∧ countTierValue w n ≤ b}.Finite :=
  (countTierValue_finiteSublevel hw b).subset fun _ hn => hn.2

set_option linter.unusedVariables false in
/-- **The tier estimate with an explicit count.**  The number of counts in the tier interval
`[a, b]` is at most `∏_s (⌊b / w s⌋₊ + 1)`, the number of lattice points of the box
`∏_s [0, ⌊b / w s⌋₊]`.

This is the version of the estimate in which the finiteness hypothesis of `countTier_card_le` is
made explicit, so that the left-hand side is the genuine cardinality of the tier band. -/
theorem countTier_toFinset_card_le' {w : S → ℝ} (hw : ∀ s, 0 < w s) {a b : ℝ} (hab : a ≤ b)
    (hA : {n : S → ℕ | a ≤ countTierValue w n ∧ countTierValue w n ≤ b}.Finite) :
    hA.toFinset.card ≤ ∏ s, (⌊b / w s⌋₊ + 1) := by
  classical
  set box : Finset (S → ℕ) :=
    Fintype.piFinset fun s => Finset.range (⌊b / w s⌋₊ + 1) with hboxdef
  -- every count of the tier band is a lattice point of the box
  have hsub : {n : S → ℕ | a ≤ countTierValue w n ∧ countTierValue w n ≤ b} ⊆
      (box : Set (S → ℕ)) := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro s
    rw [Finset.mem_range]
    have hterm : w s * (n s : ℝ) ≤ countTierValue w n := by
      rw [countTierValue_eq_sum]
      exact Finset.single_le_sum (fun t _ => mul_nonneg (hw t).le (Nat.cast_nonneg _))
        (Finset.mem_univ s)
    have hdiv : (n s : ℝ) ≤ b / w s := by
      rw [le_div_iff₀ (hw s)]
      linarith
    exact Nat.lt_succ_of_le (Nat.le_floor hdiv)
  have hsubF : hA.toFinset ⊆ box := by
    intro n hn
    exact hsub (hA.mem_toFinset.mp hn)
  have hcard : hA.toFinset.card ≤ box.card := Finset.card_le_card hsubF
  rw [hboxdef, Fintype.card_piFinset] at hcard
  simp only [Finset.card_range] at hcard
  exact hcard

set_option linter.unusedVariables false in
/-- **The tier estimate with an explicit count.**  The number of counts in the tier interval
`[a, b]` is at most `∏_s (⌊b / w s⌋₊ + 1)`.

The cardinality is written as `Nat.card` (equivalently `Set.ncard`); for the finite tier band of
`countTier_card_le` this is the genuine cardinality, by `Set.ncard_eq_toFinset_card`. -/
theorem countTier_card_le' {w : S → ℝ} (hw : ∀ s, 0 < w s) {a b : ℝ} (hab : a ≤ b) :
    Nat.card {n : S → ℕ | a ≤ countTierValue w n ∧ countTierValue w n ≤ b}
      ≤ ∏ s, (⌊b / w s⌋₊ + 1) := by
  have hA : {n : S → ℕ | a ≤ countTierValue w n ∧ countTierValue w n ≤ b}.Finite :=
    countTier_card_le hw hab
  have h1 : Nat.card {n : S → ℕ | a ≤ countTierValue w n ∧ countTierValue w n ≤ b}
      = hA.toFinset.card := by
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hA]
  rw [h1]
  exact countTier_toFinset_card_le' hw hab hA

/-! ## 3. The relation to the complex tier -/

omit [DecidableEq S] in
/-- **The count tier dominates the complex tier.**  The tier of a count is at least the tier
potential of every complex that is *enabled* at that count: if `y ≤ n` coordinatewise then
`∑_s w_s y_s ≤ ∑_s w_s n_s`. -/
theorem countTierValue_ge_complexTier {w : S → ℝ} (hw : ∀ s, 0 < w s) (n : S → ℕ) (y : Complex S)
    (hy : ∀ s, y s ≤ n s) : countTierPotential w y ≤ countTierValue w n := by
  rw [countTierPotential_eq_sum, countTierValue_eq_sum]
  exact Finset.sum_le_sum fun s _ =>
    mul_le_mul_of_nonneg_left (by exact_mod_cast hy s) (hw s).le

/-- **The count tier dominates the tier potential of every enabled reaction.**  If the reaction
`r` is enabled at the count `n` -- that is, its source complex is dominated by `n`
coordinatewise -- then the tier of `n` is at least the tier potential of the source of `r`. -/
theorem countTierValue_ge_complexTier_of_enabled {S : Type} [DecidableEq S] [Fintype S]
    {w : S → ℝ} (hw : ∀ s, 0 < w s) {N : Network S} {n : S → ℕ} {r : N.R}
    (hen : N.Enabled n r) :
    countTierPotential w (N.reaction r).source ≤ countTierValue w n :=
  countTierValue_ge_complexTier hw n (N.reaction r).source hen

/-! ## 4. The drift consequence -/

/-- **The tier estimate bounds the exceptional set of the tier drift.**  The exceptional set of
the count-lattice tier drift certificate is a **tier band** -- the set of the counts whose tier
value does not exceed a bound -- hence it is finite, and its cardinality is bounded by the
product of the box sizes of the tier estimate.

This is the count-lattice replacement of the compactness of the Anderson--Cappelletti--Kim--Nguyen
proof: on the count lattice the exceptional set of the drift is finite *because* it is a tier
band, and the tier estimate says how large it can be. -/
theorem countTierDrift_exceptional_card_le {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (T : CountTier N) :
    ∃ D : CountTierDrift N κ, ∃ R : ℝ,
      D.C = {n | countTierValue T.w n ≤ R} ∧ D.C.ncard ≤ ∏ s, (⌊R / T.w s⌋₊ + 1) := by
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierDrift_multiplicative N κ T
  have hV : ∀ n : S → ℕ, 0 ≤ countTierValue T.w n := countTierValue_nonneg T.hw
  have hfinV : ∀ R : ℝ, {n : S → ℕ | countTierValue T.w n ≤ R}.Finite :=
    countTierValue_finiteSublevel T.hw
  have hVdef : CountLyapunov N κ T = countTierValue T.w := rfl
  refine ⟨{ V := countTierValue T.w
            hV := hV
            hfinV := hfinV
            c := 1
            hc := one_pos
            C := {n | countTierValue T.w n ≤ (K + 1) / ε}
            hC := hfinV _
            hdrift := ?_ }, (K + 1) / ε, rfl, ?_⟩
  · intro n hn
    have hVn : (K + 1) / ε < countTierValue T.w n := by
      simpa [Set.mem_ofPred_eq] using hn
    have hεV : K + 1 < ε * countTierValue T.w n := by
      have h := (div_lt_iff₀ hε).mp hVn
      linarith
    have h := hdrift n
    rw [hVdef] at h
    linarith
  · -- the tier band is finite, and the tier estimate bounds its cardinality
    have hR : 0 ≤ (K + 1) / ε := by
      have hK1 : 0 ≤ K + 1 := by linarith
      exact div_nonneg hK1 hε.le
    have hband : ({n : S → ℕ | countTierValue T.w n ≤ (K + 1) / ε}).ncard
        ≤ ({n : S → ℕ | 0 ≤ countTierValue T.w n ∧
            countTierValue T.w n ≤ (K + 1) / ε}).ncard := by
      refine Set.ncard_le_ncard ?_ (countTier_card_le T.hw (a := 0) (b := (K + 1) / ε) (by linarith))
      intro n hn
      exact ⟨countTierValue_nonneg T.hw n, hn⟩
    have hmain := countTier_card_le' T.hw (a := 0) (b := (K + 1) / ε) (by linarith)
    have hmain' : ({n : S → ℕ | 0 ≤ countTierValue T.w n ∧
        countTierValue T.w n ≤ (K + 1) / ε}).ncard ≤ ∏ s, (⌊((K + 1) / ε) / T.w s⌋₊ + 1) := by
      simpa only [Nat.card_coe_set_eq] using hmain
    exact hband.trans hmain'

/-- **The tier estimate for the balanced count-lattice tier structure.**  The exceptional set of
the Anderson--Cappelletti--Kim--Nguyen drift of a balanced tier structure is again a tier band,
hence finite with the explicit cardinality bound of the tier estimate. -/
theorem countTierBalance_exceptional_card_le {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) (B : CountTierBalance N κ) :
    ∃ C : Set (S → ℕ), C.Finite ∧ ∃ R : ℝ, C = {n | countTierValue B.w n ≤ R} ∧
      C.ncard ≤ ∏ s, (⌊R / B.w s⌋₊ + 1) := by
  obtain ⟨ε, hε, K, hK, hdrift⟩ := tierBalanceDrift_multiplicative N κ B
  have hfinV : ∀ R : ℝ, {n : S → ℕ | countTierValue B.w n ≤ R}.Finite :=
    countTierValue_finiteSublevel B.hw
  have hR : 0 ≤ (K + 1) / ε := by
    have hK1 : 0 ≤ K + 1 := by linarith
    exact div_nonneg hK1 hε.le
  refine ⟨{n | countTierValue B.w n ≤ (K + 1) / ε}, hfinV _, (K + 1) / ε, rfl, ?_⟩
  have hband : ({n : S → ℕ | countTierValue B.w n ≤ (K + 1) / ε}).ncard
      ≤ ({n : S → ℕ | 0 ≤ countTierValue B.w n ∧ countTierValue B.w n ≤ (K + 1) / ε}).ncard := by
    refine Set.ncard_le_ncard ?_ (countTier_card_le B.hw (a := 0) (b := (K + 1) / ε) (by linarith))
    intro n hn
    exact ⟨countTierValue_nonneg B.hw n, hn⟩
  have hmain := countTier_card_le' B.hw (a := 0) (b := (K + 1) / ε) (by linarith)
  have hmain' : ({n : S → ℕ | 0 ≤ countTierValue B.w n ∧
      countTierValue B.w n ≤ (K + 1) / ε}).ncard ≤ ∏ s, (⌊((K + 1) / ε) / B.w s⌋₊ + 1) := by
    simpa only [Nat.card_coe_set_eq] using hmain
  exact hband.trans hmain'

end Network

/-! ## 5. An instance -/

namespace Examples
namespace EndotacticCounterexample

open Network

/-- **The tier estimate on the strongly endotactic counterexample.**  For the tier weight
`w = (1, 1)` of the two-species network `net` (the network for which
`Examples.EndotacticCounterexample.topTier_does_not_dominate` refutes the naive tier-domination
route), the number of counts whose tier value lies in the band `[0, b]` is at most
`(⌊b⌋₊ + 1)²`.  This is the count-lattice tier estimate on the very network on which the
top-tier domination fails. -/
theorem countTier_card_le_net {b : ℝ} (hb : 0 ≤ b) :
    Nat.card {n : Fin 2 → ℕ | 0 ≤ countTierValue (fun _ => (1 : ℝ)) n ∧
        countTierValue (fun _ => (1 : ℝ)) n ≤ b}
      ≤ (⌊b⌋₊ + 1) * (⌊b⌋₊ + 1) := by
  have h := countTier_card_le' (S := Fin 2) (w := fun _ => (1 : ℝ)) (fun _ => one_pos)
    (a := 0) (b := b) (by linarith)
  rw [Fin.prod_univ_two] at h
  simpa only [div_one] using h

end EndotacticCounterexample
end Examples

end CRNT

/-! ## 6. Axiom audit -/

#print axioms CRNT.Network.countTierValue
#print axioms CRNT.Network.countTierValue_eq_sum
#print axioms CRNT.Network.countTierPotential_eq_sum
#print axioms CRNT.Network.countTierValue_eq_countTierPotential
#print axioms CRNT.Network.countTierValue_nonneg
#print axioms CRNT.Network.countTierValue_finiteSublevel
#print axioms CRNT.Network.countTier_card_le
#print axioms CRNT.Network.countTier_toFinset_card_le'
#print axioms CRNT.Network.countTier_card_le'
#print axioms CRNT.Network.countTierValue_ge_complexTier
#print axioms CRNT.Network.countTierValue_ge_complexTier_of_enabled
#print axioms CRNT.Network.countTierDrift_exceptional_card_le
#print axioms CRNT.Network.countTierBalance_exceptional_card_le
#print axioms CRNT.Examples.EndotacticCounterexample.countTier_card_le_net
