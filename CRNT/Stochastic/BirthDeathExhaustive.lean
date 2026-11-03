import CRNT.Stochastic.Absorbing
import CRNT.Stochastic.ConservativeClasses
import CRNT.Flux.PSemiflow

/-!
# Birth/death exhaustivity and stochastic irreducibility structure

Following the structural irreducibility theory for stochastic CRNs, birth exhaustivity is
the existence of a finite reaction cascade that can generate every species starting from
zero-source reactions.  Death exhaustivity is the dual property for the reversed network.
Together with an integer-lattice condition these are the graph/lattice ingredients behind
whole-orthant irreducibility.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Reaction network obtained by reversing every reaction channel. -/
def reverseNetwork (N : Network S) : Network S where
  R := N.R
  decEqR := N.decEqR
  fintypeR := N.fintypeR
  reaction := fun r => { source := (N.reaction r).target, target := (N.reaction r).source }

/-- Inductively birth-generable species.  A reaction may generate a target species once
all species occurring in its source complex are already generable. -/
inductive BirthGenerable (N : Network S) : S → Prop
  | ofReaction (r : N.R) (s : S)
      (hs : 0 < (N.reaction r).target s)
      (hsrc : ∀ t : S, 0 < (N.reaction r).source t → N.BirthGenerable t) :
      N.BirthGenerable s

/-- Every species is obtainable by a birth cascade. -/
def BirthExhaustive (N : Network S) : Prop :=
  ∀ s : S, N.BirthGenerable s

/-- Death exhaustivity is birth exhaustivity of the reversed CRN. -/
def DeathExhaustive (N : Network S) : Prop :=
  N.reverseNetwork.BirthExhaustive

/-- A species generated directly by a zero-source reaction is birth-generable. -/
theorem birthGenerable_of_zeroSourceReaction (N : Network S)
    {r : N.R} (hsrc : (N.reaction r).source = 0)
    {s : S} (htgt : 0 < (N.reaction r).target s) :
    N.BirthGenerable s := by
  apply BirthGenerable.ofReaction r s htgt
  intro t ht
  simp [hsrc] at ht

/-- Birth exhaustivity excludes an absorbing origin. -/
theorem zero_not_absorbing_of_birthExhaustive (N : Network S) [Nonempty S]
    (hbirth : N.BirthExhaustive) : ¬ N.IsAbsorbingCount (fun _ => 0) := by
  have exists_zeroSource_of_birthGenerable :
      ∀ {s : S}, N.BirthGenerable s →
        ∃ r : N.R, (N.reaction r).source = 0 ∧ (N.reaction r).target ≠ 0 := by
    intro s hs
    induction hs with
    | ofReaction r s htgt hsrc ih =>
        by_cases hz : (N.reaction r).source = 0
        · refine ⟨r, hz, ?_⟩
          intro ht
          have heq := congrFun ht s
          change (N.reaction r).target s = 0 at heq
          omega
        · have hex : ∃ t : S, 0 < (N.reaction r).source t := by
            by_contra hnone
            push_neg at hnone
            apply hz
            funext t
            have ht := hnone t
            simp only [Pi.zero_apply]
            omega
          obtain ⟨t, ht⟩ := hex
          exact ih t ht
  let s : S := Classical.choice inferInstance
  obtain ⟨r, hr, ht⟩ := exists_zeroSource_of_birthGenerable (hbirth s)
  exact N.zero_not_absorbing_of_zeroSourceReaction hr ht

/-- Whole-orthant stochastic irreducibility. -/
def CountLatticeIrreducible (N : Network S) : Prop :=
  ∀ n m : S → ℕ, N.CountCommunicates n m

/-- Irreducibility forces full integer-lattice generation. -/
theorem generatesFullIntegerLattice_of_irreducible (N : Network S)
    (hirr : N.CountLatticeIrreducible) : N.GeneratesFullIntegerLattice := by
  apply top_unique
  intro z hz
  let m : S → ℕ := fun s => if h : 0 ≤ z s then Int.toNat (z s) else 0
  let n : S → ℕ := fun s => if h : 0 ≤ z s then 0 else Int.toNat (-z s)
  have hclass : N.SameIntegerStoichClass m n :=
    N.sameIntegerStoichClass_of_reachable (hirr n m).1
  have hdiff : countDifference m n = z := by
    funext s
    simp only [countDifference, m, n]
    by_cases h : 0 ≤ z s
    · simp [h, Int.toNat_of_nonneg h]
    · have hn : 0 ≤ -z s := by omega
      simp [h, Int.toNat_of_nonneg hn]
  rw [SameIntegerStoichClass, hdiff] at hclass
  exact hclass

/-- Irreducibility excludes nontrivial modular invariants. -/
theorem no_congruence_separation_of_irreducible (N : Network S)
    (hirr : N.CountLatticeIrreducible) {d : ℕ} {q : S → ℤ}
    (hq : N.IsCongruenceInvariant d q) (n m : S → ℕ) :
    Int.ModEq d (integerObservable q n) (integerObservable q m) := by
  have h := (hirr n m).1
  exact (N.integerObservable_modEq_of_reachable hq h).symm

/-- Adding a nonnegative count buffer preserves enabledness of a reaction. -/
theorem enabled_add_right (N : Network S) {n z : S → ℕ} {r : N.R}
    (h : N.Enabled n r) : N.Enabled (fun s => n s + z s) r := by
  intro s
  exact le_trans (h s) (Nat.le_add_right _ _)

/-- Firing commutes with adding a count buffer, provided the reaction was already enabled. -/
theorem fireCount_add_right (N : Network S) {n z : S → ℕ} {r : N.R}
    (h : N.Enabled n r) :
    N.fireCount (fun s => n s + z s) r = fun s => N.fireCount n r s + z s := by
  have hz := N.enabled_add_right (z := z) h
  funext s
  simp [fireCount, h, hz]
  have hs := h s
  omega

/-- One stochastic reaction step is preserved after adding the same count buffer to
both endpoints. -/
theorem countStep_add_right (N : Network S) {n m z : S → ℕ}
    (h : N.CountStep n m) :
    N.CountStep (fun s => n s + z s) (fun s => m s + z s) := by
  rcases h with ⟨r, hen, rfl⟩
  refine ⟨r, N.enabled_add_right (z := z) hen, ?_⟩
  exact (N.fireCount_add_right (z := z) hen).symm

/-- Finite stochastic reachability is translation-monotone in the nonnegative orthant. -/
theorem countReachable_add_right (N : Network S) {n m z : S → ℕ}
    (h : N.CountReachable n m) :
    N.CountReachable (fun s => n s + z s) (fun s => m s + z s) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hreach hstep ih =>
      exact Relation.ReflTransGen.tail ih (N.countStep_add_right (z := z) hstep)

/-- Left-handed form of `countReachable_add_right`. -/
theorem countReachable_add_left (N : Network S) {n m z : S → ℕ}
    (h : N.CountReachable n m) :
    N.CountReachable (fun s => z s + n s) (fun s => z s + m s) := by
  simpa [Nat.add_comm] using N.countReachable_add_right (z := z) h

/-- Communication is compatible with pointwise addition of count vectors. -/
theorem countCommunicates_add (N : Network S) {a b c d : S → ℕ}
    (hab : N.CountCommunicates a b) (hcd : N.CountCommunicates c d) :
    N.CountCommunicates (fun s => a s + c s) (fun s => b s + d s) := by
  constructor
  · exact Relation.ReflTransGen.trans
      (N.countReachable_add_right (z := c) hab.1)
      (N.countReachable_add_left (z := b) hcd.1)
  · exact Relation.ReflTransGen.trans
      (N.countReachable_add_right (z := d) hab.2)
      (N.countReachable_add_left (z := a) hcd.2)

/-- The elementary count state with one molecule of species `s`. -/
def unitCount (s : S) : S → ℕ := fun t => if t = s then 1 else 0

/-- A count state supported on one species. -/
def singleCount (s : S) (k : ℕ) : S → ℕ := fun t => if t = s then k else 0

private theorem singleCount_succ (s : S) (k : ℕ) :
    singleCount s (k + 1) = fun t => singleCount s k t + unitCount s t := by
  funext t
  by_cases h : t = s <;> simp [singleCount, unitCount, h]

/-- Communication between zero and the elementary unit state of a species extends to
communication between zero and any multiplicity of that species. -/
theorem communicates_zero_singleCount (N : Network S) (s : S)
    (hunit : N.CountCommunicates (fun _ => 0) (unitCount s)) :
    ∀ k : ℕ, N.CountCommunicates (fun _ => 0) (singleCount s k) := by
  intro k
  induction k with
  | zero =>
      have hz : singleCount s 0 = (fun _ => 0) := by
        funext t
        simp [singleCount]
      rw [hz]
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | succ k ih =>
      have hsum := N.countCommunicates_add ih hunit
      simpa [singleCount_succ, Nat.succ_eq_add_one] using hsum

private def restrictCount (n : S → ℕ) (F : Finset S) : S → ℕ :=
  fun s => if s ∈ F then n s else 0

private theorem restrictCount_insert {n : S → ℕ} {F : Finset S} {s : S} (hs : s ∉ F) :
    restrictCount n (insert s F) = fun t => restrictCount n F t + singleCount s (n s) t := by
  funext t
  by_cases hts : t = s
  · subst t
    simp [restrictCount, singleCount, hs]
  · by_cases htF : t ∈ F
    · simp [restrictCount, singleCount, hts, htF]
    · simp [restrictCount, singleCount, hts, htF]

private theorem communicates_zero_restrictCount (N : Network S) (n : S → ℕ)
    (hunit : ∀ s : S, N.CountCommunicates (fun _ => 0) (unitCount s)) :
    ∀ F : Finset S, N.CountCommunicates (fun _ => 0) (restrictCount n F) := by
  intro F
  induction F using Finset.induction_on with
  | empty =>
      have hz : restrictCount n ∅ = (fun _ => 0) := by
        funext t
        simp [restrictCount]
      rw [hz]
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @insert s F hs ih =>
      have hsng := N.communicates_zero_singleCount s (hunit s) (n s)
      have hsum := N.countCommunicates_add ih hsng
      rw [restrictCount_insert hs]
      simpa using hsum

/-- If every elementary one-molecule state communicates with zero, then every count
state communicates with zero. -/
theorem communicates_zero_of_elementary (N : Network S)
    (hunit : ∀ s : S, N.CountCommunicates (fun _ => 0) (unitCount s))
    (n : S → ℕ) : N.CountCommunicates (fun _ => 0) n := by
  have h := communicates_zero_restrictCount N n hunit Finset.univ
  have hall : restrictCount n Finset.univ = n := by
    funext t
    simp [restrictCount]
  rwa [hall] at h

/-- **Elementary-state irreducibility criterion.** The entire nonnegative count
orthant is irreducible once zero communicates with each one-molecule basis state.
This is the discrete-reaction-network criterion underlying the usual stochastic
irreducibility proofs. -/
theorem countLatticeIrreducible_of_elementaryCommunication
    (N : Network S)
    (hunit : ∀ s : S, N.CountCommunicates (fun _ => 0) (unitCount s)) :
    N.CountLatticeIrreducible := by
  intro n m
  have hn := N.communicates_zero_of_elementary hunit n
  have hm := N.communicates_zero_of_elementary hunit m
  exact ⟨Relation.ReflTransGen.trans hn.2 hm.1,
    Relation.ReflTransGen.trans hm.2 hn.1⟩

/-!
### Why the earlier signed-lattice criterion was removed

Birth exhaustivity, death exhaustivity, `GeneratesFullIntegerLattice`, and full real
stoichiometric rank are **not sufficient** for whole-orthant irreducibility.  The
Gupta--Khammash theorem uses a nonnegative reaction-column-span condition, not merely
the signed `ℤ`-span encoded by `GeneratesFullIntegerLattice`.  The regression example
`test/StochasticBirthDeathCounterexample.lean` formalizes a two-species counterexample
to the former statement.  The theorem above records the exact elementary-state
criterion that the missing nonnegative-semigroup argument must establish.
-/

/-- A strictly positive conservation law rules out whole-orthant irreducibility whenever
there are at least two count states with different conserved totals. -/
theorem not_countLatticeIrreducible_of_strictPSemiflow
    (N : Network S) {w : S → ℝ} (hw : N.IsStrictPSemiflow w)
    (hS : Nonempty S) : ¬ N.CountLatticeIrreducible := by
  intro hirr
  let toConc : (S → ℕ) → Concentration S := fun n s => (n s : ℝ)
  have hstepTotal : ∀ {n m : S → ℕ}, N.CountStep n m →
      weightedTotal w (toConc n) = weightedTotal w (toConc m) := by
    intro n m hstep
    rcases hstep with ⟨r, hen, rfl⟩
    have hcons : ∑ s : S, w s * N.reactionVector r s = 0 :=
      (N.conservationLaw_iff_mem_orthSum w).2 hw.1 r
    have hcoord : ∀ s : S,
        (toConc (N.fireCount n r) s - toConc n s) = N.reactionVector r s := by
      intro s
      have hz := congrFun (N.countDifference_fireCount hen) s
      simp only [countDifference, integerReactionVector] at hz
      dsimp [toConc]
      exact_mod_cast hz
    unfold weightedTotal
    have hzero : ∑ s : S,
        w s * (toConc (N.fireCount n r) s - toConc n s) = 0 := by
      calc
        (∑ s : S, w s * (toConc (N.fireCount n r) s - toConc n s)) =
            ∑ s : S, w s * N.reactionVector r s := by
              apply Finset.sum_congr rfl
              intro s _
              rw [hcoord s]
        _ = 0 := hcons
    simp only [mul_sub, Finset.sum_sub_distrib] at hzero
    linarith
  have hreachTotal : ∀ {n m : S → ℕ}, N.CountReachable n m →
      weightedTotal w (toConc n) = weightedTotal w (toConc m) := by
    intro n m hreach
    induction hreach with
    | refl => rfl
    | tail hreach hstep ih =>
        exact ih.trans (hstepTotal hstep)
  let s0 : S := Classical.choice hS
  let e : S → ℕ := fun s => if s = s0 then 1 else 0
  have hreach := (hirr (fun _ => 0) e).1
  have htot := hreachTotal hreach
  have heval : weightedTotal w (toConc e) = w s0 := by
    unfold weightedTotal
    rw [Finset.sum_eq_single s0]
    · simp [toConc, e]
    · intro s _ hs
      simp [toConc, e, hs]
    · simp
  have hzero : weightedTotal w (toConc (fun _ => 0)) = 0 := by
    simp [weightedTotal, toConc]
  rw [hzero, heval] at htot
  exact (hw.2 s0).ne' htot.symm

end Network
end CRNT
