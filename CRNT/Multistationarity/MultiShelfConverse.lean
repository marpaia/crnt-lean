import CRNT.Multistationarity.AdvancedDeficiencyAlgorithm
import CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness
import Mathlib.Basic.Sign.Basic

/-!
# The multi-shelf converse: decomposing a balanced flux into shelf-wise confluence vectors

This module attacks the **converse** direction of the Deficiency One Algorithm (M7) and of the
Advanced Deficiency Algorithm (M8): given a *feasible* system — a log-ratio `μ` and a strictly
positive flux `α` satisfying the two flux balances

* the **lower balance** `∑_r α_r (y'_r − y_r) = 0` (the flux balances at the lower state), and
* the **upper balance** `∑_r α_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0` (the flux balances at the upper
  state `e^{μ}`),

— can the flux be decomposed into **shelf-wise confluence vectors**, i.e. into a family of
fluxes `λ_sh`, each *supported* on a *shelf* `sh` (a part of the reaction set), *strictly
positive* on it, and each satisfying the two balance conditions **on its own shelf**?

The classical answer (Feinberg 1995b; Craciun 2015; Ellison 1998) is that the Deficiency One
Algorithm's flux splits this way, and that the Advanced Deficiency Algorithm *iterates* the
split over a system of shelves.  This module proves the **first, provable step** of that
converse: the **sign decomposition** of the reaction set into *forward* and *backward* parts
relative to the log-ratio, and the **two-shelf decomposition** of a balanced flux.

## The sign decomposition

For a reaction `r` with source `y_r` and target `y'_r`, the **mu-step**

    pairingStep N mu r = <y'_r, mu> - <y_r, mu> = <y'_r - y_r, mu>

is the pairing of the reaction vector with the log-ratio (`pairingStep_eq_reactionVector_pairing`).
A reaction is

* **forward** when its step is positive - the reaction moves *up* in the `mu`-direction
  (`IsForward`, `forwardReactions`);
* **backward** when the step is negative (`IsBackward`, `backwardReactions`);
* **flat** when the step vanishes (`IsFlat`, `flatReactions`).

The three parts partition the reaction set (`signDecomposition_cover`,
`signDecomposition_disjoint_forward_backward`, `signDecomposition_disjoint_forward_flat`,
`signDecomposition_disjoint_backward_flat`), and the lower balance forces the decomposition to
be *non-trivial*: a strictly positive balanced flux has both a forward and a backward reaction
unless every reaction is flat (`signDecomposition_forward_imp_backward`,
`signDecomposition_allFlat_of_no_forward`).  The scalar statement behind this is the
**mu-weighted balance** `sum_r alpha_r <y'_r - y_r, mu> = 0` (`lowerBalance_step_sum`).

In the **rank-one** (deficiency-one) setting - where the stoichiometric subspace is the line
`span {v}` - the step is the reduced coefficient of the reaction times the class pairing
`<v, mu>` (`pairingStep_eq_reducedCoefficient_mul_classPairing`), and the *sign* of the step
computed with `mu` agrees with the sign computed with the *sign-compatible* stoichiometric
vector `sigma` (`rankOne_signDecomposition_agrees`, via `classPairing_sign_agrees`): the forward
and backward parts are exactly the reactions whose reduced coefficient is positive resp.
negative.  This is the sense in which the decomposition is "relative to the sign-compatible
`mu`/`sigma`".  (In the general, non-rank-one setting the two signs need not agree; the theorem
is stated in the rank-one setting, which is the classical deficiency-one setting.)

## The shelf balance criterion

A **shelf** is a set of reactions; it is *pairing-constant* at `mu` when all its sources pair
equally with `mu`.  The heart of the multi-shelf converse is the following elementary fact
(`shelfLowerBalanced_implies_shelfUpperBalanced`): *on a pairing-constant shelf, the upper
balance is a consequence of the lower balance*, because the exponential factor `exp <y_r, mu>`
is constant on the shelf.  This is the mechanism by which Feinberg's algorithm turns the shelf
balance conditions into the global balance conditions.

## The two-shelf decomposition

`shelf_recursion` is the **two-value argument**: if a balanced collection `A` of reactions
splits into two parts which are pairing-constant with *distinct* pairing values, then each part
balances at the lower state - and hence, by the shelf balance criterion, at the upper state as
well.  No extra hypothesis is needed: the *shelf balance* is a *consequence* of the two global
balances.

Applying this to the whole reaction set gives the **two-shelf decomposition theorem**
(`twoShelf_decomposition`): a feasible system whose reaction set splits into two
pairing-constant parts with distinct pairing values *is* a two-shelf system of shelf-wise
confluence vectors.  The shelf-wise confluence vectors themselves are `twoShelfConfluences`,
and the corresponding shelf decomposition is `twoShelfDecomposition`.  Consequently
(`twoShelf_adaFeasible`, `twoShelf_hasMultistationarityCapacity`) the network is **ADA
feasible** - the Advanced Deficiency Algorithm affirms its capacity - and in particular it has
the capacity for multiple positive steady states.

`shelfPartition_adaFeasible` is the corresponding statement for an *arbitrary number* of
shelves: any shelf partition whose shelves are pairing-constant and satisfy the shelf balance
is an ADA witness.

## A concrete instance

The namespace `TwoShelfExample` develops the network on the four species `{A, B, C, D}` with
the six reactions

    A -> B,  A -> C,  B + C -> 2 A        (the first module)
    B -> D,  B -> C,  D + C -> 2 B        (the second module)

Each module balances on its own, and the two modules sit at *different* `mu`-levels: the
sources of the first module pair at `1` (`<A, mu> = 1 = <B + C, mu>`), those of the second at
`2` (`<B, mu> = 2 = <D + C, mu>`).  With the log-ratio `mu = (1, 2, -1, 3)` and the unit flux,
the two shelves are the two modules, the flux is positive, and both balances hold; the
sign-compatible stoichiometric vector is `sigma = (1, 1, -3, 1) = 2 v_1 - 3 v_2 + v_4`.  The
example therefore *has the capacity* for multiple positive steady states
(`TwoShelfExample.hasCapacity`) and is ADA feasible (`TwoShelfExample.adaFeasible`), by the
two-shelf decomposition theorem.

## What is *not* proved here

* **The full multi-shelf converse.**  The hypotheses of `twoShelf_decomposition` - the
  existence of a partition into two pairing-constant parts with distinct pairing values - are
  *not* automatic: they are exactly the data that Feinberg's and Ellison's algorithms *search*
  for.  What is proved here is the *converse* direction of the search: whenever such a
  partition exists, the shelf balances follow automatically, and the flux decomposes into
  shelf-wise confluence vectors.
* **The iteration to three or more shelves.**  The two-value argument is *sharp*: a shelf
  produced by it is pairing-constant, hence cannot be split further by the same argument
  (`twoShelf_cannot_iterate`).  The general `k`-shelf statement is recorded as the two *moment
  relations* on the partial balances (`partialBalance_moments`, on the partition-sum lemma
  `sum_eq_sum_partition`): with `k` pairing values there are only two linear relations, so the
  individual shelf balances are *not* forced for `k >= 3` (`threeShelf_freedom` gives an explicit
  family of partial balances which are not forced to vanish).  This is a genuine obstruction,
  not a gap in the proof.
* **The endotacticity of the shelves.**  As in `CRNT.Multistationarity.AdvancedDeficiencyAlgorithm`,
  the structural (endotactic) hypothesis on the shelves is kept separate from the feasibility
  condition, and is not used here.
* **The numerical version** of either algorithm (the reduction of the flux feasibility problem
  to a linear program over sign patterns).

Depends on: `CRNT.Multistationarity.AdvancedDeficiencyAlgorithm`,
`CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Finset

section General

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-! ### The pairing data of a reaction -/

/-- The pairing of the **source** of a reaction with the log-ratio `μ`.  This is the quantity
which enters the exponential factor `e^{⟨y_r, μ⟩}` of the upper flux balance. -/
def sourcePairing (N : Network S) (μ : S → ℝ) (r : N.R) : ℝ :=
  complexPairing (N.reaction r).source μ

/-- The pairing of the **target** of a reaction with the log-ratio `μ`. -/
def targetPairing (N : Network S) (μ : S → ℝ) (r : N.R) : ℝ :=
  complexPairing (N.reaction r).target μ

/-- The **μ-step** of a reaction: the pairing of its reaction vector `y'_r − y_r` with the
log-ratio.  A reaction is *forward* when its step is positive (its target pairs strictly above
its source), *backward* when the step is negative, and *flat* when the step vanishes. -/
def pairingStep (N : Network S) (μ : S → ℝ) (r : N.R) : ℝ :=
  targetPairing N μ r - sourcePairing N μ r

/-- **The μ-step of a reaction is the pairing of its reaction vector with the log-ratio.** -/
theorem pairingStep_eq_reactionVector_pairing (N : Network S) (μ : S → ℝ) (r : N.R) :
    pairingStep N μ r = ∑ s, N.reactionVector r s * μ s := by
  classical
  have hsub : (∑ s, (((N.reaction r).target s : ℝ)) * μ s) -
      (∑ s, (((N.reaction r).source s : ℝ)) * μ s)
      = ∑ s, (((((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ))) * μ s) := by
    calc (∑ s, (((N.reaction r).target s : ℝ)) * μ s) -
          (∑ s, (((N.reaction r).source s : ℝ)) * μ s)
        = ∑ s, ((((N.reaction r).target s : ℝ)) * μ s - (((N.reaction r).source s : ℝ)) * μ s) :=
          (Finset.sum_sub_distrib (s := (Finset.univ : Finset S))
            (f := fun s : S => (((N.reaction r).target s : ℝ)) * μ s)
            (g := fun s : S => (((N.reaction r).source s : ℝ)) * μ s)).symm
      _ = ∑ s, (((((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ))) * μ s) := by
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
  calc pairingStep N μ r
      = (∑ s, (((N.reaction r).target s : ℝ)) * μ s) -
        (∑ s, (((N.reaction r).source s : ℝ)) * μ s) := rfl
    _ = ∑ s, (((((N.reaction r).target s : ℝ) - ((N.reaction r).source s : ℝ))) * μ s) := hsub
    _ = ∑ s, N.reactionVector r s * μ s := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [reactionVector_apply]

/-! ### The sign decomposition of the reaction set -/

/-- A reaction is **forward** at the log-ratio `μ` when its target pairs strictly above its
source: the reaction moves *up* in the `μ`-direction. -/
def IsForward (N : Network S) (μ : S → ℝ) (r : N.R) : Prop := 0 < pairingStep N μ r

/-- A reaction is **backward** at the log-ratio `μ` when its target pairs strictly below its
source: the reaction moves *down* in the `μ`-direction. -/
def IsBackward (N : Network S) (μ : S → ℝ) (r : N.R) : Prop := pairingStep N μ r < 0

/-- A reaction is **flat** at the log-ratio `μ` when its source and its target pair equally
with `μ`. -/
def IsFlat (N : Network S) (μ : S → ℝ) (r : N.R) : Prop := pairingStep N μ r = 0

/-- The **forward** reactions at the log-ratio `μ`. -/
noncomputable def forwardReactions (N : Network S) (μ : S → ℝ) : Finset N.R := by
  classical
  exact Finset.univ.filter fun r => IsForward N μ r

/-- The **backward** reactions at the log-ratio `μ`. -/
noncomputable def backwardReactions (N : Network S) (μ : S → ℝ) : Finset N.R := by
  classical
  exact Finset.univ.filter fun r => IsBackward N μ r

/-- The **flat** reactions at the log-ratio `μ`. -/
noncomputable def flatReactions (N : Network S) (μ : S → ℝ) : Finset N.R := by
  classical
  exact Finset.univ.filter fun r => IsFlat N μ r

/-- A reaction is forward exactly when it belongs to the forward part. -/
theorem mem_forwardReactions {N : Network S} {μ : S → ℝ} {r : N.R} :
    r ∈ forwardReactions N μ ↔ IsForward N μ r := by
  classical
  simp only [forwardReactions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A reaction is backward exactly when it belongs to the backward part. -/
theorem mem_backwardReactions {N : Network S} {μ : S → ℝ} {r : N.R} :
    r ∈ backwardReactions N μ ↔ IsBackward N μ r := by
  classical
  simp only [backwardReactions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A reaction is flat exactly when it belongs to the flat part. -/
theorem mem_flatReactions {N : Network S} {μ : S → ℝ} {r : N.R} :
    r ∈ flatReactions N μ ↔ IsFlat N μ r := by
  classical
  simp only [flatReactions, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Every reaction is forward, backward or flat**: the sign decomposition is a partition of
the reaction set. -/
theorem signDecomposition_cover (N : Network S) (μ : S → ℝ) :
    forwardReactions N μ ∪ backwardReactions N μ ∪ flatReactions N μ = Finset.univ := by
  classical
  ext r
  simp only [Finset.mem_union, Finset.mem_univ, iff_true, mem_forwardReactions,
    mem_backwardReactions, mem_flatReactions]
  rcases lt_trichotomy (pairingStep N μ r) 0 with h | h | h
  · exact Or.inl (Or.inr h)
  · exact Or.inr h
  · exact Or.inl (Or.inl h)

/-- The forward and backward parts are disjoint. -/
theorem signDecomposition_disjoint_forward_backward (N : Network S) (μ : S → ℝ) :
    forwardReactions N μ ∩ backwardReactions N μ = ∅ := by
  classical
  rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
  intro r hrF hrB
  rw [mem_forwardReactions] at hrF
  rw [mem_backwardReactions] at hrB
  exact (lt_irrefl 0 (lt_trans hrF hrB))

/-- The forward and flat parts are disjoint. -/
theorem signDecomposition_disjoint_forward_flat (N : Network S) (μ : S → ℝ) :
    forwardReactions N μ ∩ flatReactions N μ = ∅ := by
  classical
  rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
  intro r hrF hrZ
  rw [mem_forwardReactions] at hrF
  rw [mem_flatReactions] at hrZ
  have hrF' : 0 < pairingStep N μ r := hrF
  have hrZ' : pairingStep N μ r = 0 := hrZ
  exact (lt_irrefl 0 (hrZ' ▸ hrF'))

/-- The backward and flat parts are disjoint. -/
theorem signDecomposition_disjoint_backward_flat (N : Network S) (μ : S → ℝ) :
    backwardReactions N μ ∩ flatReactions N μ = ∅ := by
  classical
  rw [← Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_left]
  intro r hrB hrZ
  rw [mem_backwardReactions] at hrB
  rw [mem_flatReactions] at hrZ
  have hrB' : pairingStep N μ r < 0 := hrB
  have hrZ' : pairingStep N μ r = 0 := hrZ
  exact (lt_irrefl 0 (hrZ' ▸ hrB'))

/-! ### The μ-weighted balance and the non-triviality of the decomposition -/

/-- **The μ-weighted balance.**  The lower balance of the flux implies that the flux-weighted
μ-steps sum to zero: `∑_r α_r ⟨y'_r − y_r, μ⟩ = 0`.  This is the scalar shadow of the lower
balance, and it is what forces the sign decomposition to be non-trivial. -/
theorem lowerBalance_step_sum (N : Network S) (μ : S → ℝ) (α : N.R → ℝ)
    (h : ∀ s, ∑ r, α r * N.reactionVector r s = 0) :
    ∑ r, α r * pairingStep N μ r = 0 := by
  classical
  calc ∑ r, α r * pairingStep N μ r
      = ∑ r, ∑ s, (α r * N.reactionVector r s) * μ s := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [pairingStep_eq_reactionVector_pairing, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = ∑ s, ∑ r, (α r * N.reactionVector r s) * μ s := Finset.sum_comm
    _ = ∑ s, μ s * (∑ r, α r * N.reactionVector r s) := by
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    _ = 0 := by
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [h s]
      simp

/-- **A balanced, strictly positive flux has a backward reaction as soon as it has a forward
one.**  This is the non-triviality of the sign decomposition. -/
theorem signDecomposition_forward_imp_backward (N : Network S) (μ : S → ℝ) (α : N.R → ℝ)
    (hα : ∀ r, 0 < α r) (h : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hf : ∃ r, IsForward N μ r) : ∃ r, IsBackward N μ r := by
  classical
  by_contra hn
  simp only [not_exists] at hn
  obtain ⟨r₀, hr₀⟩ := hf
  have hstep : ∑ r, α r * pairingStep N μ r = 0 := lowerBalance_step_sum N μ α h
  have hnonneg : ∀ r, 0 ≤ α r * pairingStep N μ r := by
    intro r
    have hle : 0 ≤ pairingStep N μ r := le_of_not_gt (hn r)
    exact mul_nonneg (le_of_lt (hα r)) hle
  have hpos : 0 < α r₀ * pairingStep N μ r₀ := mul_pos (hα r₀) hr₀
  have hsum : 0 < ∑ r, α r * pairingStep N μ r :=
    Finset.sum_pos' (fun r _ => hnonneg r) ⟨r₀, Finset.mem_univ r₀, hpos⟩
  linarith

/-- **A balanced, strictly positive flux whose reactions are all non-forward has all its
reactions flat.**  So the sign decomposition of a balanced flux is either trivial (everything
flat) or genuinely two-sided. -/
theorem signDecomposition_allFlat_of_no_forward (N : Network S) (μ : S → ℝ) (α : N.R → ℝ)
    (hα : ∀ r, 0 < α r) (h : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hnf : ∀ r, ¬ IsForward N μ r) : ∀ r, IsFlat N μ r := by
  classical
  have hstep : ∑ r, α r * pairingStep N μ r = 0 := lowerBalance_step_sum N μ α h
  have hneg : ∀ r, 0 ≤ -(α r * pairingStep N μ r) := by
    intro r
    have hle : pairingStep N μ r ≤ 0 := le_of_not_gt (hnf r)
    have h2 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hα r)) hle
    linarith
  have hsum : ∑ r, -(α r * pairingStep N μ r) = 0 := by
    rw [Finset.sum_neg_distrib]
    linarith
  have hz : ∀ r, -(α r * pairingStep N μ r) = 0 :=
    fun r => (Finset.sum_eq_zero_iff_of_nonneg (fun r _ => hneg r)).mp hsum r (Finset.mem_univ r)
  intro r
  have h1 : α r * pairingStep N μ r = 0 := neg_eq_zero.mp (hz r)
  have h2 : pairingStep N μ r = 0 := by
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h (ne_of_gt (hα r))
    · exact h
  exact h2

/-! ### The shelf balance criterion -/

/-- **The lower balance of a shelf**: the flux `lam`, supported on the shelf `A`, balances the
shelf at the lower state, `∑_{r ∈ A} λ_r (y'_r − y_r) = 0`. -/
def ShelfLowerBalanced (N : Network S) (A : Finset N.R) (lam : N.R → ℝ) : Prop :=
  ∀ s, ∑ r ∈ A, lam r * N.reactionVector r s = 0

/-- **The upper balance of a shelf**: the flux `lam`, supported on the shelf `A`, balances the
shelf at the upper state `e^{μ}`, `∑_{r ∈ A} λ_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`. -/
def ShelfUpperBalanced (N : Network S) (A : Finset N.R) (lam : N.R → ℝ) (μ : S → ℝ) : Prop :=
  ∀ s, ∑ r ∈ A, lam r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0

/-- **The shelf balance criterion.**  On a *pairing-constant* shelf — a shelf whose reactions
all have sources pairing equally with `μ` — the upper balance is a consequence of the lower
balance: the exponential factor `e^{⟨y_r, μ⟩}` is constant on the shelf.

This is the mechanism by which Feinberg's algorithm turns the *shelf* balance conditions into
the *global* balance conditions. -/
theorem shelfLowerBalanced_implies_shelfUpperBalanced (N : Network S) (A : Finset N.R)
    (lam : N.R → ℝ) (μ : S → ℝ)
    (hconst : ∀ r ∈ A, ∀ r' ∈ A, sourcePairing N μ r = sourcePairing N μ r')
    (h : ShelfLowerBalanced N A lam) : ShelfUpperBalanced N A lam μ := by
  classical
  by_cases hne : A.Nonempty
  · obtain ⟨r₀, hr₀⟩ := hne
    have hexp : ∀ r ∈ A, Real.exp (sourcePairing N μ r) =
        Real.exp (sourcePairing N μ r₀) := by
      intro r hr
      rw [hconst r hr r₀ hr₀]
    intro s
    calc ∑ r ∈ A, lam r * Real.exp (sourcePairing N μ r) * N.reactionVector r s
        = ∑ r ∈ A, (Real.exp (sourcePairing N μ r₀) * (lam r * N.reactionVector r s)) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [hexp r hr]
          ring
      _ = Real.exp (sourcePairing N μ r₀) * ∑ r ∈ A, lam r * N.reactionVector r s := by
          rw [Finset.mul_sum]
      _ = 0 := by rw [h s]; simp
  · have hA : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    subst hA
    simp [ShelfUpperBalanced]

/-! ### The two-value argument: the shelf recursion -/

/-- Two finite sets with empty intersection are disjoint. -/
theorem disjoint_of_inter_eq_empty {ι : Type} [DecidableEq ι] {F B : Finset ι} (h : F ∩ B = ∅) :
    Disjoint F B := by
  rw [Finset.disjoint_left]
  intro a ha hb
  have hmem : a ∈ F ∩ B := Finset.mem_inter.mpr ⟨ha, hb⟩
  rw [h] at hmem
  exact absurd hmem (by simp)

/-- **The shelf recursion (the two-value argument).**  Let `A` be a collection of reactions
whose restriction of the flux `α` balances at the lower *and* at the upper state.  If `A`
splits into two parts `F` and `B` which are *pairing-constant* — all the sources of the
reactions of a part pair equally with `μ` — and whose two pairing values are *distinct*, then
**each part balances at the lower state**.

The proof is the classical one: subtracting the lower balance from the upper balance, weighted
by the constant exponential of the *other* part, kills the common part and leaves
`(e^{c_F} − e^{c_B}) L_F = 0`, whence `L_F = 0` because the two pairing values differ.  Notice
that *no shelf-balance hypothesis is needed*: the shelf balances are a **consequence** of the
two global balances. -/
theorem shelf_recursion (N : Network S) (μ : S → ℝ) (α : N.R → ℝ) (A F B : Finset N.R)
    (hA : F ∪ B = A) (hdisj : F ∩ B = ∅)
    (hconstF : ∀ r ∈ F, ∀ r' ∈ F, sourcePairing N μ r = sourcePairing N μ r')
    (hconstB : ∀ r ∈ B, ∀ r' ∈ B, sourcePairing N μ r = sourcePairing N μ r')
    (hdiff : ∃ r ∈ F, ∃ r' ∈ B, sourcePairing N μ r ≠ sourcePairing N μ r')
    (hlow : ∀ s, ∑ r ∈ A, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r ∈ A, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0) :
    (∀ s, ∑ r ∈ F, α r * N.reactionVector r s = 0) ∧
      (∀ s, ∑ r ∈ B, α r * N.reactionVector r s = 0) := by
  classical
  obtain ⟨rF, hrF, rB, hrB, hne⟩ := hdiff
  have hexpF : ∀ r ∈ F, Real.exp (sourcePairing N μ r) = Real.exp (sourcePairing N μ rF) := by
    intro r hr
    rw [hconstF r hr rF hrF]
  have hexpB : ∀ r ∈ B, Real.exp (sourcePairing N μ r) = Real.exp (sourcePairing N μ rB) := by
    intro r hr
    rw [hconstB r hr rB hrB]
  have hexpne : Real.exp (sourcePairing N μ rF) ≠ Real.exp (sourcePairing N μ rB) := by
    intro h
    exact hne (Real.exp_injective h)
  have hexpne' : Real.exp (sourcePairing N μ rF) - Real.exp (sourcePairing N μ rB) ≠ 0 :=
    sub_ne_zero.mpr hexpne
  -- the sums split over the two parts
  have hsplit (f : N.R → ℝ) :
      (∑ r ∈ A, f r) = (∑ r ∈ F, f r) + ∑ r ∈ B, f r := by
    calc ∑ r ∈ A, f r = ∑ r ∈ F ∪ B, f r := by rw [← hA]
      _ = (∑ r ∈ F, f r) + ∑ r ∈ B, f r :=
        Finset.sum_union (disjoint_of_inter_eq_empty hdisj)
  -- the upper balance splits with the *constant* exponential of each part
  have huppF (s : S) :
      (∑ r ∈ F, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s)
        = Real.exp (sourcePairing N μ rF) * (∑ r ∈ F, α r * N.reactionVector r s) := by
    calc ∑ r ∈ F, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s
        = ∑ r ∈ F, (Real.exp (sourcePairing N μ rF) *
            (α r * N.reactionVector r s)) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [hexpF r hr]
          ring
      _ = Real.exp (sourcePairing N μ rF) * (∑ r ∈ F, α r * N.reactionVector r s) := by
          rw [Finset.mul_sum]
  have huppB (s : S) :
      (∑ r ∈ B, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s)
        = Real.exp (sourcePairing N μ rB) * (∑ r ∈ B, α r * N.reactionVector r s) := by
    calc ∑ r ∈ B, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s
        = ∑ r ∈ B, (Real.exp (sourcePairing N μ rB) *
            (α r * N.reactionVector r s)) := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [hexpB r hr]
          ring
      _ = Real.exp (sourcePairing N μ rB) * (∑ r ∈ B, α r * N.reactionVector r s) := by
          rw [Finset.mul_sum]
  -- the key step: the two balances force the two partial balances to vanish
  have hkey (s : S) : ∑ r ∈ F, α r * N.reactionVector r s = 0 := by
    have h1 := hlow s
    have h2 := hupp s
    rw [hsplit] at h1
    rw [hsplit, huppF s, huppB s] at h2
    have h3 : ∑ r ∈ B, α r * N.reactionVector r s = -(∑ r ∈ F, α r * N.reactionVector r s) := by
      linarith
    have h4 : (Real.exp (sourcePairing N μ rF) - Real.exp (sourcePairing N μ rB)) *
        (∑ r ∈ F, α r * N.reactionVector r s) = 0 := by
      rw [h3] at h2
      calc (Real.exp (sourcePairing N μ rF) - Real.exp (sourcePairing N μ rB)) *
          (∑ r ∈ F, α r * N.reactionVector r s)
          = Real.exp (sourcePairing N μ rF) * (∑ r ∈ F, α r * N.reactionVector r s) -
            Real.exp (sourcePairing N μ rB) * (∑ r ∈ F, α r * N.reactionVector r s) := by ring
        _ = 0 := by linarith
    exact (mul_eq_zero.mp h4).resolve_left hexpne'
  refine ⟨hkey, fun s => ?_⟩
  have h1 := hlow s
  rw [hsplit] at h1
  have h2 : ∑ r ∈ B, α r * N.reactionVector r s = 0 := by
    rw [hkey s] at h1
    linarith
  exact h2

/-! ### The two-shelf decomposition -/

/-- A **two-shelf split** of the reaction set at the log-ratio `μ`: a partition of the reaction
set into two parts, each of which is *pairing-constant* — the sources of the reactions of the
part pair equally with `μ` — and whose two pairing values are *distinct*. -/
def TwoShelfSplit (N : Network S) (μ : S → ℝ) (F B : Finset N.R) : Prop :=
  F ∪ B = Finset.univ ∧
  F ∩ B = ∅ ∧
  (∀ r ∈ F, ∀ r' ∈ F, sourcePairing N μ r = sourcePairing N μ r') ∧
  (∀ r ∈ B, ∀ r' ∈ B, sourcePairing N μ r = sourcePairing N μ r') ∧
  (∃ r ∈ F, ∃ r' ∈ B, sourcePairing N μ r ≠ sourcePairing N μ r')

/-- **The two-shelf decomposition of a balanced flux.**  Let `α` be a flux satisfying the lower
and the upper balance at the log-ratio `μ`, and suppose the reaction set splits into two
*pairing-constant* parts `F` and `B` whose pairing values are distinct.  Then the restriction
of `α` to each part balances *on its own*, at the lower state and at the upper state: the flux
decomposes into two shelf-wise confluence vectors.

The shelf balances are **consequences** of the two global balances; they are not hypotheses.
This is the first step of the multi-shelf converse. -/
theorem twoShelf_decomposition (N : Network S) (μ : S → ℝ) (α : N.R → ℝ) (F B : Finset N.R)
    (hsplit : TwoShelfSplit N μ F B)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0) :
    (∀ s, ∑ r ∈ F, α r * N.reactionVector r s = 0) ∧
      (∀ s, ∑ r ∈ B, α r * N.reactionVector r s = 0) ∧
      (∀ s, ∑ r ∈ F, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0) ∧
      (∀ s, ∑ r ∈ B, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0) := by
  classical
  obtain ⟨hcover, hdisj, hconstF, hconstB, hdiff⟩ := hsplit
  have hrec := shelf_recursion N μ α (Finset.univ : Finset N.R) F B
    hcover hdisj hconstF hconstB hdiff hlow hupp
  have huppF : ∀ s, ∑ r ∈ F, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0 := by
    intro s
    exact shelfLowerBalanced_implies_shelfUpperBalanced N F α μ hconstF hrec.1 s
  have huppB : ∀ s, ∑ r ∈ B, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0 := by
    intro s
    exact shelfLowerBalanced_implies_shelfUpperBalanced N B α μ hconstB hrec.2 s
  exact ⟨hrec.1, hrec.2, huppF, huppB⟩

/-- **The shelf decomposition of a two-shelf split.** -/
def twoShelfDecomposition {N : Network S} (F B : Finset N.R)
    (hcover : F ∪ B = Finset.univ) (hdisj : F ∩ B = ∅) : N.ADAShelfDecomposition where
  shelves := {F, B}
  cover := by
    intro r
    have hmem : r ∈ F ∪ B := by rw [hcover]; exact Finset.mem_univ r
    rcases Finset.mem_union.mp hmem with hmem | hmem
    · exact ⟨F, by simp, hmem⟩
    · exact ⟨B, by simp, hmem⟩
  disjoint := by
    intro sh hsh sh' hsh' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsh hsh'
    rcases hsh with h | h
    · subst sh
      rcases hsh' with h' | h'
      · subst sh'
        exact absurd rfl hne
      · subst sh'
        exact hdisj
    · subst sh
      rcases hsh' with h' | h'
      · subst sh'
        rw [Finset.inter_comm]
        exact hdisj
      · subst sh'
        exact absurd rfl hne

/-- **The shelf-wise confluence vectors of a two-shelf split**: the restriction of the flux to
each shelf. -/
def twoShelfConfluences {N : Network S} {F B : Finset N.R} (hcover : F ∪ B = Finset.univ)
    (hdisj : F ∩ B = ∅) (μ : S → ℝ) (α : N.R → ℝ) (hα : ∀ r, 0 < α r)
    (hlowF : ∀ s, ∑ r ∈ F, α r * N.reactionVector r s = 0)
    (hlowB : ∀ s, ∑ r ∈ B, α r * N.reactionVector r s = 0)
    (huppF : ∀ s, ∑ r ∈ F, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0)
    (huppB : ∀ s, ∑ r ∈ B, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0) :
    N.ADAConfluences (twoShelfDecomposition F B hcover hdisj) where
  μ := μ
  flux := fun sh r => if r ∈ sh then α r else 0
  support := by
    intro sh hsh r hr
    simp [hr]
  positive := by
    intro sh hsh r hr
    simp [hr]
    exact hα r
  lower_balance := by
    intro sh hsh s
    simp only [twoShelfDecomposition, Finset.mem_insert, Finset.mem_singleton] at hsh
    rcases hsh with h | h
    · subst sh
      calc ∑ r ∈ F, (if r ∈ F then α r else 0) * N.reactionVector r s
          = ∑ r ∈ F, α r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hlowF s
    · subst sh
      calc ∑ r ∈ B, (if r ∈ B then α r else 0) * N.reactionVector r s
          = ∑ r ∈ B, α r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := hlowB s
  upper_balance := by
    intro sh hsh s
    simp only [twoShelfDecomposition, Finset.mem_insert, Finset.mem_singleton] at hsh
    rcases hsh with h | h
    · subst sh
      calc ∑ r ∈ F, (if r ∈ F then α r else 0) * Real.exp (sourcePairing N μ r) *
          N.reactionVector r s
          = ∑ r ∈ F, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := huppF s
    · subst sh
      calc ∑ r ∈ B, (if r ∈ B then α r else 0) * Real.exp (sourcePairing N μ r) *
          N.reactionVector r s
          = ∑ r ∈ B, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r hr => ?_
            simp [hr]
        _ = 0 := huppB s

/-- **The multi-shelf converse, in the two-shelf form.**  A feasible system whose reaction set
splits into two pairing-constant parts with distinct pairing values is an *Advanced Deficiency
Algorithm* system: the two shelves carry the shelf-wise confluence vectors, and the network is
ADA feasible. -/
theorem twoShelf_adaFeasible (N : Network S) (μ : S → ℝ) (α : N.R → ℝ) (F B : Finset N.R)
    (hsplit : TwoShelfSplit N μ F B)
    (hα : ∀ r, 0 < α r)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0)
    (hμ0 : μ ≠ 0) (hsc : N.SignCompatibleWithStoich μ) :
    N.ADAFeasible := by
  classical
  obtain ⟨hlowF, hlowB, huppF, huppB⟩ := twoShelf_decomposition N μ α F B hsplit hlow hupp
  obtain ⟨hcover, hdisj, hconstF, hconstB, hdiff⟩ := hsplit
  refine ⟨twoShelfDecomposition F B hcover hdisj,
    twoShelfConfluences hcover hdisj μ α hα hlowF hlowB huppF huppB,
    hμ0, hsc⟩

/-- **The multi-shelf converse, in the two-shelf form: the capacity.**  A feasible system whose
reaction set splits into two pairing-constant parts with distinct pairing values yields the
capacity for multiple positive steady states. -/
theorem twoShelf_hasMultistationarityCapacity (N : Network S) (μ : S → ℝ) (α : N.R → ℝ)
    (F B : Finset N.R)
    (hsplit : TwoShelfSplit N μ F B)
    (hα : ∀ r, 0 < α r)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0)
    (hμ0 : μ ≠ 0) (hsc : N.SignCompatibleWithStoich μ) :
    N.HasMultistationarityCapacity :=
  N.adaFeasible_implies_capacity
    (twoShelf_adaFeasible N μ α F B hsplit hα hlow hupp hμ0 hsc)

/-! ### The general multi-shelf statement -/

/-- **The general multi-shelf theorem.**  An arbitrary number of shelves: if the reaction set
is partitioned into shelves which are pairing-constant at `μ` and which satisfy the *shelf
balance* (the lower balance on the shelf), then the flux decomposes into shelf-wise confluence
vectors — the shelves are an Advanced Deficiency Algorithm system, and the network has the
capacity for multiple positive steady states. -/
theorem shelfPartition_adaFeasible (N : Network S) (μ : S → ℝ) (α : N.R → ℝ)
    (shelves : Finset (Finset N.R))
    (hcover : ∀ r : N.R, ∃ sh ∈ shelves, r ∈ sh)
    (hdisj : ∀ sh ∈ shelves, ∀ sh' ∈ shelves, sh ≠ sh' → sh ∩ sh' = ∅)
    (hconst : ∀ sh ∈ shelves, ∀ r ∈ sh, ∀ r' ∈ sh, sourcePairing N μ r = sourcePairing N μ r')
    (hbal : ∀ sh ∈ shelves, ∀ s, ∑ r ∈ sh, α r * N.reactionVector r s = 0)
    (hα : ∀ r, 0 < α r)
    (hμ0 : μ ≠ 0) (hsc : N.SignCompatibleWithStoich μ) :
    N.ADAFeasible := by
  classical
  have hupp : ∀ sh ∈ shelves, ∀ s,
      ∑ r ∈ sh, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0 := by
    intro sh hsh s
    exact shelfLowerBalanced_implies_shelfUpperBalanced N sh α μ (hconst sh hsh) (hbal sh hsh) s
  refine ⟨{ shelves := shelves, cover := hcover, disjoint := hdisj },
    { μ := μ, flux := fun sh r => if r ∈ sh then α r else 0,
      support := by
        intro sh hsh r hr
        simp [hr]
      positive := by
        intro sh hsh r hr
        simp [hr]
        exact hα r
      lower_balance := by
        intro sh hsh s
        calc ∑ r ∈ sh, (if r ∈ sh then α r else 0) * N.reactionVector r s
            = ∑ r ∈ sh, α r * N.reactionVector r s := by
              refine Finset.sum_congr rfl fun r hr => ?_
              simp [hr]
          _ = 0 := hbal sh hsh s
      upper_balance := by
        intro sh hsh s
        calc ∑ r ∈ sh, (if r ∈ sh then α r else 0) * Real.exp (sourcePairing N μ r) *
              N.reactionVector r s
            = ∑ r ∈ sh, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
              refine Finset.sum_congr rfl fun r hr => ?_
              simp [hr]
          _ = 0 := hupp sh hsh s }, hμ0, hsc⟩

/-! ### The rank-one setting: the sign decomposition relative to the sign-compatible `σ` -/

/-- **Negating both vectors preserves the sign pattern.** -/
theorem sameSign_neg_neg {ι : Type} {u v : ι → ℝ} (h : SameSign u v) : SameSign (-u) (-v) := by
  apply sameSign_of_sign_eq
  intro i
  calc SignType.sign ((-u) i) = -SignType.sign (u i) := Left.sign_neg (u i)
    _ = -SignType.sign (v i) := by rw [sameSign_sign_eq h i]
    _ = SignType.sign ((-v) i) := (Left.sign_neg (v i)).symm

omit [DecidableEq S] in
/-- **The class pairing of the sign-compatible stoichiometric vector.**  If `σ = t • v` then
`⟨v, σ⟩ = t ⟨v, v⟩`. -/
theorem classPairing_smul (v σ : S → ℝ) (t : ℝ) (h : σ = t • v) :
    classPairing v σ = t * ∑ s, v s * v s := by
  rw [h, classPairing]
  simp only [Pi.smul_apply, smul_eq_mul]
  calc ∑ s, v s * (t * v s) = ∑ s, t * (v s * v s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = t * ∑ s, v s * v s := by rw [Finset.mul_sum]

omit [DecidableEq S] in
/-- **The sum of squares of a nonzero vector is positive.** -/
theorem sum_sq_pos_of_ne_zero (v : S → ℝ) (hv0 : v ≠ 0) : 0 < ∑ s, v s * v s := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv0
  have hi0 : v i ≠ 0 := by simpa only [Pi.zero_apply] using hi
  have hsq : 0 < v i * v i := by
    have := sq_pos_of_ne_zero hi0
    simpa [pow_two] using this
  refine Finset.sum_pos' (fun s _ => mul_self_nonneg (v s)) ⟨i, Finset.mem_univ i, hsq⟩

omit [DecidableEq S] in
/-- **The class pairings of a log-ratio and of its sign-compatible stoichiometric vector have
the same sign.**  Let `σ = t • v` be a nonzero stoichiometric vector and `μ` a log-ratio with
the sign pattern of `σ`.  Then `⟨v, μ⟩` and `⟨v, σ⟩` have the same (nonzero) sign.

This is the sense in which the sign decomposition of the reaction set is *relative to the
sign-compatible `μ`/`σ`*: the forward and backward parts are the same whether they are read
off `μ` or off `σ`. -/
theorem classPairing_sign_agrees (v μ σ : S → ℝ) (hv0 : v ≠ 0) (hμ0 : μ ≠ 0)
    (t : ℝ) (ht : t ≠ 0) (hσ : σ = t • v) (hsame : SameSign μ σ) :
    SignType.sign (classPairing v μ) = SignType.sign (classPairing v σ) := by
  classical
  rcases lt_trichotomy t 0 with htneg | htzero | htpos
  · -- `t < 0`: `σ` has the sign pattern of `−v`, and so does `μ`
    have hsame' : SameSign μ (-v) := by
      have h1 : SameSign (t • v) μ := by
        rw [← hσ]
        exact sameSign_symm hsame
      have h2 : SameSign (-v) μ := sameSign_smul_neg htneg h1
      exact sameSign_symm h2
    have hnegμ : (-μ) ≠ 0 := by
      intro h
      apply hμ0
      funext i
      have h1 := congrFun h i
      simp only [Pi.neg_apply] at h1
      exact neg_eq_zero.mp h1
    have hpos : 0 < classPairing v (-μ) := by
      have h1 : SameSign (-μ) v := by
        simpa only [neg_neg] using (sameSign_neg_neg hsame')
      exact classPairing_pos_of_sameSign hv0 h1
    have hneg : classPairing v (-μ) = -classPairing v μ := by
      rw [classPairing]
      calc ∑ s, v s * (-μ s) = ∑ s, -(v s * μ s) := by
            refine Finset.sum_congr rfl fun s _ => ?_
            ring
        _ = -(∑ s, v s * μ s) := Finset.sum_neg_distrib (fun s => v s * μ s)
    have h1 : classPairing v μ < 0 := by linarith
    have h2 : classPairing v σ < 0 := by
      rw [classPairing_smul v σ t hσ]
      have hsq := sum_sq_pos_of_ne_zero v hv0
      exact mul_neg_of_neg_of_pos htneg hsq
    rw [sign_neg h1, sign_neg h2]
  · exact absurd htzero ht
  · -- `t > 0`: `σ` has the sign pattern of `v`, and so does `μ`
    have hsame' : SameSign μ v := by
      have h1 : SameSign (t • v) μ := by
        rw [← hσ]
        exact sameSign_symm hsame
      have h2 : SameSign v μ := sameSign_smul_pos htpos h1
      exact sameSign_symm h2
    have hpos : 0 < classPairing v μ := classPairing_pos_of_sameSign hv0 hsame'
    have h2 : 0 < classPairing v σ := by
      rw [classPairing_smul v σ t hσ]
      have hsq := sum_sq_pos_of_ne_zero v hv0
      exact mul_pos htpos hsq
    rw [sign_pos hpos, sign_pos h2]

/-- **The μ-step of a reaction is its reduced coefficient times the class pairing.** -/
theorem pairingStep_eq_reducedCoefficient_mul_classPairing (N : Network S) (v : S → ℝ)
    (hv : v ≠ 0) (hspan : N.stoichSubspace = Submodule.span ℝ {v}) (r : N.R) (μ : S → ℝ) :
    pairingStep N μ r = reducedCoefficient N v hv hspan r * classPairing v μ := by
  rw [pairingStep_eq_reactionVector_pairing]
  calc ∑ s, N.reactionVector r s * μ s
      = ∑ s, (reducedCoefficient N v hv hspan r * v s) * μ s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [reducedCoefficient_apply N v hv hspan r s]
      _ = reducedCoefficient N v hv hspan r * ∑ s, v s * μ s := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun s _ => ?_
          ring
      _ = reducedCoefficient N v hv hspan r * classPairing v μ := rfl

/-- **In the rank-one setting, the sign decomposition computed with the log-ratio agrees with
the one computed with the sign-compatible stoichiometric vector.**  So the forward part is the
set of reactions whose reduced coefficient is positive (up to the global orientation of the
class), and the backward part is the set of those whose reduced coefficient is negative.

This is the *sign-compatible* reading of the sign decomposition. -/
theorem rankOne_signDecomposition_agrees (N : Network S) (v : S → ℝ) (hv : v ≠ 0)
    (hspan : N.stoichSubspace = Submodule.span ℝ {v})
    (μ σ : S → ℝ) (hμ0 : μ ≠ 0) (hσS : σ ∈ N.stoichSubspace) (hσ0 : σ ≠ 0)
    (hsame : SameSign μ σ) :
    ∀ r : N.R, SignType.sign (pairingStep N μ r) = SignType.sign (pairingStep N σ r) := by
  classical
  have hσmem : σ ∈ Submodule.span ℝ ({v} : Set (S → ℝ)) := by rw [← hspan]; exact hσS
  obtain ⟨t, ht⟩ := (Submodule.mem_span_singleton).mp hσmem
  have hσeq : σ = t • v := ht.symm
  have ht0 : t ≠ 0 := by
    intro ht0
    apply hσ0
    rw [hσeq, ht0, zero_smul]
  have hsign : SignType.sign (classPairing v μ) = SignType.sign (classPairing v σ) :=
    classPairing_sign_agrees v μ σ hv hμ0 t ht0 hσeq hsame
  intro r
  have h1 : pairingStep N μ r = reducedCoefficient N v hv hspan r * classPairing v μ :=
    pairingStep_eq_reducedCoefficient_mul_classPairing N v hv hspan r μ
  have h2 : pairingStep N σ r = reducedCoefficient N v hv hspan r * classPairing v σ :=
    pairingStep_eq_reducedCoefficient_mul_classPairing N v hv hspan r σ
  rw [h1, h2]
  simp only [sign_mul, hsign]

/-! ### The moment relations of a multi-shelf decomposition -/

/-- **The sum over a partition.**  If the shelves `shelves i` partition the reaction set, then
the sum of a function over the reaction set is the sum of its sums over the shelves. -/
theorem sum_eq_sum_partition {ι : Type} [DecidableEq ι] [Fintype ι] {N : Network S}
    (f : N.R → ℝ) (shelves : ι → Finset N.R)
    (hcover : ∀ r : N.R, ∃ i, r ∈ shelves i)
    (hdisj : ∀ i j : ι, i ≠ j → shelves i ∩ shelves j = ∅) :
    ∑ r, f r = ∑ i, ∑ r ∈ shelves i, f r := by
  classical
  have hone : ∀ r : N.R, ∑ i, (if r ∈ shelves i then f r else 0) = f r := by
    intro r
    obtain ⟨i₀, hi₀⟩ := hcover r
    have hne : ∀ i, i ≠ i₀ → r ∉ shelves i := by
      intro i hi hmem
      exact (Finset.disjoint_left.mp
        (disjoint_of_inter_eq_empty (hdisj i₀ i (Ne.symm hi))) hi₀) hmem
    rw [Finset.sum_eq_single_of_mem i₀ (Finset.mem_univ i₀)
      (fun j _ hj => by simp [hne j hj])]
    simp [hi₀]
  calc ∑ r, f r = ∑ r, ∑ i, (if r ∈ shelves i then f r else 0) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        exact (hone r).symm
    _ = ∑ i, ∑ r, (if r ∈ shelves i then f r else 0) := Finset.sum_comm
    _ = ∑ i, ∑ r ∈ shelves i, f r := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact Finset.sum_ite_mem_eq (shelves i) f

/-- **The moment relations of a multi-shelf decomposition.**  Let the reaction set be
partitioned into shelves which are pairing-constant at the values `c i`, and let the flux
balance the whole reaction set at the lower and at the upper state.  The *partial balances*
`L i = ∑_{r ∈ shelves i} α_r (y'_r − y_r)` then satisfy the two **moment relations**

    ∑_i L i = 0        and        ∑_i e^{c i} L i = 0.

For two shelves these two relations force both partial balances to vanish — this is the
two-value argument of `shelf_recursion`.  For three or more shelves they do *not*: see
`threeShelf_freedom`.  This is the precise reason why the two-value argument does not
iterate. -/
theorem partialBalance_moments {ι : Type} [DecidableEq ι] [Fintype ι] {N : Network S}
    (μ : S → ℝ) (α : N.R → ℝ) (shelves : ι → Finset N.R) (c : ι → ℝ)
    (hcover : ∀ r : N.R, ∃ i, r ∈ shelves i)
    (hdisj : ∀ i j : ι, i ≠ j → shelves i ∩ shelves j = ∅)
    (hconst : ∀ i, ∀ r ∈ shelves i, sourcePairing N μ r = c i)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0) :
    (∀ s, ∑ i, ∑ r ∈ shelves i, α r * N.reactionVector r s = 0) ∧
      (∀ s, ∑ i, Real.exp (c i) * (∑ r ∈ shelves i, α r * N.reactionVector r s) = 0) := by
  classical
  constructor
  · intro s
    calc ∑ i, ∑ r ∈ shelves i, α r * N.reactionVector r s
        = ∑ r, α r * N.reactionVector r s :=
          (sum_eq_sum_partition (f := fun r => α r * N.reactionVector r s) shelves hcover hdisj).symm
      _ = 0 := hlow s
  · intro s
    calc ∑ i, Real.exp (c i) * (∑ r ∈ shelves i, α r * N.reactionVector r s)
        = ∑ i, ∑ r ∈ shelves i, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
          refine Finset.sum_congr rfl fun i _ => ?_
          calc Real.exp (c i) * (∑ r ∈ shelves i, α r * N.reactionVector r s)
              = ∑ r ∈ shelves i, (Real.exp (c i) * (α r * N.reactionVector r s)) := by
                rw [Finset.mul_sum]
            _ = ∑ r ∈ shelves i, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
                refine Finset.sum_congr rfl fun r hr => ?_
                rw [hconst i r hr]
                ring
      _ = ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s :=
        (sum_eq_sum_partition
          (f := fun r => α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s)
          shelves hcover hdisj).symm
      _ = 0 := hupp s

omit [DecidableEq S] [Fintype S] in
/-- **The three-shelf freedom.**  With three pairing values, the two moment relations do *not*
force the partial balances to vanish: for any vector `w` the three partial balances

    L₁ = (e^{c₃} − e^{c₂}) w,   L₂ = (e^{c₁} − e^{c₃}) w,   L₃ = (e^{c₂} − e^{c₁}) w

satisfy both moment relations, and they vanish only when `w = 0`.  So the automatic
decomposition into shelf-wise confluence vectors is a genuinely *two*-shelf phenomenon. -/
theorem threeShelf_freedom (c1 c2 c3 : ℝ) (w : S → ℝ) :
    (∀ s, w s * (Real.exp c3 - Real.exp c2) + w s * (Real.exp c1 - Real.exp c3) +
        w s * (Real.exp c2 - Real.exp c1) = 0) ∧
      (∀ s, w s * (Real.exp c1 * (Real.exp c3 - Real.exp c2)) +
          w s * (Real.exp c2 * (Real.exp c1 - Real.exp c3)) +
          w s * (Real.exp c3 * (Real.exp c2 - Real.exp c1)) = 0) := by
  constructor <;> intro s <;> ring

/-- **The two-value argument does not iterate.**  A shelf which is *pairing-constant* cannot be
split into two parts with *distinct* pairing values: all the reactions of the shelf have
sources pairing equally with `μ`, so any two of its parts share the same pairing value.
Hence the two-value argument of `shelf_recursion` applies to the *whole* reaction set, but not
to the shelves it produces: the iteration to three or more shelves needs a different
mechanism. -/
theorem twoShelf_cannot_iterate (N : Network S) (μ : S → ℝ) (A : Finset N.R)
    (hconst : ∀ r ∈ A, ∀ r' ∈ A, sourcePairing N μ r = sourcePairing N μ r')
    (F B : Finset N.R) (hA : F ∪ B = A)
    (hFne : F.Nonempty) (hBne : B.Nonempty) :
    ∀ r ∈ F, ∀ r' ∈ B, sourcePairing N μ r = sourcePairing N μ r' := by
  obtain ⟨r, hr⟩ := hFne
  obtain ⟨r', hr'⟩ := hBne
  have hsubF : F ⊆ A := by
    rw [← hA]
    exact Finset.subset_union_left
  have hsubB : B ⊆ A := by
    rw [← hA]
    exact Finset.subset_union_right
  intro x hx y hy
  exact (hconst x (hsubF hx) r' (hsubB hr')).trans (hconst r' (hsubB hr') y (hsubB hy))

end General

/-! ### A concrete instance of the two-shelf decomposition -/

namespace TwoShelfExample

open scoped BigOperators

/-- The species of the example: four species `A`, `B`, `C`, `D`. -/
inductive Species
  | A | B | C | D
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B, Species.C, Species.D}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | .A => 1 | _ => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | .B => 1 | _ => 0

/-- The complex `C`. -/
def cC : Complex Species := fun s => match s with | .C => 1 | _ => 0

/-- The complex `D`. -/
def cD : Complex Species := fun s => match s with | .D => 1 | _ => 0

/-- The complex `B + C`. -/
def cBC : Complex Species := fun s => match s with | .B => 1 | .C => 1 | _ => 0

/-- The complex `2 A`. -/
def c2A : Complex Species := fun s => match s with | .A => 2 | _ => 0

/-- The complex `2 B`. -/
def c2B : Complex Species := fun s => match s with | .B => 2 | _ => 0

/-- The complex `D + C`. -/
def cDC : Complex Species := fun s => match s with | .D => 1 | .C => 1 | _ => 0

/-- The six reactions of the example. -/
inductive Rxn
  | r1 | r2 | r3 | r4 | r5 | r6
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2, Rxn.r3, Rxn.r4, Rxn.r5, Rxn.r6}
  complete := by intro r; cases r <;> simp

/-- **The reactions of the example**: two *modules*, each of which balances on its own.

* the first module is `A → B`, `A → C`, `B + C → 2 A`; its reaction vectors sum to zero;
* the second module is `B → D`, `B → C`, `D + C → 2 B`; its reaction vectors sum to zero.

The two modules sit at *different* `μ`-levels, which is what makes the two-shelf
decomposition possible. -/
def reaction : Rxn → Reaction Species
  | .r1 => { source := cA, target := cB }
  | .r2 => { source := cA, target := cC }
  | .r3 => { source := cBC, target := c2A }
  | .r4 => { source := cB, target := cD }
  | .r5 => { source := cB, target := cC }
  | .r6 => { source := cDC, target := c2B }

/-- The network of the example. -/
abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- **The log-ratio of the example**: `μ = (1, 2, −1, 3)`.  The sources of the first module pair
at the level `1` (`⟨A, μ⟩ = 1 = ⟨B + C, μ⟩`), those of the second at the level `2`
(`⟨B, μ⟩ = 2 = ⟨D + C, μ⟩`). -/
def μ : Species → ℝ := fun s => match s with | .A => 1 | .B => 2 | .C => -1 | .D => 3

/-- **The sign-compatible stoichiometric vector**: `σ = (1, 1, −3, 1)`.  It has the same sign
pattern as `μ` and it lies in the stoichiometric subspace. -/
def σ : Species → ℝ := fun s => match s with | .A => 1 | .B => 1 | .C => -3 | .D => 1

/-- **The flux of the example**: the unit flux on every reaction. -/
def α : Rxn → ℝ := fun _ => 1

/-- The sum over the four species of the example. -/
lemma sum_species (f : Species → ℝ) : ∑ s, f s = f .A + f .B + f .C + f .D := by
  have huniv : (Finset.univ : Finset Species) = {Species.A, Species.B, Species.C, Species.D} := by
    ext s
    cases s <;> simp
  show Finset.univ.sum f = _
  rw [huniv]
  simp [Finset.sum_insert, Finset.sum_singleton]
  ring

/-- The pairing of `A`. -/
lemma pairing_cA (ν : Species → ℝ) : complexPairing cA ν = ν .A := by
  rw [complexPairing, sum_species]
  simp [cA]

/-- The pairing of `B`. -/
lemma pairing_cB (ν : Species → ℝ) : complexPairing cB ν = ν .B := by
  rw [complexPairing, sum_species]
  simp [cB]

/-- The pairing of `C`. -/
lemma pairing_cC (ν : Species → ℝ) : complexPairing cC ν = ν .C := by
  rw [complexPairing, sum_species]
  simp [cC]

/-- The pairing of `D`. -/
lemma pairing_cD (ν : Species → ℝ) : complexPairing cD ν = ν .D := by
  rw [complexPairing, sum_species]
  simp [cD]

/-- The pairing of `B + C`. -/
lemma pairing_cBC (ν : Species → ℝ) : complexPairing cBC ν = ν .B + ν .C := by
  rw [complexPairing, sum_species]
  simp [cBC]

/-- The pairing of `2 A`. -/
lemma pairing_c2A (ν : Species → ℝ) : complexPairing c2A ν = 2 * ν .A := by
  rw [complexPairing, sum_species]
  simp [c2A]

/-- The pairing of `2 B`. -/
lemma pairing_c2B (ν : Species → ℝ) : complexPairing c2B ν = 2 * ν .B := by
  rw [complexPairing, sum_species]
  simp [c2B]

/-- The pairing of `D + C`. -/
lemma pairing_cDC (ν : Species → ℝ) : complexPairing cDC ν = ν .C + ν .D := by
  rw [complexPairing, sum_species]
  simp [cDC]

/-- The pairing of the source of each reaction with the log-ratio. -/
lemma sourcePairing_eq (r : Rxn) : sourcePairing N μ r =
    match r with
    | .r1 => 1
    | .r2 => 1
    | .r3 => 1
    | .r4 => 2
    | .r5 => 2
    | .r6 => 2 := by
  cases r <;>
    simp [sourcePairing, reaction, pairing_cA, pairing_cB, pairing_cBC, pairing_cDC, μ] <;> ring

/-- The univ of the reaction index. -/
lemma univ_Rxn : (Finset.univ : Finset Rxn) =
    {Rxn.r1, Rxn.r2, Rxn.r3, Rxn.r4, Rxn.r5, Rxn.r6} := by
  ext r
  cases r <;> simp

/-- **The lower balance of the example**: the unit flux balances the whole network. -/
lemma lower_balance : ∀ s : Species, ∑ r, α r * N.reactionVector r s = 0 := by
  intro s
  rw [univ_Rxn]
  cases s <;>
    simp [α, reactionVector_apply, reaction, cA, cB, cC, cD, cBC, c2A, c2B, cDC,
      Finset.sum_insert, Finset.sum_singleton] <;> ring

/-- **The upper balance of the example**: the unit flux balances the whole network at the upper
state `e^{μ}`. -/
lemma upper_balance : ∀ s : Species,
    ∑ r, α r * Real.exp (sourcePairing N μ r) * N.reactionVector r s = 0 := by
  intro s
  rw [univ_Rxn]
  cases s <;>
    simp [α, sourcePairing_eq, reactionVector_apply, reaction, cA, cB, cC, cD, cBC, c2A, c2B,
      cDC, Finset.sum_insert, Finset.sum_singleton] <;> ring

/-- The log-ratio is nonzero. -/
lemma mu_ne_zero : μ ≠ 0 := by
  intro h
  have h1 := congrFun h Species.A
  simp [μ] at h1

/-- The log-ratio and the stoichiometric vector have the same sign pattern. -/
lemma sameSign : SameSign μ σ := by
  intro s
  cases s <;> simp [μ, σ] <;> norm_num

/-- **The sign-compatible vector lies in the stoichiometric subspace**: `σ = 2 v₁ − 3 v₂ + v₄`. -/
lemma mem_stoichSubspace : σ ∈ N.stoichSubspace := by
  have h1 : N.reactionVector Rxn.r1 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h2 : N.reactionVector Rxn.r2 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h4 : N.reactionVector Rxn.r4 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h12 : (2 : ℝ) • N.reactionVector Rxn.r1 + (-3 : ℝ) • N.reactionVector Rxn.r2
      ∈ N.stoichSubspace :=
    N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem 2 h1) (N.stoichSubspace.smul_mem (-3) h2)
  have h124 : (2 : ℝ) • N.reactionVector Rxn.r1 + (-3 : ℝ) • N.reactionVector Rxn.r2 +
      (1 : ℝ) • N.reactionVector Rxn.r4 ∈ N.stoichSubspace :=
    N.stoichSubspace.add_mem h12 (N.stoichSubspace.smul_mem 1 h4)
  have heq : σ = (2 : ℝ) • N.reactionVector Rxn.r1 + (-3 : ℝ) • N.reactionVector Rxn.r2 +
      (1 : ℝ) • N.reactionVector Rxn.r4 := by
    funext s
    cases s <;>
      simp [σ, reactionVector_apply, reaction, cA, cB, cC, cD,
        Pi.smul_apply, smul_eq_mul] <;> ring
  rw [heq]
  exact h124

/-- The first shelf: the reactions of the first module. -/
def shelf1 : Finset Rxn := {Rxn.r1, Rxn.r2, Rxn.r3}

/-- The second shelf: the reactions of the second module. -/
def shelf2 : Finset Rxn := {Rxn.r4, Rxn.r5, Rxn.r6}

/-- The two shelves cover the reaction set. -/
lemma shelves_cover : shelf1 ∪ shelf2 = Finset.univ := by
  rw [univ_Rxn]
  ext r
  cases r <;> simp [shelf1, shelf2]

/-- The two shelves are disjoint. -/
lemma shelves_disjoint : shelf1 ∩ shelf2 = ∅ := by
  rw [shelf1, shelf2]
  ext r
  cases r <;> simp

/-- The source pairing of each reaction of the first shelf is `1`. -/
lemma sourcePairing_shelf1 (r : Rxn) (hr : r ∈ shelf1) : sourcePairing N μ r = 1 := by
  rcases (Finset.mem_insert.mp hr) with hr | hr
  · rw [hr]
    simp [sourcePairing_eq]
  · rcases (Finset.mem_insert.mp hr) with hr | hr
    · rw [hr]
      simp [sourcePairing_eq]
    · rw [Finset.mem_singleton.mp hr]
      simp [sourcePairing_eq]

/-- The source pairing of each reaction of the second shelf is `2`. -/
lemma sourcePairing_shelf2 (r : Rxn) (hr : r ∈ shelf2) : sourcePairing N μ r = 2 := by
  rcases (Finset.mem_insert.mp hr) with hr | hr
  · rw [hr]
    simp [sourcePairing_eq]
  · rcases (Finset.mem_insert.mp hr) with hr | hr
    · rw [hr]
      simp [sourcePairing_eq]
    · rw [Finset.mem_singleton.mp hr]
      simp [sourcePairing_eq]

/-- **The two-shelf split of the example**: the two modules are pairing-constant at the
distinct levels `1` and `2`. -/
lemma twoShelfSplit : TwoShelfSplit N μ shelf1 shelf2 := by
  refine ⟨shelves_cover, shelves_disjoint, ?_, ?_, ?_⟩
  · intro r hr r' hr'
    rw [sourcePairing_shelf1 r hr, sourcePairing_shelf1 r' hr']
  · intro r hr r' hr'
    rw [sourcePairing_shelf2 r hr, sourcePairing_shelf2 r' hr']
  · refine ⟨Rxn.r1, by simp [shelf1], Rxn.r4, by simp [shelf2], ?_⟩
    simp [sourcePairing_eq]

/-- **The example has the capacity for multiple positive steady states.**  The flux of the
example splits into the two shelf-wise confluence vectors of the two modules. -/
theorem hasCapacity : N.HasMultistationarityCapacity :=
  twoShelf_hasMultistationarityCapacity N μ α shelf1 shelf2 twoShelfSplit
    (fun r => by simp [α]) lower_balance upper_balance mu_ne_zero
    ⟨σ, mem_stoichSubspace, sameSign_symm sameSign⟩

/-- **The example is ADA feasible**: the two shelves carry the shelf-wise confluence vectors. -/
theorem adaFeasible : N.ADAFeasible :=
  twoShelf_adaFeasible N μ α shelf1 shelf2 twoShelfSplit (fun r => by simp [α])
    lower_balance upper_balance mu_ne_zero ⟨σ, mem_stoichSubspace, sameSign_symm sameSign⟩

end TwoShelfExample

end Network
end CRNT
