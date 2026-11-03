import CRNT.Multistationarity.TrueSRDegreeTwoNoSToR
import CRNT.Multistationarity.TrueSRSSGlueCPairs
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.NormNum

/-!
# What degree-two isolation forces: the parity and cross-class consequences

`TrueSRDegreeTwoNoSToR.lean` records the graph-theoretic content of "the reactions of `C` have
SR-degree two": a common-edge component between `C` and any other cycle cannot *end* at a reaction
of `C`.  This file works out what such a configuration forces on the *parity* side, which is
where the remaining obligations of the degree-two case live.

## 1. Degree two ⟹ no c-pair ⟹ the cycle is an e-cycle for free

The chain is short and each link is already in the repository:

* a c-pair at index `j` forces a third SR edge off `C` at `C.reaction j`
  (`Network.exists_offCycle_edge_of_isCPair`);
* degree two says there is no such edge (`TrueSRCycle.DegreeTwo` below);
* so `C.numCPairs = 0`, so `C.Even` — *unconditionally*, with no criterion hypothesis at all.

This is the cross-class consequence: at every reaction vertex of a degree-two cycle the two cycle
edges carry **different** endpoint complexes, so the cycle crosses each reaction instead of
turning back on one side (`TrueSRCycle.crossClass_of_degree_two`,
`TrueSRCycle.left_species_occurs_in_source`, `TrueSRCycle.right_species_occurs_in_target`).

Because `C.Even` is free, the *first* conjunct of `TrueSRStrongCriterion` bites:
`TrueSRCycle.sCycle_of_degree_two_of_trueSRCriterion` produces `C.SCycle` with no further input.

## 2. The strict-gain contradiction, in `SCycle` labels

`TrueChemistrySRCriterion.lean` carries `TrueSRCycle.no_strict_gain'` and friends, but that module
also carries the theorem's remaining `sorry`, so nothing here may depend on it.
`TrueSRCycle.no_strict_gain_labels` is proved from scratch in this file, in exactly the form the
degree-two endgame needs: an `SCycle` (stoichiometric labels) cannot support a strict gain
telescoping all the way around.  Combining it with §1 gives

`false_of_degree_two_strict_gain`

which closes the degree-two case of the true-SR argument **up to the gain hypotheses**: once a
degree-two reaction vertex is isolated, the only thing left to produce is the family of positive
multipliers and the pointwise strict inequalities, which come from `InKerL α` and `hopp`.

## 3. Where `hSR.2` is — and is not — used

`TrueSRStrongCriterion`'s second conjunct is the "no S-to-R sharing" half.  This file isolates
exactly how much work it does in the degree-two case:

* `TrueSRCycle.no_sToRIntersection_of_degree_two'` needs **no** hypothesis whatsoever.  So on a
  degree-two cycle the sharing half of the criterion is *vacuous*: it is never invoked, and it can
  never be the step that produces a contradiction.
* `false_of_shared_sToR_of_trueSRCriterion` is the place `hSR.2` is actually used, in one
  line, and it is the only such use.

This is the machine-checked form of the statement "degree-two isolation cannot be discharged by
`hSR.2`; it must be discharged by `hSR.1` together with the strict gain".

## 4. The c-pair counting obstruction for species-to-species glues

`ssGlueCycle_numCPairs` gives `numCPairs (P ∪ Q) = ssNumCPairs P + ssNumCPairs Q` with no seam
term.  Degree two of the glued cycle therefore forces **both** arcs to be c-pair-free:

* `TrueSRSSPath.ssGlue_degree_two_zero`, and hence
* `TrueSRSSPath.ssGlue_even_of_degree_two`, `TrueSRSSPath.ssGlue_not_odd_of_degree_two`,
* `TrueSRSSPath.ssGlue_sCycle_of_degree_two_of_trueSRCriterion` (via `hSR.1`),
* `TrueSRSSPath.ssGlue_parity_transport`: with `ssNumCPairs P = 0` the parity of `P ∪ Q` is the
  parity of `ssNumCPairs Q` alone, so the chord `P` is parity-invisible — the odd-c-pair
  configurations are exactly the ones degree two excludes.

## 5. Residuals

The remaining obligations are recorded as `Prop`s in the `Residual` namespace at the end of this
file, so that they are machine-readable statements rather than prose.  `Residual.DegTwoGain`
is the only one still needed for the degree-two case; it is the `InKerL α`/`hopp` input and lives
outside the graph theory.
-/

namespace CRNT.Network

open scoped BigOperators
open Finset

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-! ### The degree-two predicate -/

/-- **SR-degree two at the reactions of `C`.**  Every true-SR edge incident to a reaction vertex
of `C` is one of the two edges `C` uses there; there is no third edge.

This is the hypothesis of `no_sToRIntersection_of_degree_two`, named so that the parity
consequences below can refer to it. -/
def TrueSRCycle.DegreeTwo (C : N.TrueSRCycle n) : Prop :=
  ∀ (e : N.TrueSREdge) (i : Fin n), e.reaction = C.reaction i →
    e.SameIncidence (C.leftEdge i) ∨ e.SameIncidence (C.rightEdge i)

/-- **Degree two means every edge at a reaction of `C` is a cycle edge.** -/
theorem TrueSRCycle.containsEdge_of_degree_two (C : N.TrueSRCycle n)
    (hdeg : C.DegreeTwo) (e : N.TrueSREdge) (i : Fin n) (her : e.reaction = C.reaction i) :
    C.ContainsEdge e := by
  rcases hdeg e i her with h | h
  · exact Or.inl ⟨i, h⟩
  · exact Or.inr ⟨i, h⟩

/-- **Degree two means no edge leaves `C` at a reaction of `C`.**  This is the contrapositive
form of `containsEdge_of_degree_two`, and it is what rules out c-pairs. -/
theorem TrueSRCycle.no_offCycle_edge_of_degree_two (C : N.TrueSRCycle n)
    (hdeg : C.DegreeTwo) :
    ¬ ∃ (e : N.TrueSREdge) (i : Fin n), e.reaction = C.reaction i ∧ ¬ C.ContainsEdge e := by
  rintro ⟨e, i, her, hnc⟩
  exact hnc (C.containsEdge_of_degree_two hdeg e i her)

/-! ### 1. Degree two ⟹ no c-pair ⟹ an even cycle, for free -/

/-- **Degree two forbids c-pairs.**  A c-pair at index `j` forces a third edge off `C` at
`C.reaction j` (reactant/product separation plus internality of the class), and degree two says
there is none. -/
theorem TrueSRCycle.no_isCPair_of_degree_two (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) (j : Fin n) : ¬ C.isCPair j := by
  intro hpair
  obtain ⟨f, hfr, -, -, hcont⟩ := N.exists_offCycle_edge_of_isCPair hsep C j hpair
  exact (C.no_offCycle_edge_of_degree_two hdeg) ⟨f, j, hfr, hcont⟩

/-- **A degree-two cycle has no c-pair at all**, so `numCPairs C = 0`. -/
theorem TrueSRCycle.numCPairs_eq_zero_of_degree_two (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) : C.numCPairs = 0 := by
  classical
  refine Finset.card_eq_zero.mpr (Finset.eq_empty_of_forall_notMem ?_)
  intro t ht
  exact C.no_isCPair_of_degree_two hsep hdeg t (Finset.mem_filter.mp ht).2

/-- **Every degree-two cycle is an e-cycle.**  No criterion hypothesis is needed: the second
conjunct of `TrueSRStrongCriterion` is not what makes this even. -/
theorem TrueSRCycle.even_of_degree_two (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) : C.Even := by
  refine ⟨0, ?_⟩
  rw [C.numCPairs_eq_zero_of_degree_two hsep hdeg]

/-- **Degree two turns the first conjunct of the criterion on.**  A degree-two cycle is an
e-cycle, so `hSR` forces it to be an s-cycle.  This is the step that replaces the (vacuous)
sharing half in the degree-two case. -/
theorem TrueSRCycle.sCycle_of_degree_two_of_trueSRCriterion
    (hSR : N.TrueSRStrongCriterion) (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) : C.SCycle :=
  hSR.1 C (C.even_of_degree_two hsep hdeg)

/-- A degree-two cycle is never an odd cycle: `Odd m` unpacks to `m = 2 * k + 1`, which `0`
rules out. -/
theorem TrueSRCycle.not_odd_of_degree_two (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) : ¬ Odd C.numCPairs := by
  rintro ⟨k, hk⟩
  rw [C.numCPairs_eq_zero_of_degree_two hsep hdeg] at hk
  omega

/-! ### The cross-class consequence -/

/-- **At a degree-two reaction vertex the cycle crosses the reaction.**  The two cycle edges carry
*different* endpoint complexes; since both lie in the two-element set `{source, target}` of any
representative of the class, one is the reactant side and the other the product side.

Concretely: the cycle cannot "turn back" at this vertex — it does not visit the same side twice.
This is what forces the labels at the two edges to be a reactant coefficient and a product
coefficient, so that `SCycle` compares reactants against products rather than a species with
itself. -/
theorem TrueSRCycle.crossClass_of_degree_two (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) (i : Fin n) :
    ((C.leftEdge i).endpoint = (N.reaction (C.leftEdge i).representative).source ∧
        (C.rightEdge i).endpoint = (N.reaction (C.leftEdge i).representative).target) ∨
    ((C.leftEdge i).endpoint = (N.reaction (C.leftEdge i).representative).target ∧
        (C.rightEdge i).endpoint = (N.reaction (C.leftEdge i).representative).source) := by
  have hne : (C.leftEdge i).endpoint ≠ (C.rightEdge i).endpoint :=
    C.no_isCPair_of_degree_two hsep hdeg i
  have hmem : (C.rightEdge i).endpoint =
        (N.reaction (C.leftEdge i).representative).source ∨
      (C.rightEdge i).endpoint = (N.reaction (C.leftEdge i).representative).target :=
    endpoint_pair_of_sameReaction ((C.right_reaction i).trans (C.left_reaction i).symm)
  rcases (C.leftEdge i).endpoint_is_source_or_target with hsrc | htgt <;> rcases hmem with hmem | hmem
  · exact absurd (hmem.trans hsrc.symm) (fun h => hne h.symm)
  · exact Or.inl ⟨hsrc, hmem⟩
  · exact Or.inr ⟨htgt, hmem⟩
  · exact absurd (hmem.trans htgt.symm) (fun h => hne h.symm)

/-- The reactant-side statement on its own, in the orientation produced by the first disjunct.
The occurrence hypothesis `TrueSREdge.occurs` turns "the left edge carries the reactant complex"
into "the left cycle species is a reactant". -/
theorem TrueSRCycle.left_species_occurs_in_source (C : N.TrueSRCycle n)
    (i : Fin n)
    (h : (C.leftEdge i).endpoint = (N.reaction (C.leftEdge i).representative).source) :
    (N.reaction (C.leftEdge i).representative).source (C.species i) ≠ 0 := by
  have hocc := (C.leftEdge i).occurs
  rw [h, C.left_species i] at hocc
  exact hocc

/-- Likewise for the product side. -/
theorem TrueSRCycle.right_species_occurs_in_target (C : N.TrueSRCycle n)
    (i : Fin n)
    (h : (C.rightEdge i).endpoint = (N.reaction (C.leftEdge i).representative).target) :
    (N.reaction (C.leftEdge i).representative).target
      (C.species ⟨(i.1 + 1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩) ≠ 0 := by
  have hocc := (C.rightEdge i).occurs
  rw [h, C.right_species i] at hocc
  exact hocc

/-! ### 2. Strict gain in `SCycle` labels, and the degree-two contradiction -/

/-- **An `s`-cycle cannot support a strict gain all the way around, in `SCycle` labels.**

This is `TrueSRCycle.no_strict_gain'` re-proved here so that this module does not depend on
`TrueChemistrySRCriterion.lean` (which still carries the theorem's remaining `sorry`).  The
inequality is oriented with the rotation on the left-hand factor family, which is the orientation
`gain_of_two_term_flux` produces at an end species-block of degree two. -/
theorem TrueSRCycle.no_strict_gain_labels {m : ℕ} (C : N.TrueSRCycle m)
    (hsc : C.SCycle) (a : Fin m → ℝ) (ha : ∀ i, 0 < a i)
    (hineq : ∀ i, ((C.leftEdge (finRotate m i)).coeff : ℝ) * a (finRotate m i) <
      ((C.rightEdge i).coeff : ℝ) * a i) : False := by
  haveI : NeZero m := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide) C.nontrivial)⟩
  have hz : Fin m := Fin.mk (0 : ℕ) (by have := C.nontrivial; omega)
  have hp : (∏ i : Fin m, ((C.leftEdge (finRotate m i)).coeff : ℝ) * a (finRotate m i))
      < ∏ i : Fin m, ((C.rightEdge i).coeff : ℝ) * a i := by
    refine Finset.prod_lt_prod₀
      (fun i _ => mul_pos (Nat.cast_pos.mpr ((C.leftEdge (finRotate m i)).coeff_pos)) (ha (finRotate m i)))
      (fun i _ => (hineq i).le) ⟨hz, Finset.mem_univ _, hineq hz⟩
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    Equiv.prod_comp (finRotate m) (fun i => ((C.leftEdge i).coeff : ℝ)),
    Equiv.prod_comp (finRotate m) (fun i => a i)] at hp
  have hscR : (∏ i : Fin m, ((C.leftEdge i).coeff : ℝ)) =
      ∏ i : Fin m, ((C.rightEdge i).coeff : ℝ) := by exact_mod_cast hsc
  rw [hscR] at hp
  have hRp : 0 ≤ ∏ i : Fin m, ((C.rightEdge i).coeff : ℝ) :=
    (prod_pos fun i _ => Nat.cast_pos.mpr (C.rightEdge i).coeff_pos).le
  exact lt_irrefl _ (lt_of_mul_lt_mul_left hp hRp)

/-- **The degree-two endgame.**  Once a degree-two reaction vertex is isolated, the parity side is
complete: `C` is an s-cycle (unconditionally even, by `sCycle_of_degree_two_of_trueSRCriterion`)
and an s-cycle cannot carry a strict gain.  The only remaining input is the family of positive
multipliers `a` together with the pointwise strict inequalities, which come from `InKerL α` and
the causal orientation `hopp` — not from the SR graph. -/
theorem false_of_degree_two_strict_gain
    (hSR : N.TrueSRStrongCriterion) (hsep : N.ReactantProductSeparated)
    {n : ℕ} (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo)
    (a : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hineq : ∀ i, ((C.leftEdge (finRotate n i)).coeff : ℝ) * a (finRotate n i) <
      ((C.rightEdge i).coeff : ℝ) * a i) : False :=
  TrueSRCycle.no_strict_gain_labels C
    (C.sCycle_of_degree_two_of_trueSRCriterion hSR hsep hdeg) a ha hineq

/-! ### 3. Where `hSR.2` is and is not used -/

/-- **The single place the sharing half of the criterion is used.**  Two even cycles with a
certified S-to-R intersection are contradictory, and this is the only place in the degree-two
development where `TrueSRStrongCriterion`'s second conjunct appears at all. -/
theorem false_of_shared_sToR_of_trueSRCriterion
    (hSR : N.TrueSRStrongCriterion) {m k : ℕ} (C : N.TrueSRCycle m) (D : N.TrueSRCycle k)
    (hC : C.Even) (hD : D.Even) (hI : Nonempty (C.SToRIntersection D)) : False :=
  hSR.2 C D hC hD hI

/-- **On a degree-two cycle the sharing half is vacuous.**  `hSR.2` is never invoked and never
needed; the S-to-R intersection is impossible for a purely combinatorial reason.  Consequently
degree-two isolation *cannot* be discharged by the sharing half of the criterion — that would be
proving a contradiction from a hypothesis which has no content there. -/
theorem TrueSRCycle.no_sToRIntersection_of_degree_two' {m k : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle k) (hdeg : C.DegreeTwo) :
    ¬ Nonempty (C.SToRIntersection D) :=
  no_sToRIntersection_of_degree_two C D hdeg

/-- The two halves side by side.  On a degree-two cycle the first half produces an `SCycle` and
the second half produces nothing at all. -/
theorem degree_two_halves_are_asymmetric
    (hSR : N.TrueSRStrongCriterion) (hsep : N.ReactantProductSeparated)
    {n k : ℕ} (C : N.TrueSRCycle n) (D : N.TrueSRCycle k) (hdeg : C.DegreeTwo) :
    C.SCycle ∧ ¬ Nonempty (C.SToRIntersection D) :=
  ⟨C.sCycle_of_degree_two_of_trueSRCriterion hSR hsep hdeg,
    TrueSRCycle.no_sToRIntersection_of_degree_two' C D hdeg⟩

/-! ### 4. The c-pair counting obstruction for species-to-species glues -/

namespace TrueSRSSPath

variable {i j : ℕ} (P : N.TrueSRSSPath (2 * j + 2)) (Q : N.TrueSRSSPath (2 * i + 2))
  (h : SSGluable P Q)

/-- **A degree-two glued cycle has no c-pair.** -/
theorem ssGlue_no_isCPair_of_degree_two
    (hsep : N.ReactantProductSeparated)
    (hdeg : (ssGlueCycle P Q h).DegreeTwo) (t : Fin (i + 1 + j + 1)) :
    ¬ (ssGlueCycle P Q h).isCPair t :=
  TrueSRCycle.no_isCPair_of_degree_two hsep (ssGlueCycle P Q h) hdeg t

/-- **… hence it has no c-pairs at all.** -/
theorem ssGlue_numCPairs_eq_zero_of_degree_two (hsep : N.ReactantProductSeparated)
    (hdeg : (ssGlueCycle P Q h).DegreeTwo) : (ssGlueCycle P Q h).numCPairs = 0 :=
  TrueSRCycle.numCPairs_eq_zero_of_degree_two hsep (ssGlueCycle P Q h) hdeg

/-- **… and it is an even cycle for free.** -/
theorem ssGlue_even_of_degree_two (hsep : N.ReactantProductSeparated)
    (hdeg : (ssGlueCycle P Q h).DegreeTwo) : (ssGlueCycle P Q h).Even :=
  TrueSRCycle.even_of_degree_two hsep (ssGlueCycle P Q h) hdeg

/-- **Degree two excludes every odd c-pair configuration.** -/
theorem ssGlue_not_odd_of_degree_two (hsep : N.ReactantProductSeparated)
    (hdeg : (ssGlueCycle P Q h).DegreeTwo) : ¬ Odd ((ssGlueCycle P Q h).numCPairs) :=
  TrueSRCycle.not_odd_of_degree_two hsep (ssGlueCycle P Q h) hdeg

/-- **Degree two of the glue forces *both* arcs to be c-pair-free.**  This is the cross-class
counting statement: `numCPairs (P ∪ Q) = ssNumCPairs P + ssNumCPairs Q`, and the left-hand side
vanishes, so each summand does. -/
theorem ssGlue_degree_two_zero (hsep : N.ReactantProductSeparated)
    (hdeg : (ssGlueCycle P Q h).DegreeTwo) : ssNumCPairs P = 0 ∧ ssNumCPairs Q = 0 := by
  have hz : ssNumCPairs P + ssNumCPairs Q = 0 := by
    rw [← ssGlueCycle_numCPairs P Q h]
    exact ssGlue_numCPairs_eq_zero_of_degree_two P Q h hsep hdeg
  omega

/-- The glued cycle is an s-cycle, by the first conjunct of the criterion. -/
theorem ssGlue_sCycle_of_degree_two_of_trueSRCriterion
    (hSR : N.TrueSRStrongCriterion) (hsep : N.ReactantProductSeparated)
    (hdeg : (ssGlueCycle P Q h).DegreeTwo) : (ssGlueCycle P Q h).SCycle :=
  TrueSRCycle.sCycle_of_degree_two_of_trueSRCriterion hSR hsep (ssGlueCycle P Q h) hdeg

/-- **Parity transport.**  With a c-pair-free chord `P`, the parity of `P ∪ Q` is the parity of
`ssNumCPairs Q` alone: the chord contributes nothing.  So the two gluings `P ∪ Q₁` and `P ∪ Q₂`
share their parity status, and the odd-c-pair configuration is exactly the one degree two rules
out. -/
theorem ssGlue_parity_transport (hsep : N.ReactantProductSeparated)
    (hdeg : (ssGlueCycle P Q h).DegreeTwo) :
    (ssGlueCycle P Q h).Even ↔ _root_.Even (ssNumCPairs Q) := by
  change _root_.Even (ssGlueCycle P Q h).numCPairs ↔ _
  have hQ0 : ssNumCPairs Q = 0 := by
    have hsum : ssNumCPairs P + ssNumCPairs Q = 0 := by
      rw [← ssGlueCycle_numCPairs P Q h]
      exact ssGlue_numCPairs_eq_zero_of_degree_two P Q h hsep hdeg
    omega
  constructor
  · intro _
    rw [hQ0]
    exact ⟨0, rfl⟩
  · intro _
    rw [ssGlue_numCPairs_eq_zero_of_degree_two P Q h hsep hdeg]
    exact ⟨0, rfl⟩

end TrueSRSSPath

/-! ### Residuals

The open obligations of the degree-two case, as machine-readable statements.  Each is a `Prop`
rather than a theorem: none of them is proved here, and each is stated in exactly the form a
producer must supply. -/

namespace Residual

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

/-- **The single remaining input for the degree-two case.**  A witness `(α, σ)` for
`InKerL α` together with the causal orientation data must produce, on the causal cycle `C`, a
family of positive multipliers and the pointwise strict gain inequalities.  Everything else in
the degree-two case is already discharged: `C.Even` is free
(`even_of_degree_two`), `C.SCycle` follows (`sCycle_of_degree_two_of_trueSRCriterion`), and
`no_strict_gain_labels` refutes the gain.  This is not graph theory — it is the `InKerL α` /
`hopp` step. -/
def DegTwoGain (C : N.TrueSRCycle n) : Prop :=
  ∃ (a : Fin n → ℝ), (∀ i, 0 < a i) ∧
    (∀ i, ((C.leftEdge (finRotate n i)).coeff : ℝ) * a (finRotate n i) <
      ((C.rightEdge i).coeff : ℝ) * a i)

/-- The degree-two case closes exactly when `DegTwoGain` is available at the isolated cycle. -/
theorem degTwoGain_refutes (hSR : N.TrueSRStrongCriterion) (hsep : N.ReactantProductSeparated)
    {n : ℕ} (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) (h : DegTwoGain C) : False := by
  obtain ⟨a, ha, hineq⟩ := h
  exact false_of_degree_two_strict_gain hSR hsep C hdeg a ha hineq

/-- **Isolating a degree-two reaction vertex in the residue of
`TrueChemistrySRCriterion.lean`.**  The residue is reached with `vertex0 = s0` a cycle species and
the rest of the shortest route of length one.  The degree-two statement needed there is that the
reaction class entered on the first hop has no third edge, i.e. exactly `TrueSRCycle.DegreeTwo` at
that index — nothing weaker is provable from `hSR` alone. -/
def IsolateDegreeTwo (C : N.TrueSRCycle n) (k : Fin n) : Prop := C.DegreeTwo

/-- A degree-two cycle is an e-cycle and hence an s-cycle, with no sharing hypothesis involved.
Recorded as a `Prop` so that the *combination* used by the residue is nameable. -/
def DegreeTwoParity (C : N.TrueSRCycle n) : Prop :=
  (∀ i : Fin n, ¬ C.isCPair i) ∧ C.numCPairs = 0 ∧ C.Even ∧ C.SCycle

/-- Degree two delivers `DegreeTwoParity` outright. -/
theorem degreeTwoParity (hSR : N.TrueSRStrongCriterion) (hsep : N.ReactantProductSeparated)
    {n : ℕ} (C : N.TrueSRCycle n) (hdeg : C.DegreeTwo) : DegreeTwoParity C :=
  ⟨fun i => C.no_isCPair_of_degree_two hsep hdeg i,
   C.numCPairs_eq_zero_of_degree_two hsep hdeg,
   C.even_of_degree_two hsep hdeg,
   C.sCycle_of_degree_two_of_trueSRCriterion hSR hsep hdeg⟩

end Residual

end CRNT.Network