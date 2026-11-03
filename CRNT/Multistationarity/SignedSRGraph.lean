import CRNT.Multistationarity.SRGraphCriterion
import CRNT.Stoich.Vector
import Mathlib.Data.Sign.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations
import Mathlib.Combinatorics.SimpleGraph.Walk.Traversal

/-!
# The signed species–reaction graph

The Craciun–Feinberg species–reaction-graph criterion for injectivity of the
mass-action vector field refines the unsigned SR-graph by attaching a *sign* to each
species–reaction incidence: the sign of the stoichiometric change the reaction
produces in that species. Cycles in the signed graph carry a multiplicative sign,
and the criterion is phrased in terms of the parity of cycles (the number of
negative incidences they cross) and the way even cycles share terminal edges.

This module records the signed substrate on top of the unsigned `srGraph`.

* `signedEdge` — the sign of a single species–reaction incidence, the `SignType`
  sign of the reaction vector's coordinate.
* `NetChange` and `signedEdge_ne_zero_iff_netChange` — the incidence sign is nonzero
  exactly when the reaction effects a net stoichiometric change in the species.
* `netChange_imp_occursIn` — a net change implies the species occurs in the
  reaction, so a signed incidence is in particular an unsigned adjacency.
* `edgeSignAt` — the incidence sign attached to the `i`-th step of a walk.
* `walkSign` — the product of incidence signs along a walk, with the algebra
  `walkSign_nil`, `walkSign_cons`, `walkSign_append`, `walkSign_copy`.
* `negEdgeCount` and `walkSign_eq_negOnePow_negEdgeCount` — when no step is a zero
  incidence the walk sign is `(-1)` raised to the number of negative incidences.
* `CycleSignNegative` — the predicate that a cycle's sign is `-1`.
* `cycle_even_length` — re-export of the SR-graph evenness of cycles, so cycle sign
  and parity range over an even edge set.

The signs here are `SignType` values of a real (`ℝ`-valued) stoichiometry, so the
sign predicates are propositional: there is no decidable Boolean companion. Relating
the signed-cycle structure to a Jacobian determinant sign — the full Craciun–Feinberg
criterion — additionally requires a determinant-via-cycle-cover expansion and the
mass-action Jacobian, neither of which this module provides.

Depends on:
`CRNT.Multistationarity.SRGraphCriterion`, `CRNT.Stoich.Vector`,
`Mathlib.Data.Sign.Basic`, `Mathlib.Algebra.BigOperators.Group.Finset.Basic`,
`Mathlib.Combinatorics.SimpleGraph.Walk.Operations`,
`Mathlib.Combinatorics.SimpleGraph.Walk.Traversal`.
-/

namespace CRNT

namespace Network

open SimpleGraph Finset

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Incidence signs -/

/-- The sign of the species–reaction incidence `(s, r)`: the `SignType` sign of the
reaction vector's `s`-coordinate, i.e. the sign of the net stoichiometric change
`target s − source s` the reaction produces in the species. -/
noncomputable def signedEdge (N : Network S) (s : S) (r : N.R) : SignType :=
  SignType.sign (N.reactionVector r s)

@[simp] theorem signedEdge_eq_sign_reactionVector (N : Network S) (s : S) (r : N.R) :
    N.signedEdge s r = SignType.sign (N.reactionVector r s) := rfl

/-- A reaction `r` effects a *net change* in species `s` when its reaction vector has
a nonzero `s`-coordinate. -/
def NetChange (N : Network S) (s : S) (r : N.R) : Prop :=
  N.reactionVector r s ≠ 0

/-- The incidence sign is nonzero exactly when the reaction effects a net change in
the species. -/
theorem signedEdge_ne_zero_iff_netChange (N : Network S) (s : S) (r : N.R) :
    N.signedEdge s r ≠ 0 ↔ N.NetChange s r := by
  rw [signedEdge, sign_ne_zero]
  rfl

/-- A net stoichiometric change implies the species occurs in the reaction: a signed
incidence is in particular an unsigned SR-graph incidence. -/
theorem netChange_imp_occursIn (N : Network S) {s : S} {r : N.R}
    (h : N.NetChange s r) : N.OccursIn s r := by
  rw [NetChange, reactionVector_apply] at h
  by_contra hocc
  rw [OccursIn, not_or, not_not, not_not] at hocc
  obtain ⟨hsrc, htgt⟩ := hocc
  rw [hsrc, htgt] at h
  simp at h

/-! ## Walk signs -/

/-- The incidence sign attached to the `i`-th step of a walk in the SR-graph. The
step joins `w.getVert i` and `w.getVert (i + 1)`; on a genuine SR-walk one endpoint
is a species and the other a reaction, and this returns the corresponding
`signedEdge`. The same-side case never arises on a real step (the SR-graph has no
same-side edges), and is given the unit value `1` to keep the function total. -/
noncomputable def edgeSignAt (N : Network S) {u v : N.SRVertex S} (w : N.srGraph.Walk u v) (i : ℕ) :
    SignType :=
  match w.getVert i, w.getVert (i + 1) with
  | Sum.inl s, Sum.inr r => N.signedEdge s r
  | Sum.inr r, Sum.inl s => N.signedEdge s r
  | _, _ => 1

/-- **The sign of a walk:** the product of its incidence signs. -/
noncomputable def walkSign (N : Network S) {u v : N.SRVertex S} (w : N.srGraph.Walk u v) :
    SignType :=
  ∏ i ∈ Finset.range w.length, N.edgeSignAt w i

theorem walkSign_eq_prod (N : Network S) {u v : N.SRVertex S} (w : N.srGraph.Walk u v) :
    N.walkSign w = ∏ i ∈ Finset.range w.length, N.edgeSignAt w i := rfl

/-- The empty walk has sign `1`. -/
@[simp] theorem walkSign_nil (N : Network S) {u : N.SRVertex S} :
    N.walkSign (SimpleGraph.Walk.nil : N.srGraph.Walk u u) = 1 := by
  simp [walkSign]

/-- The incidence sign of the `i`-th step of `w` equals that of the `(i+1)`-th step of
`w.cons h`. -/
theorem edgeSignAt_cons_succ (N : Network S) {t u v : N.SRVertex S}
    (h : N.srGraph.Adj t u) (w : N.srGraph.Walk u v) (i : ℕ) :
    N.edgeSignAt (w.cons h) (i + 1) = N.edgeSignAt w i := by
  simp only [edgeSignAt, SimpleGraph.Walk.getVert_cons_succ]

/-- The sign of a `cons` walk factors as the leading incidence sign times the sign of
the tail. -/
theorem walkSign_cons (N : Network S) {t u v : N.SRVertex S}
    (h : N.srGraph.Adj t u) (w : N.srGraph.Walk u v) :
    N.walkSign (w.cons h) = N.edgeSignAt (w.cons h) 0 * N.walkSign w := by
  rw [walkSign, walkSign, SimpleGraph.Walk.length_cons,
    Finset.prod_range_succ',
    Finset.prod_congr rfl (fun i _ => N.edgeSignAt_cons_succ h w i), mul_comm]

/-- The incidence sign of step `i` of `p.append q` agrees with step `i` of `p` for
`i < p.length`, and otherwise with step `i - p.length` of `q`. -/
theorem edgeSignAt_append (N : Network S) {u v w : N.SRVertex S}
    (p : N.srGraph.Walk u v) (q : N.srGraph.Walk v w) {i : ℕ} (hi : i < p.length) :
    N.edgeSignAt (p.append q) i = N.edgeSignAt p i := by
  have h0 : (p.append q).getVert i = p.getVert i := by
    rw [SimpleGraph.Walk.getVert_append, if_pos hi]
  have h1 : (p.append q).getVert (i + 1) = p.getVert (i + 1) := by
    rw [SimpleGraph.Walk.getVert_append]
    rcases lt_or_eq_of_le (Nat.add_one_le_iff.mpr hi) with hlt | heq
    · rw [if_pos hlt]
    · rw [if_neg (by omega), heq, Nat.sub_self, SimpleGraph.Walk.getVert_zero,
        SimpleGraph.Walk.getVert_length]
  simp only [edgeSignAt, h0, h1]

theorem edgeSignAt_append_right (N : Network S) {u v w : N.SRVertex S}
    (p : N.srGraph.Walk u v) (q : N.srGraph.Walk v w) (j : ℕ) :
    N.edgeSignAt (p.append q) (p.length + j) = N.edgeSignAt q j := by
  have h0 : (p.append q).getVert (p.length + j) = q.getVert j := by
    rw [SimpleGraph.Walk.getVert_append]; simp
  have h1 : (p.append q).getVert (p.length + j + 1) = q.getVert (j + 1) := by
    rw [SimpleGraph.Walk.getVert_append]
    simp only [add_assoc]
    rw [if_neg (by omega)]
    congr 1
    omega
  simp only [edgeSignAt, h0, h1]

/-- **Multiplicativity of the walk sign under concatenation.** -/
theorem walkSign_append (N : Network S) {u v w : N.SRVertex S}
    (p : N.srGraph.Walk u v) (q : N.srGraph.Walk v w) :
    N.walkSign (p.append q) = N.walkSign p * N.walkSign q := by
  rw [walkSign, walkSign, walkSign, SimpleGraph.Walk.length_append,
    Finset.prod_range_add]
  congr 1
  · exact Finset.prod_congr rfl (fun i hi =>
      N.edgeSignAt_append p q (Finset.mem_range.mp hi))
  · exact Finset.prod_congr rfl (fun j _ => N.edgeSignAt_append_right p q j)

/-- The walk sign is invariant under retyping the endpoints. -/
@[simp] theorem walkSign_copy (N : Network S) {u v u' v' : N.SRVertex S}
    (w : N.srGraph.Walk u v) (hu : u = u') (hv : v = v') :
    N.walkSign (w.copy hu hv) = N.walkSign w := by
  subst hu; subst hv; rfl

/-! ## Cycle parity -/

/-- The number of negatively-signed incidences crossed by a walk. -/
noncomputable def negEdgeCount (N : Network S) {u v : N.SRVertex S} (w : N.srGraph.Walk u v) : ℕ :=
  ((Finset.range w.length).filter (fun i => N.edgeSignAt w i = -1)).card

/-- A product over `range n` of `SignType` values, none of which is zero, equals
`(-1)` raised to the number of factors equal to `-1`. -/
theorem prod_signType_eq_negOnePow {n : ℕ} (f : ℕ → SignType)
    (hf : ∀ i ∈ Finset.range n, f i ≠ 0) :
    ∏ i ∈ Finset.range n, f i =
      (-1) ^ ((Finset.range n).filter (fun i => f i = -1)).card := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, Finset.range_add_one, Finset.filter_insert]
    have hfk : f k ≠ 0 := hf k (Finset.mem_range.mpr (Nat.lt_succ_self k))
    have hk_not : k ∉ (Finset.range k).filter (fun i => f i = -1) := by
      simp
    have ih' : ∏ i ∈ Finset.range k, f i =
        (-1) ^ ((Finset.range k).filter (fun i => f i = -1)).card :=
      ih (fun i hi => hf i (Finset.mem_range.mpr
        (Nat.lt_succ_of_lt (Finset.mem_range.mp hi))))
    rcases SignType.trichotomy (f k) with hneg | hzero | hpos
    · rw [if_pos hneg, Finset.card_insert_of_notMem hk_not, ih', hneg, pow_succ]
    · exact absurd hzero hfk
    · rw [if_neg (by rw [hpos]; decide), ih', hpos, mul_one]

/-- **When no step is a zero incidence, the walk sign is `(-1)` to the power of the
number of negative incidences.** -/
theorem walkSign_eq_negOnePow_negEdgeCount (N : Network S) {u v : N.SRVertex S}
    (w : N.srGraph.Walk u v) (hw : ∀ i ∈ Finset.range w.length, N.edgeSignAt w i ≠ 0) :
    N.walkSign w = (-1) ^ N.negEdgeCount w :=
  prod_signType_eq_negOnePow (N.edgeSignAt w) hw

/-- A cycle is **sign-negative** when its walk sign is `-1`. -/
def CycleSignNegative (N : Network S) {u : N.SRVertex S} (w : N.srGraph.Walk u u) : Prop :=
  N.walkSign w = -1

/-! ## Bridge to the unsigned parity facts -/

/-- **Every cycle in the signed SR-graph has even length** (re-export from the
unsigned graph): cycle signs and parities range over an even incidence set. -/
theorem cycle_even_length (N : Network S) {u : N.SRVertex S}
    {w : N.srGraph.Walk u u} (h : w.IsCycle) : Even w.length :=
  srGraph_even_length_of_isCycle N h

section Example

/-- A two-species, single-reaction network `A → B`. -/
private def exampleNetwork : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ =>
    { source := fun s => if s = 0 then 1 else 0
      target := fun s => if s = 1 then 1 else 0 }

/-- The reaction depletes species `0` (it is consumed), so the incidence sign is
negative. -/
example : exampleNetwork.signedEdge 0 () = -1 := by
  have h : exampleNetwork.reactionVector () 0 = -1 := by
    change ((exampleNetwork.reaction ()).target 0 : ℝ) -
      ((exampleNetwork.reaction ()).source 0 : ℝ) = -1
    have ht : (exampleNetwork.reaction ()).target 0 = 0 := rfl
    have hs : (exampleNetwork.reaction ()).source 0 = 1 := rfl
    rw [ht, hs]; norm_num
  change SignType.sign (exampleNetwork.reactionVector () 0) = -1
  rw [h]
  exact sign_neg (by norm_num)

/-- The reaction produces species `1`, so the incidence sign is positive. -/
example : exampleNetwork.signedEdge 1 () = 1 := by
  have h : exampleNetwork.reactionVector () 1 = 1 := by
    change ((exampleNetwork.reaction ()).target 1 : ℝ) -
      ((exampleNetwork.reaction ()).source 1 : ℝ) = 1
    have ht : (exampleNetwork.reaction ()).target 1 = 1 := rfl
    have hs : (exampleNetwork.reaction ()).source 1 = 0 := rfl
    rw [ht, hs]; norm_num
  change SignType.sign (exampleNetwork.reactionVector () 1) = 1
  rw [h]
  exact sign_pos (by norm_num)

end Example

end Network

end CRNT
