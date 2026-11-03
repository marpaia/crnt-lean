import CRNT.Computation.PiecewiseNatAffineRealization
import Mathlib.Data.Fintype.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Composition of stable computations

This file provides the **composition lemma** for stable computations by chemical reaction
networks, the technical keystone that makes the *realization* direction of the
Chen–Doty–Soloveichik programme systematic.

## The framework

Following Chen–Doty–Soloveichik (*Deterministic function computation with chemical
reaction networks*, Natural Computing 13 (2014)), a network **stably computes** a function
`f` if, from the configuration encoding the input, *every* execution can be continued to an
*output-stable* configuration — one from which the count of the output species can never
change again — whose output count is `f` of the input.  This is the predicate
`CRNT.Computation.StablyComputes` of `CRNT.Computation.StableComputation`, and it is the
notion used throughout the repository.

The classes realized in the repository so far are the elementary ones — `+`, `min`, `k·`,
`max` (`CRNT.Computation.addCRN_stablyComputes`, `minCRN_stablyComputes`,
`scaleCRN_stablyComputes`, `maxCRN_stablyComputes`), the affine maps
(`CRNT.Computation.affineCRN_stablyComputes`) and the *min-of-affine* family
(`CRNT.Computation.MinAffine.minAffineCRN_stablyComputes`, together with
`minList_piecewiseNatAffine` for the piecewiseNatAffineity of the class).  The corresponding
*piecewiseNatAffine* characterization is `CRNT.Computation.PiecewiseNatAffine`: a function `ℕ^d → ℕ` is
piecewiseNatAffine if `ℕ^d` is covered by finitely many regions on each of which the function is a
fixed affine map.  Note that this notion of piecewiseNatAffineity is *weaker* than Presburger
piecewiseNatAffineity: it carries no congruence conditions.

## What this file adds

The **composition lemma** `CRNT.Computation.stablyComputes_comp`: the network
`compNetwork` runs `k` networks `N₁ i` in parallel, one per *row* (a disjoint copy of the
species), transfers the output of row `i` to the input species `τ i` of a second network
`N₂`, and lets `N₂` collect the transferred molecules.  If the rows stably compute
`f₁ i` and `N₂` is a *collector* for the input species — a network in which every molecule
entering at `τ i` is converted into a fixed target — then the composed network stably
computes `a ↦ f₂ (fun i => f₁ i a)`.

The proof has three parts.

* **Termination.**  The potential `compPotential` decreases at every step of the composed
  network: a step of a row decreases the weighted sum of that row, a step of the second
  network decreases the weighted sum of the second part, and a transfer reaction moves one
  molecule from the output species of a row to the input species of the second part.  The
  three cases are `compPotential_row_step`, `compPotential_tail_step` and
  `compPotential_transfer_step`.

* **The shadow of a row.**  `CRNT.Computation.comp_shadow` records, along a run of the
  composed network, the *shadow* of each row — the row with the transferred molecules
  restored — and shows that the shadow is reachable in the network `N₁ i`, that the
  transferred molecules `tr i` and the conversions `ph i` of the second network satisfy
  `tr i = ph i + (tailOf c) (τ i)`, and that the output of the second part is
  `∑ i, ph i * w i`.

* **Correctness.**  At a terminal configuration the shadow of a row is terminal for `N₁ i`,
  hence displays `f₁ i`; the transfer reactions have drained the rows, so `tr i = f₁ i`; the
  second network has consumed all its input, so `ph i = tr i`; and the output of the second
  part is therefore `∑ i, f₁ i * w i`, which is `f₂ (fun i => f₁ i a)` by
  `CRNT.Computation.collector_function`.

The supporting theory of *collectors* — networks whose reactions each consume exactly one
molecule of an input species and produce a fixed target — is in
`CRNT.Computation.Collector`, `collector_invariant`, `collector_output` and
`collector_function`.

## What remains open

The **full** Chen–Doty–Soloveichik theorem is *not* proved here.  It asserts that every
piecewiseNatAffine function is stably computable (the realization direction, for *arbitrary*
networks) and that every stably computable function is piecewiseNatAffine (the necessity
direction, for arbitrary networks).  This file contributes the composition machinery that
makes the realization direction systematic for the classes built so far; the necessity
direction is known in the repository only under extra hypotheses (output-conserving
networks: `CRNT.Computation.output_conserving_piecewiseNatAffine`).
-/

namespace CRNT
namespace Computation

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The unit vector at the species `s`: one molecule of `s` and nothing else. -/



def unitVec {S : Type} [DecidableEq S] (s : S) : S → ℕ := fun t => if t = s then 1 else 0

/-- The species of a **composed network**: `k` disjoint copies of `S` (the *rows*, one
per first network) together with the species of the second network. -/
abbrev CompSpecies (k : ℕ) (S T : Type) := (Σ _i : Fin k, S) ⊕ T

/-- The row `i` of a configuration of the composed species. -/
def rowOf {k : ℕ} {S T : Type} (c : Config (CompSpecies k S T)) (i : Fin k) : Config S :=
  fun s => c (Sum.inl (Sigma.mk i s))

/-- The second part of a configuration of the composed species. -/
def tailOf {k : ℕ} {S T : Type} (c : Config (CompSpecies k S T)) : Config T :=
  fun t => c (Sum.inr t)

/-- Embed a configuration of `S` into the row `i` of the composed species. -/
def embedRow {k : ℕ} {S T : Type} (i : Fin k) (w : S → ℕ) : Config (CompSpecies k S T) :=
  fun s => match s with
    | Sum.inl (Sigma.mk j t) => if j = i then w t else 0
    | Sum.inr _ => 0

/-- Embed a configuration of `T` into the second part of the composed species. -/
def embedTail {k : ℕ} {S T : Type} (w : T → ℕ) : Config (CompSpecies k S T) :=
  fun s => match s with
    | Sum.inl _ => 0
    | Sum.inr t => w t

@[simp] theorem embedRow_inl {k : ℕ} {S T : Type} (i j : Fin k) (w : S → ℕ) (t : S) :
    embedRow i w ((Sum.inl (Sigma.mk j t) : CompSpecies k S T)) = if j = i then w t else 0 := rfl

@[simp] theorem embedRow_inr {k : ℕ} {S T : Type} (i : Fin k) (w : S → ℕ) (t : T) :
    embedRow i w ((Sum.inr t : CompSpecies k S T)) = 0 := rfl

@[simp] theorem embedTail_inl {k : ℕ} {S T : Type} (w : T → ℕ) (i : Fin k) (t : S) :
    embedTail w ((Sum.inl (Sigma.mk i t) : CompSpecies k S T)) = 0 := rfl

@[simp] theorem embedTail_inr {k : ℕ} {S T : Type} (w : T → ℕ) (t : T) :
    embedTail w ((Sum.inr t : CompSpecies k S T)) = w t := rfl

@[simp] theorem rowOf_inl {k : ℕ} {S T : Type} (c : Config (CompSpecies k S T)) (i : Fin k)
    (t : S) : rowOf c i t = c ((Sum.inl (Sigma.mk i t) : CompSpecies k S T)) := rfl

@[simp] theorem tailOf_inr {k : ℕ} {S T : Type} (c : Config (CompSpecies k S T)) (t : T) :
    tailOf c t = c ((Sum.inr t : CompSpecies k S T)) := rfl

/-- **The composed network.**  The rows `i` run the first networks `N₁ i`, whose output
species `o i` is *transferred* to the input species `τ i` of the second network `N₂` by
the transfer reaction `o i → τ i`; the second network then collects the transferred
molecules. -/
def compNetwork {k : ℕ} {S T : Type} [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T) (N₂ : Network T) :
    Network (CompSpecies k S T) :=
  { R := Sigma (fun i : Fin k => (N₁ i).R) ⊕ N₂.R ⊕ Fin k
    decEqR := inferInstance
    fintypeR := inferInstance
    reaction := fun r => match r with
      | Sum.inl (Sigma.mk i ri) =>
          ⟨embedRow i ((N₁ i).reaction ri).source, embedRow i ((N₁ i).reaction ri).target⟩
      | Sum.inr (Sum.inl r₂) =>
          ⟨embedTail ((N₂.reaction r₂).source), embedTail ((N₂.reaction r₂).target)⟩
      | Sum.inr (Sum.inr i) => ⟨embedRow i (unitVec (o i)), embedTail (unitVec (τ i))⟩ }

/-- The initial configuration of the composed network: the initial configuration of each
first network in its own row, and an empty second part. -/
def compInit {k : ℕ} {α : Type} {S T : Type} (init₁ : Fin k → α → Config S) (a : α) :
    Config (CompSpecies k S T) :=
  fun s => match s with
    | Sum.inl (Sigma.mk i t) => init₁ i a t
    | Sum.inr _ => 0

@[simp] theorem compInit_inl {k : ℕ} {α : Type} {S T : Type} (init₁ : Fin k → α → Config S)
    (a : α) (i : Fin k) (t : S) :
    compInit init₁ a ((Sum.inl (Sigma.mk i t) : CompSpecies k S T)) = init₁ i a t := rfl

@[simp] theorem compInit_inr {k : ℕ} {α : Type} {S T : Type} (init₁ : Fin k → α → Config S)
    (a : α) (t : T) :
    compInit init₁ a ((Sum.inr t : CompSpecies k S T)) = 0 := rfl

/-- The **shadow** of a configuration of a row: the configuration with `n` extra
molecules at the species `t0`.  The shadow of a row is the configuration the first
network would have reached if the transfer reactions had not fired. -/
def shadowOf {S : Type} [DecidableEq S] (c : Config S) (t0 : S) (n : ℕ) : Config S :=
  fun t => c t + (if t = t0 then n else 0)

section Comp

variable {k : ℕ} {T : Type} [DecidableEq T] [Fintype T]

/-- The source complex of a step of the first network in row `i`. -/
@[simp] theorem compSource_row (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i j : Fin k) (ri : (N₁ i).R) (t : S) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).source
        (Sum.inl (Sigma.mk j t)) = if j = i then ((N₁ i).reaction ri).source t else 0 := rfl

/-- The target complex of a step of the first network in row `i`. -/
@[simp] theorem compTarget_row (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i j : Fin k) (ri : (N₁ i).R) (t : S) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).target
        (Sum.inl (Sigma.mk j t)) = if j = i then ((N₁ i).reaction ri).target t else 0 := rfl

/-- The source complex of a step of the first network, at a species of the second part. -/
@[simp] theorem compSource_row_inr (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (ri : (N₁ i).R) (t : T) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).source (Sum.inr t) = 0 := rfl

/-- The target complex of a step of the first network, at a species of the second part. -/
@[simp] theorem compTarget_row_inr (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (ri : (N₁ i).R) (t : T) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).target (Sum.inr t) = 0 := rfl

/-- The source complex of a step of the second network. -/
@[simp] theorem compSource_tail (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (r₂ : N₂.R) (t : T) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).source (Sum.inr t)
      = (N₂.reaction r₂).source t := rfl

/-- The target complex of a step of the second network. -/
@[simp] theorem compTarget_tail (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (r₂ : N₂.R) (t : T) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).target (Sum.inr t)
      = (N₂.reaction r₂).target t := rfl

/-- The source complex of a step of the second network, at a species of a row. -/
@[simp] theorem compSource_tail_inl (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (r₂ : N₂.R) (i : Fin k) (t : S) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).source (Sum.inl (Sigma.mk i t))
      = 0 := rfl

/-- The target complex of a step of the second network, at a species of a row. -/
@[simp] theorem compTarget_tail_inl (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (r₂ : N₂.R) (i : Fin k) (t : S) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).target (Sum.inl (Sigma.mk i t))
      = 0 := rfl

/-- The source complex of the transfer reaction of row `i`. -/
@[simp] theorem compSource_transfer (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i j : Fin k) (t : S) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).source (Sum.inl (Sigma.mk j t))
      = if j = i then (if t = o i then 1 else 0) else 0 := rfl

/-- The source complex of the transfer reaction of row `i`, at a species of the second
part. -/
@[simp] theorem compSource_transfer_inr (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (t : T) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).source (Sum.inr t) = 0 := rfl

/-- The target complex of the transfer reaction of row `i`. -/
@[simp] theorem compTarget_transfer (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (t : T) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).target (Sum.inr t)
      = if t = τ i then 1 else 0 := rfl

/-- The target complex of the transfer reaction of row `i`, at a species of a row. -/
@[simp] theorem compTarget_transfer_inl (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i j : Fin k) (t : S) :
    ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).target (Sum.inl (Sigma.mk j t))
      = 0 := rfl

/-- A step of the first network in row `i` is applicable exactly when the corresponding
step of the network `N₁ i` is applicable in the row. -/
theorem compApplicable_row (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (ri : (N₁ i).R) (c : Config (CompSpecies k S T)) :
    Applicable (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c
      ↔ Applicable (N₁ i) ri (rowOf c i) := by
  constructor
  · intro h t
    have ht := h (Sum.inl (Sigma.mk i t))
    rw [compSource_row] at ht
    rw [ite_eq_left rfl] at ht
    exact ht
  · intro h s
    rcases s with (⟨j, t⟩ | t)
    · rw [compSource_row]
      by_cases hj : j = i
      · rw [ite_eq_left hj, hj]
        exact h t
      · rw [ite_eq_right hj]
        omega
    · rw [compSource_row_inr]
      omega

/-- A step of the second network is applicable exactly when the corresponding step of
`N₂` is applicable in the second part. -/
theorem compApplicable_tail (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (r₂ : N₂.R) (c : Config (CompSpecies k S T)) :
    Applicable (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inl r₂)) c
      ↔ Applicable N₂ r₂ (tailOf c) := by
  constructor
  · intro h t
    have ht := h (Sum.inr t)
    rw [compSource_tail] at ht
    exact ht
  · intro h s
    rcases s with (⟨j, t⟩ | t)
    · rw [compSource_tail_inl]
      omega
    · rw [compSource_tail]
      exact h t

/-- The transfer reaction of row `i` is applicable exactly when the output species
`o i` of the row still holds a molecule. -/
theorem compApplicable_transfer (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (c : Config (CompSpecies k S T)) :
    Applicable (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c
      ↔ 1 ≤ (rowOf c i) (o i) := by
  constructor
  · intro h
    have ht := h (Sum.inl (Sigma.mk i (o i)))
    rw [compSource_transfer] at ht
    rw [ite_eq_left rfl, ite_eq_left rfl] at ht
    exact ht
  · intro h s
    rcases s with (⟨j, t⟩ | t)
    · rw [compSource_transfer]
      by_cases hj : j = i
      · rw [ite_eq_left hj, hj]
        by_cases ht : t = o i
        · rw [ite_eq_left ht, ht]
          exact h
        · rw [ite_eq_right ht]
          omega
      · rw [ite_eq_right hj]
        omega
    · rw [compSource_transfer_inr]
      omega

/-- A step of the first network in row `i` acts on the row `i` only. -/
theorem fire_comp_row (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (ri : (N₁ i).R) (c : Config (CompSpecies k S T)) :
    rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c) i
        = fire (N₁ i) ri (rowOf c i) ∧
    (∀ j, j ≠ i → rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c) j = rowOf c j) ∧
    tailOf (fire (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c) = tailOf c := by
  constructor
  · funext t
    show c (Sum.inl (Sigma.mk i t))
        - ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).source
            (Sum.inl (Sigma.mk i t))
        + ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).target
            (Sum.inl (Sigma.mk i t))
        = (rowOf c i) t - ((N₁ i).reaction ri).source t + ((N₁ i).reaction ri).target t
    rw [compSource_row, ite_eq_left rfl, compTarget_row, ite_eq_left rfl]
    rfl
  · constructor
    · intro j hj
      funext t
      show c (Sum.inl (Sigma.mk j t))
          - ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).source
              (Sum.inl (Sigma.mk j t))
          + ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).target
              (Sum.inl (Sigma.mk j t))
          = (rowOf c j) t
      rw [compSource_row, ite_eq_right hj, compTarget_row, ite_eq_right hj]
      simp only [Nat.sub_zero, Nat.add_zero, rowOf_inl]
    · funext t
      show c (Sum.inr t)
          - ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).source (Sum.inr t)
          + ((compNetwork N₁ o τ N₂).reaction (Sum.inl (Sigma.mk i ri))).target (Sum.inr t)
          = (tailOf c) t
      rw [compSource_row_inr, compTarget_row_inr]
      simp only [Nat.sub_zero, Nat.add_zero, tailOf_inr]


/-- The transfer reaction of row `i` moves one molecule from the output species `o i`
of the row to the input species `τ i` of the second part. -/
theorem fire_comp_transfer (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (i : Fin k) (c : Config (CompSpecies k S T)) :
    rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c) i
        = (fun t => (rowOf c i) t - (if t = o i then 1 else 0)) ∧
    (∀ j, j ≠ i → rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c) j = rowOf c j) ∧
    tailOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c)
        = (fun t => (tailOf c) t + (if t = τ i then 1 else 0)) := by
  constructor
  · funext t
    show c (Sum.inl (Sigma.mk i t))
        - ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).source (Sum.inl (Sigma.mk i t))
        + ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).target (Sum.inl (Sigma.mk i t))
        = (rowOf c i) t - (if t = o i then 1 else 0)
    rw [compSource_transfer, ite_eq_left rfl, compTarget_transfer_inl]
    simp only [Nat.add_zero]
    rfl
  · constructor
    · intro j hj
      funext t
      show c (Sum.inl (Sigma.mk j t))
          - ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).source (Sum.inl (Sigma.mk j t))
          + ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).target (Sum.inl (Sigma.mk j t))
          = (rowOf c j) t
      rw [compSource_transfer, ite_eq_right hj, compTarget_transfer_inl]
      simp only [Nat.sub_zero, Nat.add_zero, rowOf_inl]
    · funext t
      show c (Sum.inr t)
          - ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).source (Sum.inr t)
          + ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inr i))).target (Sum.inr t)
          = (tailOf c) t + (if t = τ i then 1 else 0)
      rw [compSource_transfer_inr, compTarget_transfer]
      simp only [Nat.sub_zero, tailOf_inr]

/-- A step of the second network leaves the rows untouched. -/
theorem fire_comp_tail (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (r₂ : N₂.R) (c : Config (CompSpecies k S T)) :
    (∀ j, rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inl r₂)) c) j = rowOf c j) ∧
    tailOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inl r₂)) c) = fire N₂ r₂ (tailOf c) := by
  constructor
  · intro j
    funext t
    show c (Sum.inl (Sigma.mk j t))
        - ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).source (Sum.inl (Sigma.mk j t))
        + ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).target (Sum.inl (Sigma.mk j t))
        = (rowOf c j) t
    rw [compSource_tail_inl, compTarget_tail_inl]
    simp only [Nat.sub_zero, Nat.add_zero, rowOf_inl]
  · funext t
    show c (Sum.inr t)
        - ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).source (Sum.inr t)
        + ((compNetwork N₁ o τ N₂).reaction (Sum.inr (Sum.inl r₂))).target (Sum.inr t)
        = (fire N₂ r₂ (tailOf c)) t
    rw [compSource_tail, compTarget_tail]
    rfl

/-- Firing a reaction commutes with the shadow, provided the reaction does not consume
the shadow species. -/
theorem fire_shadow {N : Network S} {r : N.R} {c : Config S}
    {t0 : S} {n : ℕ} (ht0 : (N.reaction r).source t0 = 0) :
    fire N r (shadowOf c t0 n) = shadowOf (fire N r c) t0 n := by
  funext s
  show (c s + (if s = t0 then n else 0)) - (N.reaction r).source s + (N.reaction r).target s
      = (c s - (N.reaction r).source s + (N.reaction r).target s) + (if s = t0 then n else 0)
  by_cases hst : s = t0
  · subst hst
    rw [ht0]
    simp only [Nat.sub_zero]
    omega
  · simp only [ite_eq_right hst]
    omega

/-- A reaction that does not consume the shadow species is applicable in the shadow
whenever it is applicable in the configuration. -/
theorem shadow_applicable {N : Network S} {r : N.R} {c : Config S}
    {t0 : S} {n : ℕ} (h : Applicable N r c) (ht0 : (N.reaction r).source t0 = 0) :
    Applicable N r (shadowOf c t0 n) := by
  intro s
  have hs := h s
  show (N.reaction r).source s ≤ c s + (if s = t0 then n else 0)
  by_cases hst : s = t0
  · rw [hst] at hs ⊢
    rw [ht0] at hs
    simp only
    omega
  · rw [ite_eq_right hst, Nat.add_zero]
    exact hs

/-- A reaction that does not consume the shadow species is applicable in the
configuration whenever it is applicable in the shadow. -/
theorem applicable_of_shadow {N : Network S} {r : N.R} {c : Config S}
    {t0 : S} {n : ℕ} (h : Applicable N r (shadowOf c t0 n)) (ht0 : (N.reaction r).source t0 = 0) :
    Applicable N r c := by
  intro s
  have hs := h s
  show (N.reaction r).source s ≤ c s
  by_cases hst : s = t0
  · rw [hst] at hs ⊢
    have hsn : shadowOf c t0 n t0 = c t0 + n := by
      show c t0 + (if t0 = t0 then n else 0) = c t0 + n
      rw [ite_eq_left rfl]
    rw [ht0] at hs
    rw [hsn] at hs
    omega
  · have hsn : (N.reaction r).source s ≤ c s + (if s = t0 then n else 0) := hs
    rw [ite_eq_right hst, Nat.add_zero] at hsn
    exact hsn


/-! ## Collectors: the second network of a composition -/

/-- A network `N` over the species `T` is a **collector** for the input species
`τ : Fin k → T`, with output species `o` and weights `w : Fin k → ℕ`, if

* for every `i` there is exactly one reaction `r` whose source is the unit vector at
  `τ i` (and at no other species),
* every reaction of `N` is of this form,
* the target of that reaction contains `w i` molecules of the output species `o` and
  no molecule of any input species, and
* the output species is not an input species.

A collector is a *linear* device: every molecule that enters at `τ i` is converted into
the target of the `i`-th reaction.  Its output is therefore `∑ i, v i * w i` when it is
fed the input vector `v`. -/
def Collector {k : ℕ} {T : Type} [DecidableEq T] [Fintype T] (τ : Fin k → T) (N : Network T)
    (o : T) (w : Fin k → ℕ) : Prop :=
  (∀ i : Fin k, ∃! r : N.R, (N.reaction r).source = fun t => if t = τ i then 1 else 0) ∧
  (∀ r : N.R, ∃ i : Fin k, (N.reaction r).source = fun t => if t = τ i then 1 else 0) ∧
  (∀ r : N.R, ∀ i : Fin k, (N.reaction r).target (τ i) = 0) ∧
  (∀ i : Fin k, τ i ≠ o) ∧
  (∀ i : Fin k, ∀ r : N.R,
      (N.reaction r).source = (fun t => if t = τ i then 1 else 0) → (N.reaction r).target o = w i)

/-- The input encoding of a collector puts `v i` molecules at the input species `τ i`. -/
def collectorInit {k : ℕ} {T : Type} [DecidableEq T] (τ : Fin k → T) (v : Fin k → ℕ) :
    Config T :=
  fun t => ∑ i, if t = τ i then v i else 0

/-- **The invariant of a collector.**  If a collector is fed the vector `v`, then along
every run there is a vector `n` of "how many input molecules of each species have been
converted", such that `n j + c (τ j) = v j` and the output is `∑ j, n j * w j`. -/
theorem collector_invariant {k : ℕ} {T : Type} [DecidableEq T] [Fintype T]
    {N : Network T} {init₂ : (Fin k → ℕ) → Config T} {τ : Fin k → T} {o₂ : T}
    {w : Fin k → ℕ}
    (hinit₂₁ : ∀ v i, init₂ v (τ i) = v i)
    (hinit₂₂ : ∀ v t, (∀ i, t ≠ τ i) → init₂ v t = 0)
    (hτ : ∀ i j, τ i = τ j → i = j)
    (hcoll : Collector τ N o₂ w)
    {v : Fin k → ℕ} {c : Config T} (hc : Reach N (init₂ v) c) :
    ∃ n : Fin k → ℕ, (∀ j, n j + c (τ j) = v j) ∧ (c o₂ = ∑ j, n j * w j) := by
  have hP : ∀ c' : Config T, Reach N (init₂ v) c' →
      ∃ n : Fin k → ℕ, (∀ j, n j + c' (τ j) = v j) ∧ (c' o₂ = ∑ j, n j * w j) := by
    intro c' hc'
    refine reach_invariant N
      (fun c' => ∃ n : Fin k → ℕ, (∀ j, n j + c' (τ j) = v j) ∧ (c' o₂ = ∑ j, n j * w j))
      ?_ hc' ?_
    · intro c c' hstep hinv
      obtain ⟨r, hr, rfl⟩ := hstep
      obtain ⟨n, hn, hno₂⟩ := hinv
      obtain ⟨i, hi⟩ := hcoll.2.1 r
      have hsrc : (N.reaction r).source = fun t => if t = τ i then 1 else 0 := hi
      have hwt : (N.reaction r).target o₂ = w i := hcoll.2.2.2.2 i r hi
      have hsrcO : (N.reaction r).source o₂ = 0 := by
        rw [hsrc]
        by_cases hne : o₂ = τ i
        · exact absurd hne.symm (hcoll.2.2.2.1 i)
        · simp only [ite_eq_right hne]
      have happτ : 1 ≤ c (τ i) := by
        have h := hr (τ i)
        rw [hsrc] at h
        simp at h
        omega
      refine ⟨fun j => n j + if j = i then 1 else 0, ?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · rw [hj]
          have hsrc' : (N.reaction r).source (τ i) = 1 := by rw [hsrc]; simp
          have htgt' : (N.reaction r).target (τ i) = 0 := hcoll.2.2.1 r i
          have hfire : (fire N r c) (τ i) = c (τ i) - 1 := by
            show c (τ i) - (N.reaction r).source (τ i) + (N.reaction r).target (τ i)
                = c (τ i) - 1
            rw [hsrc', htgt']
            rfl
          rw [hfire]
          have h2 : (fun x => n x + (if x = i then 1 else 0)) i = n i + 1 := by simp
          rw [h2]
          have h1 := hn i
          have h3 := happτ
          omega
        · have hsrc' : (N.reaction r).source (τ j) = 0 := by
            rw [hsrc]
            by_cases hne : τ j = τ i
            · exact absurd hne (fun h => hj (hτ j i h))
            · simp only [ite_eq_right hne]
          have htgt' : (N.reaction r).target (τ j) = 0 := hcoll.2.2.1 r j
          have hfire : (fire N r c) (τ j) = c (τ j) := by
            show c (τ j) - (N.reaction r).source (τ j) + (N.reaction r).target (τ j) = c (τ j)
            rw [hsrc', htgt']
            omega
          rw [hfire]
          have h2 : (fun x => n x + (if x = i then 1 else 0)) j = n j := by simp [hj]
          rw [h2]
          have h1 := hn j
          omega
      · have hfireO : (fire N r c) o₂ = c o₂ + w i := by
          show c o₂ - (N.reaction r).source o₂ + (N.reaction r).target o₂ = c o₂ + w i
          rw [hsrcO, hwt]
          omega
        rw [hfireO, hno₂]
        have hsum : (∑ j, (n j + if j = i then 1 else 0) * w j)
            = (∑ j, n j * w j) + w i := by
          calc (∑ j, (n j + if j = i then 1 else 0) * w j)
              = ∑ j, (n j * w j + (if j = i then 1 else 0) * w j) := by
                  apply Finset.sum_congr rfl
                  intro j _
                  by_cases hj : j = i <;> simp [hj]; ring
            _ = (∑ j, n j * w j) + ∑ j, (if j = i then 1 else 0) * w j := Finset.sum_add_distrib
            _ = (∑ j, n j * w j) + w i := by
                have hkey : ∀ j : Fin k, (if j = i then 1 else 0) * w j
                    = if j = i then w j else 0 := by
                  intro j
                  by_cases hj : j = i <;> simp [hj]
                rw [Finset.sum_congr rfl (fun j _ => hkey j)]
                rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin k)) i w]
                simp
        exact hsum.symm
    · refine ⟨fun _ => 0, ?_, ?_⟩
      · intro j
        rw [hinit₂₁]
        simp
      · rw [hinit₂₂]
        · simp
        · intro i hi
          exact absurd hi.symm (hcoll.2.2.2.1 i)
  exact hP c hc

/-- **The output of a collector.**  A collector that is fed the vector `v` displays
`∑ i, v i * w i` at its output species, whatever run is followed. -/
theorem collector_output {k : ℕ} {T : Type} [DecidableEq T] [Fintype T]
    {N : Network T} {init₂ : (Fin k → ℕ) → Config T} {τ : Fin k → T} {o₂ : T}
    {w : Fin k → ℕ}
    (hinit₂₁ : ∀ v i, init₂ v (τ i) = v i)
    (hinit₂₂ : ∀ v t, (∀ i, t ≠ τ i) → init₂ v t = 0)
    (hτ : ∀ i j, τ i = τ j → i = j)
    (hcoll : Collector τ N o₂ w)
    {v : Fin k → ℕ} {c : Config T} (hc : Reach N (init₂ v) c) (hterm : Terminal N c) :
    c o₂ = ∑ i, v i * w i := by
  obtain ⟨n, hn, hno₂⟩ := collector_invariant hinit₂₁ hinit₂₂ hτ hcoll hc
  have hzero : ∀ j, c (τ j) = 0 := by
    intro j
    obtain ⟨r, hr, huniq⟩ := hcoll.1 j
    have hnotapp : ¬ Applicable N r c := hterm r
    by_contra hcon
    have hpos : 1 ≤ c (τ j) := by omega
    have : Applicable N r c := by
      intro t
      have hsrc : (N.reaction r).source t = (if t = τ j then 1 else 0) := by rw [hr]
      rw [hsrc]
      by_cases ht : t = τ j
      · rw [ht]
        rw [ite_eq_left rfl]
        exact hpos
      · rw [ite_eq_right ht]
        omega
    exact hnotapp this
  have hnv : ∀ j, n j = v j := by
    intro j
    have := hn j
    rw [hzero j] at this
    omega
  have hout : c o₂ = ∑ i, v i * w i := by
    rw [hno₂]
    apply Finset.sum_congr rfl
    intro i _
    rw [hnv i]
  exact hout

/-- **The function computed by a collector.**  A collector that stably computes `f₂`
computes the *linear* function `v ↦ ∑ i, v i * w i`. -/
theorem collector_function {k : ℕ} {T : Type} [DecidableEq T] [Fintype T]
    {N : Network T} {init₂ : (Fin k → ℕ) → Config T} {τ : Fin k → T} {o₂ : T}
    {w : Fin k → ℕ} {f₂ : (Fin k → ℕ) → ℕ}
    (hinit₂₁ : ∀ v i, init₂ v (τ i) = v i)
    (hinit₂₂ : ∀ v t, (∀ i, t ≠ τ i) → init₂ v t = 0)
    (hτ : ∀ i j, τ i = τ j → i = j)
    (hcoll : Collector τ N o₂ w)
    (hcomp : StablyComputes N init₂ o₂ f₂)
    (v : Fin k → ℕ) :
    f₂ v = ∑ i, v i * w i := by
  obtain ⟨c', hc', hstable, hval⟩ := hcomp v (init₂ v) Relation.ReflTransGen.refl
  obtain ⟨n, hn, hno₂⟩ := collector_invariant hinit₂₁ hinit₂₂ hτ hcoll hc'
  have hzero : ∀ j, w j > 0 → c' (τ j) = 0 := by
    intro j hw
    obtain ⟨r, hr, huniq⟩ := hcoll.1 j
    by_contra hcon
    have hpos : 1 ≤ c' (τ j) := by omega
    have happ : Applicable N r c' := by
      intro t
      have hsrc : (N.reaction r).source t = (if t = τ j then 1 else 0) := by rw [hr]
      rw [hsrc]
      by_cases ht : t = τ j
      · rw [ht]
        rw [ite_eq_left rfl]
        exact hpos
      · rw [ite_eq_right ht]
        omega
    have hfire : (fire N r c') o₂ = c' o₂ + w j := by
      show c' o₂ - (N.reaction r).source o₂ + (N.reaction r).target o₂ = c' o₂ + w j
      have hsrcO : (N.reaction r).source o₂ = 0 := by
        rw [hr]
        by_cases hne : o₂ = τ j
        · exact absurd hne.symm (hcoll.2.2.2.1 j)
        · simp only [ite_eq_right hne]
      have hwt : (N.reaction r).target o₂ = w j := hcoll.2.2.2.2 j r hr
      rw [hsrcO, hwt]
      omega
    have hstab := hstable (fire N r c')
      (Relation.ReflTransGen.head ⟨r, happ, rfl⟩ Relation.ReflTransGen.refl)
    rw [hfire] at hstab
    omega
  have hnv : ∀ j, w j > 0 → n j = v j := by
    intro j hw
    have := hn j
    rw [hzero j hw] at this
    omega
  rw [← hval, hno₂]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hw : w j = 0
  · simp [hw]
  · rw [hnv j (by omega)]

/-- The shadow of a row after a transfer: the transferred molecule is restored. -/
theorem shadow_transfer {S : Type} [DecidableEq S] {c : Config S} {t0 : S} {n : ℕ}
    (ht0 : 1 ≤ c t0) :
    shadowOf (fun t => c t - (if t = t0 then 1 else 0)) t0 (n + 1) = shadowOf c t0 n := by
  funext t
  show (c t - (if t = t0 then 1 else 0)) + (if t = t0 then n + 1 else 0)
      = c t + (if t = t0 then n else 0)
  by_cases h : t = t0
  · rw [h, ite_eq_left rfl, ite_eq_left rfl, ite_eq_left rfl]
    show (c t0 - 1) + (n + 1) = c t0 + n
    omega
  · rw [ite_eq_right h, ite_eq_right h, ite_eq_right h]
    show (c t - 0) + 0 = c t + 0
    omega
/-- **The shadow of a composed run.**  If a run of the composed network starts at the
initial configuration, then for each row `i` the *shadow* of the row — the row with the
transferred molecules restored — is reachable in the network `N₁ i`, the number of
transferred molecules `tr i` and the number of conversions `ph i` of the second network
satisfy `tr i = ph i + (tailOf c) (τ i)`, and the output of the second part is
`∑ i, ph i * w i`. -/
theorem comp_shadow {k : ℕ} {α : Type} {S T : Type}
    [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (N₁ : Fin k → Network S) (init₁ : Fin k → α → Config S) (o : Fin k → S) (τ : Fin k → T)
    (N₂ : Network T) (o₂ : T) (w : Fin k → ℕ)
    (hmono₁ : ∀ i r, ((N₁ i).reaction r).source (o i) = 0)
    (hcoll : Collector τ N₂ o₂ w)
    (hτ : ∀ i j, τ i = τ j → i = j)
    (a : α) {c : Config (CompSpecies k S T)}
    (hreach : Reach (compNetwork N₁ o τ N₂) (compInit init₁ a) c) :
    ∃ tr ph : Fin k → ℕ,
      (∀ i, Reach (N₁ i) (init₁ i a) (shadowOf (rowOf c i) (o i) (tr i))) ∧
      (∀ i, tr i = ph i + (tailOf c) (τ i)) ∧
      ((tailOf c) o₂ = ∑ i, ph i * w i) := by
  have hP : ∀ c' : Config (CompSpecies k S T),
      Reach (compNetwork N₁ o τ N₂) (compInit init₁ a) c' →
      ∃ tr ph : Fin k → ℕ,
        (∀ i, Reach (N₁ i) (init₁ i a) (shadowOf (rowOf c' i) (o i) (tr i))) ∧
        (∀ i, tr i = ph i + (tailOf c') (τ i)) ∧
        ((tailOf c') o₂ = ∑ i, ph i * w i) := by
    intro c' hc'
    refine reach_invariant (compNetwork N₁ o τ N₂)
      (fun c' => ∃ tr ph : Fin k → ℕ,
        (∀ i, Reach (N₁ i) (init₁ i a) (shadowOf (rowOf c' i) (o i) (tr i))) ∧
        (∀ i, tr i = ph i + (tailOf c') (τ i)) ∧
        ((tailOf c') o₂ = ∑ i, ph i * w i))
      ?_ hc' ?_
    · intro c c' hstep hinv
      obtain ⟨r, hr, rfl⟩ := hstep
      obtain ⟨tr, ph, hsh, htr, ho₂⟩ := hinv
      cases r with
      | inl sr =>
        rcases sr with ⟨i, ri⟩
        -- a step of the first network in row `i`
        have hrow := fire_comp_row N₁ o τ N₂ i ri c
        have hnew : shadowOf (rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c) i)
              (o i) (tr i) = fire (N₁ i) ri (shadowOf (rowOf c i) (o i) (tr i)) := by
          rw [hrow.1]
          exact (fire_shadow (hmono₁ i ri)).symm
        refine ⟨tr, ph, ?_, ?_, ?_⟩
        · intro j
          by_cases hj : j = i
          · rw [hj]
            have happ : Applicable (N₁ i) ri (shadowOf (rowOf c i) (o i) (tr i)) := by
              refine shadow_applicable ?_ (hmono₁ i ri)
              exact (compApplicable_row N₁ o τ N₂ i ri c).mp hr
            rw [hnew]
            exact Relation.ReflTransGen.tail (hsh i) ⟨ri, happ, rfl⟩
          · have hrowj : rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c) j
                = rowOf c j := hrow.2.1 j hj
            rw [hrowj]
            exact hsh j
        · intro j
          have htail := hrow.2.2
          rw [htail]
          exact htr j
        · have htail := hrow.2.2
          rw [htail]
          exact ho₂
      | inr h₂ =>
        cases h₂ with
        | inl r₂ =>
          -- a step of the second network
          obtain ⟨i, hi⟩ := hcoll.2.1 r₂
          have hsrc : (N₂.reaction r₂).source = fun t => if t = τ i then 1 else 0 := hi
          have hwt : (N₂.reaction r₂).target o₂ = w i := hcoll.2.2.2.2 i r₂ hi
          have htail := fire_comp_tail N₁ o τ N₂ r₂ c
          refine ⟨tr, fun j => ph j + if j = i then 1 else 0, ?_, ?_, ?_⟩
          · intro j
            have hrowj : rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inl r₂)) c) j = rowOf c j :=
              htail.1 j
            rw [hrowj]
            exact hsh j
          · intro j
            by_cases hj : j = i
            · rw [hj]
              have hsrc' : (N₂.reaction r₂).source (τ i) = 1 := by rw [hsrc]; simp
              have htgt' : (N₂.reaction r₂).target (τ i) = 0 := hcoll.2.2.1 r₂ i
              have hfire : (fire N₂ r₂ (tailOf c)) (τ i) = (tailOf c) (τ i) - 1 := by
                show (tailOf c) (τ i) - (N₂.reaction r₂).source (τ i)
                    + (N₂.reaction r₂).target (τ i) = (tailOf c) (τ i) - 1
                rw [hsrc', htgt']
                rfl
              have hpos : 1 ≤ (tailOf c) (τ i) := by
                have h := hr (Sum.inr (τ i))
                rw [compSource_tail] at h
                rw [hsrc] at h
                simp at h
                show 1 ≤ c (Sum.inr (τ i))
                omega
              have h1 := htr i
              have h2 : (fun j => ph j + (if j = i then 1 else 0)) i = ph i + 1 := by simp
              rw [h2, htail.2, hfire]
              omega
            · have hsrc' : (N₂.reaction r₂).source (τ j) = 0 := by
                rw [hsrc]
                by_cases hne : τ j = τ i
                · exact absurd hne (fun h => hj (hτ j i h))
                · simp only [ite_eq_right hne]
              have htgt' : (N₂.reaction r₂).target (τ j) = 0 := hcoll.2.2.1 r₂ j
              have hfire : (fire N₂ r₂ (tailOf c)) (τ j) = (tailOf c) (τ j) := by
                show (tailOf c) (τ j) - (N₂.reaction r₂).source (τ j)
                    + (N₂.reaction r₂).target (τ j) = (tailOf c) (τ j)
                rw [hsrc', htgt']
                omega
              have h1 := htr j
              have h2 : (fun j => ph j + (if j = i then 1 else 0)) j = ph j := by simp [hj]
              rw [h2, htail.2, hfire]
              omega
          · have hsrcO : (N₂.reaction r₂).source o₂ = 0 := by
              rw [hsrc]
              by_cases hne : o₂ = τ i
              · exact absurd hne.symm (hcoll.2.2.2.1 i)
              · simp only [ite_eq_right hne]
            have hfireO : (fire N₂ r₂ (tailOf c)) o₂ = (tailOf c) o₂ + w i := by
              show (tailOf c) o₂ - (N₂.reaction r₂).source o₂ + (N₂.reaction r₂).target o₂
                  = (tailOf c) o₂ + w i
              rw [hsrcO, hwt]
              omega
            rw [htail.2, hfireO, ho₂]
            have hsum : (∑ j, (ph j + if j = i then 1 else 0) * w j)
                = (∑ j, ph j * w j) + w i := by
              calc (∑ j, (ph j + if j = i then 1 else 0) * w j)
                  = ∑ j, (ph j * w j + (if j = i then 1 else 0) * w j) := by
                      apply Finset.sum_congr rfl
                      intro j _
                      by_cases hj : j = i <;> simp [hj]; ring
                _ = (∑ j, ph j * w j) + ∑ j, (if j = i then 1 else 0) * w j := Finset.sum_add_distrib
                _ = (∑ j, ph j * w j) + w i := by
                    have hkey : ∀ j : Fin k, (if j = i then 1 else 0) * w j
                        = if j = i then w j else 0 := by
                      intro j
                      by_cases hj : j = i <;> simp [hj]
                    rw [Finset.sum_congr rfl (fun j _ => hkey j)]
                    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin k)) i w]
                    simp
            exact hsum.symm
        | inr i =>
          -- the transfer reaction of row `i`
          have hrow := fire_comp_transfer N₁ o τ N₂ i c
          refine ⟨fun j => tr j + if j = i then 1 else 0, ph, ?_, ?_, ?_⟩
          · intro j
            by_cases hj : j = i
            · rw [hj]
              have hnew : shadowOf (rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c) i)
                    (o i) (tr i + 1) = shadowOf (rowOf c i) (o i) (tr i) := by
                rw [hrow.1]
                have hpos : 1 ≤ (rowOf c i) (o i) := by
                  exact (compApplicable_transfer N₁ o τ N₂ i c).mp hr
                exact shadow_transfer hpos
              have h2 : (fun j => tr j + (if j = i then 1 else 0)) i = tr i + 1 := by simp
              rw [h2, hnew]
              exact hsh i
            · have hrowj : rowOf (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c) j = rowOf c j :=
                hrow.2.1 j hj
              rw [hrowj]
              have h2 : (fun j => tr j + (if j = i then 1 else 0)) j = tr j := by simp [hj]
              rw [h2]
              exact hsh j
          · intro j
            by_cases hj : j = i
            · rw [hj]
              have h2 : (fun j => tr j + (if j = i then 1 else 0)) i = tr i + 1 := by simp
              rw [h2]
              have h1 : tr i = ph i + c (Sum.inr (τ i)) := by rw [htr i]; rfl
              rw [hrow.2.2]
              show tr i + 1 = ph i + (c (Sum.inr (τ i)) + (if τ i = τ i then 1 else 0))
              rw [ite_eq_left rfl]
              omega
            · have h2 : (fun j => tr j + (if j = i then 1 else 0)) j = tr j := by simp [hj]
              rw [h2]
              have h1 : tr j = ph j + c (Sum.inr (τ j)) := by rw [htr j]; rfl
              have hne : τ j ≠ τ i := fun h => hj (hτ j i h)
              rw [hrow.2.2]
              show tr j = ph j + (c (Sum.inr (τ j)) + (if τ j = τ i then 1 else 0))
              rw [ite_eq_right hne]
              omega
          · have htail := hrow.2.2
            rw [htail]
            have hne : o₂ ≠ τ i := (hcoll.2.2.2.1 i).symm
            simp [hne]
            exact ho₂
    · refine ⟨fun _ => 0, fun _ => 0, ?_, ?_, ?_⟩
      · intro i
        have hsh0 : shadowOf (rowOf (compInit init₁ a : Config (CompSpecies k S T)) i) (o i) 0
            = init₁ i a := by
          funext t
          show (compInit init₁ a) (Sum.inl (Sigma.mk i t)) + (if t = o i then 0 else 0)
              = init₁ i a t
          rw [compInit_inl]
          simp
        rw [hsh0]
        exact Relation.ReflTransGen.refl
      · intro i
        show (0 : ℕ) = 0 + (compInit init₁ a) (Sum.inr (τ i))
        rw [compInit_inr]
      · show (compInit init₁ a) (Sum.inr o₂) = ∑ i, (0 : ℕ) * w i
        rw [compInit_inr]
        simp
  exact hP c hreach

/-! ## The potential of the composed network -/

/-- The weighted sum of a configuration with a nonnegative weight. -/
theorem configSum_nat {S : Type} [DecidableEq S] [Fintype S] (w : S → ℕ) (c : Config S) :
    configSum (fun s => (w s : ℤ)) c = ((∑ s, w s * c s) : ℤ) := by
  simp [configSum, wsum]

/-- A reaction that decreases the weighted sum decreases it strictly. -/
theorem weightedSum_fire {S : Type} [DecidableEq S] [Fintype S] {N : Network S}
    (w : S → ℕ) (r : N.R) (c : Config S) (h : Applicable N r c)
    (hw : wsum (fun s => (w s : ℤ)) (delta N r) ≤ -1) :
    (∑ s, w s * (fire N r c) s) < ∑ s, w s * c s := by
  have hdec := configSum_fire N (fun s => (w s : ℤ)) r c h
  have h3 : (∑ s, (w s : ℤ) * (fire N r c) s)
      = (∑ s, (w s : ℤ) * c s) + wsum (fun s => (w s : ℤ)) (delta N r) := by
    calc (∑ s, (w s : ℤ) * (fire N r c) s) = configSum (fun s => (w s : ℤ)) (fire N r c) := rfl
      _ = configSum (fun s => (w s : ℤ)) c + wsum (fun s => (w s : ℤ)) (delta N r) := hdec
      _ = (∑ s, (w s : ℤ) * c s) + wsum (fun s => (w s : ℤ)) (delta N r) := rfl
  have hlt : (∑ s, (w s : ℤ) * (fire N r c) s) < (∑ s, (w s : ℤ) * c s) := by omega
  have hlt' : ((∑ s, w s * (fire N r c) s : ℕ) : ℤ) < ((∑ s, w s * c s : ℕ) : ℤ) := by
    simpa only [Nat.cast_sum, Nat.cast_mul] using hlt
  exact Int.ofNat_lt.mp hlt'

/-- If the summand changes only at `i`, the sum changes by the change at `i`. -/
theorem sum_sub_single {ι : Type} [Fintype ι] [DecidableEq ι] {M : Type} [AddCommGroup M]
    [PartialOrder M]
    (f g : ι → M) (i : ι) (h : ∀ j, j ≠ i → f j = g j) :
    (∑ j, f j) - (∑ j, g j) = f i - g i := by
  rw [← Finset.sum_sub_distrib]
  have key : ∀ j, f j - g j = if j = i then (f i - g i) else 0 := by
    intro j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [h j hj]
      rw [ite_eq_right hj]
      simp
  rw [Finset.sum_congr rfl (fun j _ => key j)]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset ι) i (fun _ => f i - g i)]
  simp

/-- The weighted sum of a configuration, in explicit form. -/
theorem configSum_eq_sumZ {S : Type} [DecidableEq S] [Fintype S] (w : S → ℕ) (c : Config S) :
    configSum (fun s => (w s : ℤ)) c = ∑ s, (w s : ℤ) * (c s : ℤ) := rfl

/-- The weighted sum of a configuration, as an integer. -/
theorem weightedSumZ {S : Type} [DecidableEq S] [Fintype S] (w : S → ℕ) (c : Config S) :
    (∑ s, (w s : ℤ) * (c s : ℤ)) = ((∑ s, w s * c s : ℕ) : ℤ) := by
  simp [Nat.cast_sum, Nat.cast_mul]

/-- The weighted sum of a configuration from which one molecule at `t0` was removed. -/
theorem weightedSum_removeZ {S : Type} [DecidableEq S] [Fintype S] (w : S → ℕ) (c : Config S)
    (t0 : S) (h : 1 ≤ c t0) :
    (∑ s, (w s : ℤ) * (fun t => c t - (if t = t0 then 1 else 0)) s)
      = (∑ s, (w s : ℤ) * c s) - (w t0 : ℤ) := by
  have key : ∀ s : S, (w s : ℤ) * (fun t => c t - (if t = t0 then 1 else 0)) s
      = (w s : ℤ) * c s - (if s = t0 then (w s : ℤ) else 0) := by
    intro s
    by_cases hs : s = t0
    · rw [hs]
      simp only [ite_true]
      have hcast : ((c t0 - 1 : ℕ) : ℤ) = (c t0 : ℤ) - 1 := by
        rw [Nat.cast_sub h]
        simp
      rw [hcast, Int.mul_sub]
      ring
    · simp only [ite_eq_right hs]
      have hcast : ((c s - 0 : ℕ) : ℤ) = (c s : ℤ) - 0 := by
        rw [Nat.cast_sub (Nat.zero_le _)]
        simp
      rw [hcast, Int.mul_sub]
      ring
  calc (∑ s, (w s : ℤ) * (fun t => c t - (if t = t0 then 1 else 0)) s)
      = ∑ s, ((w s : ℤ) * c s - (if s = t0 then (w s : ℤ) else 0)) :=
        Finset.sum_congr rfl fun s _ => key s
    _ = (∑ s, (w s : ℤ) * c s) - ∑ s, (if s = t0 then (w s : ℤ) else 0) := by
        rw [← Finset.sum_sub_distrib]
    _ = (∑ s, (w s : ℤ) * c s) - (w t0 : ℤ) := by
        rw [Finset.sum_ite_eq' (Finset.univ : Finset S) t0 (fun s => (w s : ℤ))]
        simp

/-- The weighted sum of a configuration to which one molecule at `t0` was added. -/
theorem weightedSum_addZ {S : Type} [DecidableEq S] [Fintype S] (w : S → ℕ) (c : Config S)
    (t0 : S) :
    (∑ s, (w s : ℤ) * (fun t => c t + (if t = t0 then 1 else 0)) s)
      = (∑ s, (w s : ℤ) * c s) + (w t0 : ℤ) := by
  have key : ∀ s : S, (w s : ℤ) * (fun t => c t + (if t = t0 then 1 else 0)) s
      = (w s : ℤ) * c s + (if s = t0 then (w s : ℤ) else 0) := by
    intro s
    by_cases hs : s = t0
    · rw [hs]
      simp only [ite_true]
      have hcast : ((c t0 + 1 : ℕ) : ℤ) = (c t0 : ℤ) + 1 := by
        rw [Nat.cast_add]
        simp
      rw [hcast, Int.mul_add]
      ring
    · simp only [ite_eq_right hs]
      have hcast : ((c s + 0 : ℕ) : ℤ) = (c s : ℤ) + 0 := by
        rw [Nat.cast_add]
        simp
      rw [hcast, Int.mul_add]
      ring
  calc (∑ s, (w s : ℤ) * (fun t => c t + (if t = t0 then 1 else 0)) s)
      = ∑ s, ((w s : ℤ) * c s + (if s = t0 then (w s : ℤ) else 0)) :=
        Finset.sum_congr rfl fun s _ => key s
    _ = (∑ s, (w s : ℤ) * c s) + ∑ s, (if s = t0 then (w s : ℤ) else 0) := Finset.sum_add_distrib
    _ = (∑ s, (w s : ℤ) * c s) + (w t0 : ℤ) := by
        rw [Finset.sum_ite_eq' (Finset.univ : Finset S) t0 (fun s => (w s : ℤ))]
        simp

/-- **The potential of the composed network.** -/
def compPotential {k : ℕ} {S T : Type} [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (w₁ : Fin k → S → ℕ) (w₂ : T → ℕ) (A : ℕ)
    (c : Config (CompSpecies k S T)) : ℕ :=
  A * (∑ i, ∑ s, w₁ i s * (rowOf c i) s) + (∑ t, w₂ t * (tailOf c) t)

/-- **The potential of the composed network**, as an integer. -/
def compPotentialZ {k : ℕ} {S T : Type} [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (w₁ : Fin k → S → ℕ) (w₂ : T → ℕ) (A : ℕ)
    (c : Config (CompSpecies k S T)) : ℤ :=
  (A : ℤ) * (∑ i, ∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ))
    + (∑ t, (w₂ t : ℤ) * ((tailOf c) t : ℤ))

/-- The integer potential is the cast of the natural-number potential. -/
theorem compPotentialZ_eq {k : ℕ} {S T : Type} [DecidableEq S] [Fintype S] [DecidableEq T]
    [Fintype T] (w₁ : Fin k → S → ℕ) (w₂ : T → ℕ) (A : ℕ)
    (c : Config (CompSpecies k S T)) :
    compPotentialZ w₁ w₂ A c = (compPotential w₁ w₂ A c : ℤ) := by
  simp only [compPotentialZ, compPotential, Nat.cast_mul, Nat.cast_sum]
  have h1 : (∑ i, ∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ))
      = ∑ i, ((∑ s, w₁ i s * (rowOf c i) s : ℕ) : ℤ) :=
    Finset.sum_congr rfl fun i _ => (weightedSumZ (w₁ i) (rowOf c i))
  have h2 : (∑ t, (w₂ t : ℤ) * ((tailOf c) t : ℤ)) = ((∑ t, w₂ t * (tailOf c) t : ℕ) : ℤ) :=
    (weightedSumZ w₂ (tailOf c))
  rw [h1, h2]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum]

/-- A step of the first network in row `i` decreases the potential of the composed
network. -/
theorem compPotential_row_step {k : ℕ} {S T : Type}
    [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T) (N₂ : Network T)
    (w₁ : Fin k → S → ℕ) (w₂ : T → ℕ) (A : ℕ)
    (i : Fin k) (ri : (N₁ i).R) (c : Config (CompSpecies k S T))
    (hr : Applicable (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c)
    (hw₁δ : ∀ j r, wsum (fun s => (w₁ j s : ℤ)) (delta (N₁ j) r) ≤ -1)
    (hApos : (0 : ℤ) < (A : ℤ)) :
    compPotentialZ w₁ w₂ A (fire (compNetwork N₁ o τ N₂) (Sum.inl (Sigma.mk i ri)) c)
      < compPotentialZ w₁ w₂ A c := by
  have hrow := fire_comp_row N₁ o τ N₂ i ri c
  have hdec := configSum_fire (N₁ i) (fun s => (w₁ i s : ℤ)) ri (rowOf c i)
    ((compApplicable_row N₁ o τ N₂ i ri c).mp hr)
  rw [← hrow.1] at hdec
  rw [configSum_eq_sumZ, configSum_eq_sumZ] at hdec
  have hlt : (∑ s, (w₁ i s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inl (Sigma.mk i ri)) c) i) s : ℤ))
      < ∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ) := by
    linarith [hdec, hw₁δ i ri]
  have hle : ∀ j, j ≠ i →
      (∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inl (Sigma.mk i ri)) c) j) s : ℤ))
      = ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ) := by
    intro j hj
    rw [hrow.2.1 j hj]
  have hdiff : (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inl (Sigma.mk i ri)) c) j) s : ℤ))
      - (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ))
      = (∑ s, (w₁ i s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inl (Sigma.mk i ri)) c) i) s : ℤ))
      - (∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ)) := by
    refine sum_sub_single _ _ i ?_
    intro j hj
    rw [hle j hj]
  simp only [compPotentialZ]
  rw [hrow.2.2]
  have hmul : (A : ℤ) * (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inl (Sigma.mk i ri)) c) j) s : ℤ))
      < (A : ℤ) * (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ)) := by
    have h1 : (∑ s, (w₁ i s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
          (Sum.inl (Sigma.mk i ri)) c) i) s : ℤ))
        < (∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ)) := hlt
    have hlt' : (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
          (Sum.inl (Sigma.mk i ri)) c) j) s : ℤ))
        < (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ)) := by
      have h1 : (∑ s, (w₁ i s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
            (Sum.inl (Sigma.mk i ri)) c) i) s : ℤ))
          < (∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ)) := hlt
      omega
    exact mul_lt_mul_of_pos_left hlt' hApos
  omega

/-- A step of the second network decreases the potential of the composed network. -/
theorem compPotential_tail_step {k : ℕ} {S T : Type}
    [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T) (N₂ : Network T)
    (w₁ : Fin k → S → ℕ) (w₂ : T → ℕ) (A : ℕ)
    (r₂ : N₂.R) (c : Config (CompSpecies k S T))
    (hr : Applicable (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inl r₂)) c)
    (hw₂δ : ∀ r, wsum (fun t => (w₂ t : ℤ)) (delta N₂ r) ≤ -1) :
    compPotentialZ w₁ w₂ A (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inl r₂)) c)
      < compPotentialZ w₁ w₂ A c := by
  have htail := fire_comp_tail N₁ o τ N₂ r₂ c
  have hdec := configSum_fire N₂ (fun t => (w₂ t : ℤ)) r₂ (tailOf c)
    ((compApplicable_tail N₁ o τ N₂ r₂ c).mp hr)
  rw [← htail.2] at hdec
  rw [configSum_eq_sumZ, configSum_eq_sumZ] at hdec
  have hlt : (∑ t, (w₂ t : ℤ) * ((tailOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inl r₂)) c) t) : ℤ))
      < ∑ t, (w₂ t : ℤ) * ((tailOf c) t : ℤ) := by
    linarith [hdec, hw₂δ r₂]
  have hrow : ∀ j, (∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inl r₂)) c) j) s : ℤ))
      = ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ) := by
    intro j
    rw [htail.1 j]
  simp only [compPotentialZ]
  rw [Finset.sum_congr rfl (fun j _ => hrow j)]
  omega

/-- The transfer reaction of row `i` decreases the potential of the composed network. -/
theorem compPotential_transfer_step {k : ℕ} {S T : Type}
    [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (N₁ : Fin k → Network S) (o : Fin k → S) (τ : Fin k → T) (N₂ : Network T)
    (w₁ : Fin k → S → ℕ) (w₂ : T → ℕ) (A : ℕ)
    (i : Fin k) (c : Config (CompSpecies k S T))
    (hr : Applicable (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c)
    (hw₁ : ∀ j, 1 ≤ w₁ j (o j))
    (hAv : (A : ℤ) > (w₂ (τ i) : ℤ)) :
    compPotentialZ w₁ w₂ A (fire (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c)
      < compPotentialZ w₁ w₂ A c := by
  have hrow := fire_comp_transfer N₁ o τ N₂ i c
  have hpos : 1 ≤ (rowOf c i) (o i) := by
    exact (compApplicable_transfer N₁ o τ N₂ i c).mp hr
  have hrem := weightedSum_removeZ (w₁ i) (rowOf c i) (o i) hpos
  rw [← hrow.1] at hrem
  have hrem' : (∑ s, (w₁ i s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inr i)) c) i) s : ℤ))
      = ∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ) - (w₁ i (o i) : ℤ) := by
    rw [← hrem]
  have hrowle : ∀ j, j ≠ i →
      (∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inr i)) c) j) s : ℤ))
      = ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ) := by
    intro j hj
    rw [hrow.2.1 j hj]
  have hadd := weightedSum_addZ w₂ (tailOf c) (τ i)
  have hadd' : (∑ t, (w₂ t : ℤ) * ((tailOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inr i)) c) t) : ℤ))
      = ∑ t, (w₂ t : ℤ) * ((tailOf c) t : ℤ) + (w₂ (τ i) : ℤ) := by
    have key : ∀ t, (w₂ t : ℤ) * (fun s => (tailOf c) s + (if s = τ i then 1 else 0)) t
        = (w₂ t : ℤ) * (tailOf c) t + (if t = τ i then (w₂ t : ℤ) else 0) := by
      intro t
      by_cases ht : t = τ i
      · rw [ht]
        simp only [ite_true]
        have hcast : ((tailOf c (τ i) + 1 : ℕ) : ℤ) = (tailOf c (τ i) : ℤ) + 1 := by
          rw [Nat.cast_add]
          simp
        rw [hcast, Int.mul_add]
        ring
      · simp only [ite_eq_right ht]
        have hcast : ((tailOf c t + 0 : ℕ) : ℤ) = (tailOf c t : ℤ) + 0 := by
          rw [Nat.cast_add]
          simp
        rw [hcast, Int.mul_add]
        ring
    calc (∑ t, (w₂ t : ℤ) * ((tailOf (fire (compNetwork N₁ o τ N₂)
          (Sum.inr (Sum.inr i)) c) t) : ℤ))
        = ∑ t, (w₂ t : ℤ) * ((fun s => (tailOf c) s + (if s = τ i then 1 else 0)) t : ℤ) := by
          rw [hrow.2.2]
      _ = ∑ t, ((w₂ t : ℤ) * (tailOf c) t + (if t = τ i then (w₂ t : ℤ) else 0)) :=
          Finset.sum_congr rfl fun t _ => key t
      _ = (∑ t, (w₂ t : ℤ) * (tailOf c) t) + ∑ t, (if t = τ i then (w₂ t : ℤ) else 0) := by
          rw [Finset.sum_add_distrib]
      _ = (∑ t, (w₂ t : ℤ) * (tailOf c) t) + (w₂ (τ i) : ℤ) := by
          rw [Finset.sum_ite_eq' (Finset.univ : Finset T) (τ i) (fun t => (w₂ t : ℤ))]
          simp
  simp only [compPotentialZ]
  have hdiff : (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inr i)) c) j) s : ℤ))
      - (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ))
      = (∑ s, (w₁ i s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inr i)) c) i) s : ℤ))
      - (∑ s, (w₁ i s : ℤ) * ((rowOf c i) s : ℤ)) := by
    refine sum_sub_single _ _ i ?_
    intro j hj
    rw [hrowle j hj]
  have hroweq : (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf (fire (compNetwork N₁ o τ N₂)
        (Sum.inr (Sum.inr i)) c) j) s : ℤ))
      = (∑ j, ∑ s, (w₁ j s : ℤ) * ((rowOf c j) s : ℤ)) - (w₁ i (o i) : ℤ) := by
    have h1 := hdiff
    rw [hrem'] at h1
    omega
  rw [hroweq, hadd']
  rw [Int.mul_sub]
  have hmul : (A : ℤ) * (w₁ i (o i) : ℤ) ≥ (A : ℤ) := by
    have h1 : (1 : ℤ) ≤ (w₁ i (o i) : ℤ) := by exact_mod_cast hw₁ i
    have h2 : (0 : ℤ) ≤ (A : ℤ) := by positivity
    have h3 := Int.mul_le_mul_of_nonneg_left h1 h2
    simpa using h3
  omega

/-- **Composition of stable computations.**

If the rows `i` of the composed network run the networks `N₁ i`, which stably compute the
functions `f₁ i` at the output species `o i`, and the second network `N₂` is a *collector*
for the input species `τ i` (a network that converts every molecule entering at `τ i`
into a fixed target), then the composed network — the rows running in parallel and the
second network collecting what they produce — stably computes the function
`a ↦ f₂ (fun i => f₁ i a)`. -/
theorem stablyComputes_comp {k : ℕ} {α : Type} {S T : Type}
    [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
    (N₁ : Fin k → Network S) (init₁ : Fin k → α → Config S) (o : Fin k → S)
    (f₁ : Fin k → α → ℕ)
    (hmono₁ : ∀ i r, ((N₁ i).reaction r).source (o i) = 0)
    (w₁ : Fin k → S → ℕ) (hw₁ : ∀ i, 1 ≤ w₁ i (o i))
    (hw₁δ : ∀ i r, wsum (fun s => (w₁ i s : ℤ)) (delta (N₁ i) r) ≤ -1)
    (hout₁ : ∀ i a c, Reach (N₁ i) (init₁ i a) c → Terminal (N₁ i) c → c (o i) = f₁ i a)
    (N₂ : Network T) (init₂ : (Fin k → ℕ) → Config T) (τ : Fin k → T) (o₂ : T)
    (f₂ : (Fin k → ℕ) → ℕ)
    (hinit₂₁ : ∀ v i, init₂ v (τ i) = v i)
    (hinit₂₂ : ∀ v t, (∀ i, t ≠ τ i) → init₂ v t = 0)
    (hτ : ∀ i j, τ i = τ j → i = j)
    (w : Fin k → ℕ) (hcoll : Collector τ N₂ o₂ w)
    (w₂ : T → ℕ) (hw₂δ : ∀ r, wsum (fun t => (w₂ t : ℤ)) (delta N₂ r) ≤ -1)
    (h₂ : StablyComputes N₂ init₂ o₂ f₂) :
    StablyComputes (compNetwork N₁ o τ N₂) (fun a => compInit init₁ a) (Sum.inr o₂)
      (fun a => f₂ (fun i => f₁ i a)) := by
  let A : ℕ := (∑ i, w₂ (τ i)) + 1
  have hA : ∀ i, w₂ (τ i) < A := by
    intro i
    have h1 : w₂ (τ i) ≤ ∑ j, w₂ (τ j) := by
      calc w₂ (τ i) = ∑ j, (if j = i then w₂ (τ j) else 0) := by
            rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin k)) i (fun j => w₂ (τ j))]
            simp
        _ ≤ ∑ j, w₂ (τ j) := Finset.sum_le_sum fun j _ => by
            by_cases hj : j = i <;> simp [hj]
    dsimp [A]
    omega
  have hApos : (0 : ℤ) < (A : ℤ) := by
    dsimp [A]
    omega
  refine stablyComputes_of_terminating _ _ _ _ (compPotential w₁ w₂ A) ?_ ?_
  · -- the potential decreases at every step
    intro c c' hstep
    obtain ⟨r, hr, hcf⟩ := hstep
    have hΦ : compPotentialZ w₁ w₂ A c' < compPotentialZ w₁ w₂ A c := by
      rw [hcf]
      cases r with
      | inl sr =>
        rcases sr with ⟨i, ri⟩
        exact compPotential_row_step N₁ o τ N₂ w₁ w₂ A i ri c hr hw₁δ hApos
      | inr h₂ =>
        cases h₂ with
        | inl r₂ =>
          exact compPotential_tail_step N₁ o τ N₂ w₁ w₂ A r₂ c hr hw₂δ
        | inr i =>
          exact compPotential_transfer_step N₁ o τ N₂ w₁ w₂ A i c hr hw₁
            (by exact_mod_cast hA i)
    have hΦ' : (compPotential w₁ w₂ A c' : ℤ) < (compPotential w₁ w₂ A c : ℤ) := by
      rw [← compPotentialZ_eq, ← compPotentialZ_eq]
      exact hΦ
    exact Int.ofNat_lt.mp hΦ'
  · -- the correctness at a terminal configuration
    intro a c hc hterm
    obtain ⟨tr, ph, hsh, htr, ho₂⟩ :=
      comp_shadow N₁ init₁ o τ N₂ o₂ w hmono₁ hcoll hτ a hc
    have hterm₁ : ∀ i, Terminal (N₁ i) (shadowOf (rowOf c i) (o i) (tr i)) := by
      intro i r
      intro happ
      have hnotapp : ¬ Applicable (N₁ i) r (rowOf c i) := by
        intro h2
        exact hterm (Sum.inl (Sigma.mk i r)) ((compApplicable_row N₁ o τ N₂ i r c).mpr h2)
      exact hnotapp (applicable_of_shadow happ (hmono₁ i r))
    have hval : ∀ i, (rowOf c i) (o i) + tr i = f₁ i a := by
      intro i
      have h1 := hout₁ i a (shadowOf (rowOf c i) (o i) (tr i)) (hsh i) (hterm₁ i)
      have h2 : shadowOf (rowOf c i) (o i) (tr i) (o i) = (rowOf c i) (o i) + tr i := by
        show (rowOf c i) (o i) + (if o i = o i then tr i else 0) = (rowOf c i) (o i) + tr i
        simp
      rw [h2] at h1
      exact h1
    have hz : ∀ i, (rowOf c i) (o i) = 0 := by
      intro i
      have hnotapp : ¬ Applicable (compNetwork N₁ o τ N₂) (Sum.inr (Sum.inr i)) c :=
        hterm (Sum.inr (Sum.inr i))
      rw [compApplicable_transfer] at hnotapp
      omega
    have htrv : ∀ i, tr i = f₁ i a := by
      intro i
      have h1 := hval i
      have h2 := hz i
      omega
    have hz2 : ∀ i, (tailOf c) (τ i) = 0 := by
      intro i
      obtain ⟨r₂, hr₂, huniq⟩ := hcoll.1 i
      have hnotapp : ¬ Applicable N₂ r₂ (tailOf c) := by
        intro happ
        exact hterm (Sum.inr (Sum.inl r₂)) ((compApplicable_tail N₁ o τ N₂ r₂ c).mpr happ)
      have hsrc : (N₂.reaction r₂).source = fun t => if t = τ i then 1 else 0 := hr₂
      by_contra hcon
      have hpos : 1 ≤ (tailOf c) (τ i) := by omega
      apply hnotapp
      intro t
      have hsrc' : (N₂.reaction r₂).source t = (if t = τ i then 1 else 0) := by rw [hsrc]
      rw [hsrc']
      by_cases ht : t = τ i
      · rw [ht]
        simp only
        exact hpos
      · rw [ite_eq_right ht]
        omega
    have hphv : ∀ i, ph i = f₁ i a := by
      intro i
      have h1 := htr i
      rw [hz2 i] at h1
      have h2 := htrv i
      omega
    show (tailOf c) o₂ = f₂ (fun i => f₁ i a)
    rw [ho₂]
    have hlin : f₂ (fun i => f₁ i a) = ∑ i, f₁ i a * w i :=
      collector_function hinit₂₁ hinit₂₂ hτ hcoll h₂ (fun i => f₁ i a)
    rw [hlin]
    apply Finset.sum_congr rfl
    intro i _
    rw [hphv i]

#print axioms CRNT.Computation.stablyComputes_comp
#print axioms CRNT.Computation.comp_shadow
#print axioms CRNT.Computation.collector_function
#print axioms CRNT.Computation.compPotential_row_step

/-! ## An instance: the sum of two minima of affine maps -/

namespace MinAffine

variable {d k : ℕ}

/-- The nonnegative potential weight of the min-of-affine network. -/
def weight (ps : Fin (k+1) → Affine d) : Species d k → ℕ := fun s =>
  match s with
  | Sum.inl i => 1 + ∑ l, (ps l).coeff i
  | Sum.inr _ => 1

/-- The weight is the potential weight of the repository, cast to a natural number. -/
theorem weight_eq (ps : Fin (k+1) → Affine d) (s : Species d k) :
    (weight ps s : ℤ) = potentialWeight ps s := by
  cases s with
  | inl i => simp [weight, potentialWeight]
  | inr sr =>
    cases sr with
    | inl r => simp [weight, potentialWeight]
    | inr r => simp [weight, potentialWeight]

/-- The weight decreases by one at every reaction of the min-of-affine network. -/
theorem weight_delta (ps : Fin (k+1) → Affine d) (r : (minAffineCRN ps).R) :
    wsum (fun s => (weight ps s : ℤ)) (delta (minAffineCRN ps) r) = -1 := by
  cases r with
  | inl i =>
    have h := potentialWeight_delta_conv ps i
    have h2 : wsum (fun s => (weight ps s : ℤ)) (delta (minAffineCRN ps) (Sum.inl i))
        = wsum (potentialWeight ps) (delta (minAffineCRN ps) (Sum.inl i)) := by
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact weight_eq ps s
    rw [h2]
    exact h
  | inr j =>
    have h := potentialWeight_delta_chain ps j
    have h2 : wsum (fun s => (weight ps s : ℤ)) (delta (minAffineCRN ps) (Sum.inr j))
        = wsum (potentialWeight ps) (delta (minAffineCRN ps) (Sum.inr j)) := by
      apply Finset.sum_congr rfl
      intro s _
      congr 1
      exact weight_eq ps s
    rw [h2]
    exact h

/-- The min-of-affine network never consumes its output species. -/
theorem output_not_consumed (ps : Fin (k+1) → Affine d) (r : (minAffineCRN ps).R) :
    ((minAffineCRN ps).reaction r).source (minAffineOut k) = 0 := by
  cases r with
  | inl i => simp [finNetwork, minAffineOut, convSource]
  | inr j =>
    simp only [chainSource, minAffineOut]
    split
    · rename_i h
      have h2 := Fin.ext_iff.mp h
      have hj : (j : ℕ) < k := j.isLt
      simp only [Fin.val_castSucc] at h2
      omega
    · rfl

end MinAffine

#print axioms CRNT.Computation.stablyComputes_comp
#print axioms CRNT.Computation.comp_shadow
#print axioms CRNT.Computation.collector_function
#print axioms CRNT.Computation.compPotential_row_step
