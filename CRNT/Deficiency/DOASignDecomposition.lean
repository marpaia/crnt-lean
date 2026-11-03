import CRNT.Multistationarity.MultiShelfConverse
import CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness

/-!
# Bridging the presented Deficiency One Algorithm to the multi-shelf machinery

This module supplies the **bridge** between the two halves of the Deficiency One Algorithm
(DOA) that the repository formalizes separately:

* the *presentation* — the combinatorial enumeration of shelf partitions and confluence vectors
  of `CRNT.Deficiency.DeficiencyOneAlgorithm` (`N.DOAAffirmsCapacity`), together with the shelf
  machinery of `CRNT.Deficiency.Shelf` and the placement rules read against the confluence
  vector (`ShelfPartition.imposes`);
* the *semantics* — the multi-shelf converse of
  `CRNT.Multistationarity.MultiShelfConverse`, which turns a balanced flux into shelf-wise
  confluence vectors.

## Feinberg's algorithm and the shelf construction

Feinberg's Deficiency One Algorithm decides the capacity for multiple positive steady states of
a *regular* deficiency-one mass-action network by a parameter-independent feasibility test
(Feinberg, *Chemical reaction network structure and the stability of complex isothermal reactors—
I. The deficiency zero and deficiency one theorems*, Chem. Eng. Sci. 1979; and the 1987 sequel;
and *Arch. Rational Mech. Anal.* **132** (1995)).  The algorithm enumerates *shelf partitions* of
the complexes into a lower, a middle and an upper shelf and, for each of them, solves a system of
linear constraints on the unknown log-ratio `μ = log y − log x` of the two candidate steady
states; the network is declared to have capacity exactly when some generated system is a
*signature* — it has a nonzero solution `μ` which is sign-compatible with the stoichiometric
subspace.  The *placement rules* of the enumeration are the four constraints of
`ShelfPartition.imposes`:

* **(height)** `y` strictly above `y'` ⟹ `y · μ > y' · μ`;
* **(middle level set)** `y, y'` both on the middle shelf ⟹ `y · μ = y' · μ`;
* **(upper cut pairs)** a cut pair `(y, y')` on the upper shelf orders `y · μ` versus `y' · μ`
  according to the sign of the cut-pair functional `[g, y→y', y]`;
* **(lower cut pairs)** the same, with the strict inequalities reversed.

## The shelf

A **shelf** is a *dependent set of reactions*: a set `A` of reactions whose reaction vectors
`y'_r − y_r` admit a **positive dependence** `λ` (`λ_r > 0` on `A`, `∑_{r ∈ A} λ_r (y'_r − y_r) = 0`).
The **confluence vector** of the shelf is that positive dependence, read as a vector on the
complexes through the incidence map `∂`.  In the repository's terms the shelf balance is
`ShelfLowerBalanced N A lam`, and `stoichMap_eq_zero_of_shelfLowerBalanced` below is the
assertion that the shelf is *dependent*: the image of the shelf flux under the stoichiometric map
vanishes.  `confluenceVector_of_shelfFlux` and `complexMap_incidenceMap_shelfFlux` are the two
consequences used by the bridge.

## The two-value argument, and its sharp obstruction

The *two-value argument* (`CRNT.Network.shelf_recursion`) is what makes the shelf decomposition
automatic: if the reaction set splits into two parts which are **pairing-constant** at `μ` — all
the sources of the reactions of a part pair equally with `μ` — and whose two pairing values are
**distinct**, then the *two global balances* (the lower balance `∑_r α_r (y'_r − y_r) = 0` and the
upper balance `∑_r α_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`) already force the two *shelf* balances: no
shelf-balance hypothesis is needed.

The argument is **sharp**, and this is a genuine obstruction rather than a gap:

* `twoShelf_cannot_iterate` — a shelf which is pairing-constant *cannot* be split into two parts
  with distinct pairing values, so the two-value argument applies to the whole reaction set but
  not to the shelves it produces;
* `threeShelf_freedom` — the two global balances supply only **two moments**, so with three
  pairing values the partial balances are *not* forced to vanish (an explicit family of partial
  balances satisfies both moment relations without vanishing).

Consequently a multi-shelf decomposition cannot be *iterated*: the bridge below is a
**two-shelf** bridge.

## What this module adds

The bridge theorems of `CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness` are stated with the
shelf-wise confluence vectors `DOAShelfFluxes` as *hypotheses*: that is the datum the presented
algorithm computes from the network and which the repository's verdict `N.DOAAffirmsCapacity`
does not record.  This module replaces that assumed witness by a **checkable combinatorial
condition on the run**:

* `DOARun.pairingStep_pos`, `DOARun.pairingStep_eq_zero_of_middle`, `DOARun.pairingStep_neg` —
  the **μ-step of a reaction is read off the shelves** of its source and its target.  The
  placement rules make the pairing strictly monotone in the shelf rank, so the shelf of the source
  and the shelf of the target determine the sign of the reaction's μ-step, and hence whether the
  reaction is forward, backward or flat;
* `doaRun_twoShelf_capacity` — the **canonical two-shelf split of a run**.  The forward and the
  backward parts of the sign decomposition are the two shelves; if each is pairing-constant and
  their pairing values differ, the two global balances force the two shelf balances, the flux
  decomposes into two shelf-wise confluence vectors, and the network has the capacity for
  multiple positive steady states.  This is the multi-shelf converse, applied to the data the
  presented algorithm actually produces.

## What is *not* proved here

* The **full Deficiency One Algorithm statement**, `N.HasMultistationarityCapacity ↔
  N.DOAAffirmsCapacity` (`CRNT.Deficiency.DeficiencyOneAlgorithm.DeficiencyOneAlgorithmStatement`),
  is **not** proved in this module — nor anywhere else in the repository.  The *algorithmic*
  direction is available through `doaRun_doaFeasible` and `doaRun_hasMultistationarityCapacity`
  (once the shelf-wise confluence vectors are supplied), and the *feasibility test* is proved
  correct in `CRNT.Multistationarity.DeficiencyOneAlgorithm`; what is missing is the **converse
  direction**: that a capacity flux always decomposes into a genuine shelf decomposition whose
  shelf-wise fluxes satisfy the two balance conditions.  That is Feinberg's *structural* analysis
  of the network — the search over shelf partitions and their confluence vectors — and it is
  genuinely algorithm-specific; the two-value argument of `shelf_recursion` only goes one way.
* The **existence** of a pairing-refined partition of the reaction set satisfying the
  pairing-constancy and distinctness conditions of `doaRun_twoShelf_capacity` is not established
  here: it is the datum the algorithm *searches* for.
* The **numerical version** of the algorithm (the reduction of the flux feasibility problem to a
  linear program over sign patterns).

## A concrete instance

The namespace `DOAStepExample` instantiates the bridge on the deficiency-one network
`0 → A`, `0 → B`, `A + B → 0` of `CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness.DOAExample`:
the run of the presented algorithm is reconstructed there, and the μ-step of the reaction `0 → A`
is shown to be positive (its source `0` is on the middle shelf, its target `A` on the upper one)
while the μ-step of the reaction `A + B → 0` is flat (both complexes are on the middle shelf).
The unit flux of that example is a positive dependence of the reaction set, so its incidence image
is a confluence vector whose complex map vanishes.

## A remark on `confluenceVector_of_shelfFlux`

With the repository's definition `IsConfluenceVector g := g ∈ LinearMap.range N.incidenceMap`, the
*membership* asserted by `confluenceVector_of_shelfFlux` is automatic — it is the *shelf flux*
that carries the content: `λ` is a positive dependence of the reaction vectors of the shelf `A`,
so that `A` is a dependent set of reactions and `λ` is its confluence vector.  The substantive
vanishing statement is `complexMap_incidenceMap_shelfFlux` (equivalently
`stoichMap_eq_zero_of_shelfLowerBalanced`).

Depends on: `CRNT.Multistationarity.MultiShelfConverse`,
`CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Finset

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

section MuStep

/-! ### The μ-step of a reaction is read off the shelves of its source and target -/

/-- **The μ-step of a reaction whose source is on the middle shelf and whose target is on the
upper shelf is strictly positive.**  In a run of the presented Deficiency One Algorithm the
pairing of a complex is strictly monotone in the shelf rank, so the placement rules determine
the sign of the reaction's μ-step.

The *height* rule of `ShelfPartition.imposes` is used with `y := N.targetIdx r` and
`y' := N.sourceIdx r`: the hypothesis is
`(run.sp.shelf (N.sourceIdx r)).rank < (run.sp.shelf (N.targetIdx r)).rank`, i.e.
`Shelf.middle.rank < Shelf.upper.rank`. -/
theorem DOARun.pairingStep_pos (run : DOARun N) (r : N.R)
    (hsrc : run.sp.shelf (N.sourceIdx r) = Shelf.middle)
    (htgt : run.sp.shelf (N.targetIdx r) = Shelf.upper) :
    0 < pairingStep N run.μ r := by
  have hlt : (run.sp.shelf (N.sourceIdx r)).rank < (run.sp.shelf (N.targetIdx r)).rank := by
    rw [hsrc, htgt]
    decide
  have hpair : CRNT.complexPairing (N.sourceIdx r).val run.μ
      < CRNT.complexPairing (N.targetIdx r).val run.μ :=
    run.imposes.1 (N.targetIdx r) (N.sourceIdx r) hlt
  have hpair' : CRNT.Network.complexPairing (N.reaction r).source run.μ
      < CRNT.Network.complexPairing (N.reaction r).target run.μ := by
    exact hpair
  rw [pairingStep, targetPairing, sourcePairing]
  linarith

/-- **A reaction between two complexes of the middle shelf is flat.**  The *middle level set* rule
of `ShelfPartition.imposes` is used with `y := N.targetIdx r` and `y' := N.sourceIdx r`: both
complexes lie on the middle shelf, hence their pairings with `μ` agree. -/
theorem DOARun.pairingStep_eq_zero_of_middle (run : DOARun N) (r : N.R)
    (hsrc : run.sp.shelf (N.sourceIdx r) = Shelf.middle)
    (htgt : run.sp.shelf (N.targetIdx r) = Shelf.middle) :
    pairingStep N run.μ r = 0 := by
  have hpair : CRNT.complexPairing (N.sourceIdx r).val run.μ
      = CRNT.complexPairing (N.targetIdx r).val run.μ :=
    (run.imposes.2.1 (N.targetIdx r) (N.sourceIdx r) htgt hsrc).symm
  have hpair' : CRNT.Network.complexPairing (N.reaction r).source run.μ
      = CRNT.Network.complexPairing (N.reaction r).target run.μ := by
    exact hpair
  rw [pairingStep, targetPairing, sourcePairing]
  linarith

/-- **The μ-step of a reaction whose source is on the upper shelf and whose target is on the
middle shelf is strictly negative.**  The *height* rule of `ShelfPartition.imposes` is used with
`y := N.sourceIdx r` and `y' := N.targetIdx r`: the hypothesis is
`(run.sp.shelf (N.targetIdx r)).rank < (run.sp.shelf (N.sourceIdx r)).rank`, i.e.
`Shelf.middle.rank < Shelf.upper.rank`. -/
theorem DOARun.pairingStep_neg (run : DOARun N) (r : N.R)
    (hsrc : run.sp.shelf (N.sourceIdx r) = Shelf.upper)
    (htgt : run.sp.shelf (N.targetIdx r) = Shelf.middle) :
    pairingStep N run.μ r < 0 := by
  have hlt : (run.sp.shelf (N.targetIdx r)).rank < (run.sp.shelf (N.sourceIdx r)).rank := by
    rw [htgt, hsrc]
    decide
  have hpair : CRNT.complexPairing (N.targetIdx r).val run.μ
      < CRNT.complexPairing (N.sourceIdx r).val run.μ :=
    run.imposes.1 (N.sourceIdx r) (N.targetIdx r) hlt
  have hpair' : CRNT.Network.complexPairing (N.reaction r).target run.μ
      < CRNT.Network.complexPairing (N.reaction r).source run.μ := by
    exact hpair
  rw [pairingStep, targetPairing, sourcePairing]
  linarith

end MuStep

section TwoShelf

/-! ### The canonical two-shelf split of a run -/

/-- **The Deficiency One Algorithm's canonical two-shelf split.**  Let `run` be a run of the
presented algorithm and let `α` be a flux balancing the network at the lower and at the upper
state.  Suppose the *forward* reactions of `run` and the *backward* reactions of `run` are each
pairing-constant at the log-ratio and their pairing values differ.  Then the flux splits into
two shelf-wise confluence vectors: the network is ADA feasible and has the capacity for multiple
positive steady states.

This replaces the *assumed* `DOAShelfFluxes` of `doaRun_doaFeasible` by a checkable combinatorial
condition on the run: `hnoFlat` makes the sign decomposition a genuine two-way split
(`signDecomposition_cover`, `signDecomposition_disjoint_forward_backward`), `hF`, `hB` and `hdiff`
make it a `TwoShelfSplit`, and the two-value argument of
`CRNT.Network.shelf_recursion` then forces the two shelf balances. -/
theorem doaRun_twoShelf_capacity (run : DOARun N) (α : N.R → ℝ)
    (hα : ∀ r, 0 < α r)
    (hlow : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, α r * Real.exp (sourcePairing N run.μ r) * N.reactionVector r s = 0)
    (hF : ∀ r ∈ forwardReactions N run.μ, ∀ r' ∈ forwardReactions N run.μ,
        sourcePairing N run.μ r = sourcePairing N run.μ r')
    (hB : ∀ r ∈ backwardReactions N run.μ, ∀ r' ∈ backwardReactions N run.μ,
        sourcePairing N run.μ r = sourcePairing N run.μ r')
    (hdiff : ∃ r ∈ forwardReactions N run.μ, ∃ r' ∈ backwardReactions N run.μ,
        sourcePairing N run.μ r ≠ sourcePairing N run.μ r')
    (hnoFlat : ∀ r, ¬ IsFlat N run.μ r) :
    N.HasMultistationarityCapacity := by
  classical
  -- the sign decomposition is a genuine two-way split: there are no flat reactions
  have hflat : flatReactions N run.μ = ∅ := by
    ext r
    constructor
    · intro hr
      exact absurd ((mem_flatReactions).mp hr) (hnoFlat r)
    · intro hr
      exact absurd hr (by simp)
  have hcover : forwardReactions N run.μ ∪ backwardReactions N run.μ
      = (Finset.univ : Finset N.R) := by
    calc forwardReactions N run.μ ∪ backwardReactions N run.μ
        = forwardReactions N run.μ ∪ backwardReactions N run.μ ∪ ∅ :=
          (Finset.union_empty _).symm
      _ = forwardReactions N run.μ ∪ backwardReactions N run.μ ∪ flatReactions N run.μ := by
        rw [hflat]
      _ = Finset.univ := signDecomposition_cover N run.μ
  have hdisj : forwardReactions N run.μ ∩ backwardReactions N run.μ = ∅ :=
    signDecomposition_disjoint_forward_backward N run.μ
  -- the two parts are pairing-constant with distinct pairing values: a two-shelf split
  have hsplit : TwoShelfSplit N run.μ (forwardReactions N run.μ) (backwardReactions N run.μ) :=
    ⟨hcover, hdisj, hF, hB, hdiff⟩
  -- the multi-shelf converse: the flux splits into two shelf-wise confluence vectors
  exact twoShelf_hasMultistationarityCapacity N run.μ α (forwardReactions N run.μ)
    (backwardReactions N run.μ) hsplit hα hlow hupp run.μ_ne_zero run.sign_compatible

end TwoShelf

section ShelfFlux

/-! ### The shelf flux determines the confluence vector -/

/-- **A shelf whose reaction vectors have a positive dependence.**  If the flux `lam` balances
the shelf `A` at the lower state — `∑_{r ∈ A} lam r * N.reactionVector r s = 0` — then the image
of `lam` (extended by zero off the shelf) under the stoichiometric map vanishes: the shelf is a
*dependent* set of reactions and `lam` is a positive dependence of its reaction vectors. -/
theorem stoichMap_eq_zero_of_shelfLowerBalanced (N : Network S) (A : Finset N.R)
    (lam : N.R → ℝ) (hbal : ShelfLowerBalanced N A lam) :
    N.stoichMap (fun r => if r ∈ A then lam r else 0) = 0 := by
  classical
  funext s
  rw [stoichMap_apply]
  simp only [Pi.zero_apply]
  calc ∑ r, (if r ∈ A then lam r else 0) * N.reactionVector r s
      = ∑ r ∈ A, lam r * N.reactionVector r s := by
        have h1 : (∑ r ∈ A, lam r * N.reactionVector r s)
            = ∑ r ∈ A, (if r ∈ A then lam r else 0) * N.reactionVector r s := by
          refine Finset.sum_congr rfl fun r hr => ?_
          rw [ite_eq_left hr]
        have h2 : (∑ r ∈ A, (if r ∈ A then lam r else 0) * N.reactionVector r s)
            = ∑ r ∈ (Finset.univ : Finset N.R),
              (if r ∈ A then lam r else 0) * N.reactionVector r s := by
          refine Finset.sum_subset (Finset.subset_univ A) ?_
          intro r _ hr
          rw [ite_eq_right hr]
          simp
        rw [h1, h2]
    _ = 0 := hbal s

/-- **The complex map of the incidence image of a balanced shelf flux vanishes.**  This is the
*dependence* content of the shelf: the shelf flux, pushed through the incidence map `∂` and then
through the complex matrix `Y`, is killed — because `Y ∘ ∂` is the stoichiometric map. -/
theorem complexMap_incidenceMap_shelfFlux (N : Network S) (A : Finset N.R) (lam : N.R → ℝ)
    (hbal : ∀ s, ∑ r ∈ A, lam r * N.reactionVector r s = 0) :
    N.complexMap (N.incidenceMap (fun r => if r ∈ A then lam r else 0)) = 0 := by
  classical
  have hcomp : N.complexMap (N.incidenceMap (fun r => if r ∈ A then lam r else 0))
      = N.stoichMap (fun r => if r ∈ A then lam r else 0) := by
    have h := congrArg (fun f : (N.R → ℝ) →ₗ[ℝ] (S → ℝ) =>
      f (fun r => if r ∈ A then lam r else 0)) N.complexMap_comp_incidenceMap
    simpa only [LinearMap.comp_apply] using h
  rw [hcomp]
  exact stoichMap_eq_zero_of_shelfLowerBalanced N A lam hbal

set_option linter.unusedVariables false in
/-- **A positive dependence of a set of reactions gives a confluence vector.**  If the
reactions of a set `A` carry a strictly positive dependence `lam` — the shelf balance at the lower
state, `∑_{r ∈ A} lam r * N.reactionVector r s = 0` — then the image of `lam` under the incidence
map is a confluence vector on the complexes.

Note that `IsConfluenceVector g` is membership in the range of the incidence map
(`CRNT.Deficiency.Confluence`); the *content* of the statement is that the shelf flux `lam` — a
positive dependence of the reaction vectors of the shelf `A` — is the data of a shelf. -/
theorem confluenceVector_of_shelfFlux (N : Network S) (A : Finset N.R) (lam : N.R → ℝ)
    (hlam : ∀ r ∈ A, 0 < lam r)
    (hbal : ∀ s, ∑ r ∈ A, lam r * N.reactionVector r s = 0) :
    N.IsConfluenceVector (N.incidenceMap (fun r => if r ∈ A then lam r else 0)) := by
  refine ⟨fun r => if r ∈ A then lam r else 0, rfl⟩

end ShelfFlux

/-! ### A concrete instance: the deficiency-one network `0 → A`, `0 → B`, `A + B → 0` -/

namespace DOAStepExample

/-- **The log-ratio of the example is nonzero.** -/
lemma mu_ne_zero : DOAExample.μ ≠ 0 := by
  intro h
  have h' := congrFun h DOAExample.Species.A
  simp [DOAExample.μ] at h'

/-- **The log-ratio is sign-compatible with the stoichiometric subspace.** -/
lemma signCompatible : DOAExample.N.SignCompatibleWithStoich DOAExample.μ :=
  ⟨DOAExample.N.reactionVector DOAExample.Rxn.r1 - DOAExample.N.reactionVector DOAExample.Rxn.r2,
    DOAExample.N.stoichSubspace.sub_mem
      (DOAExample.N.reactionVector_mem_stoichSubspace DOAExample.Rxn.r1)
      (DOAExample.N.reactionVector_mem_stoichSubspace DOAExample.Rxn.r2),
    by rw [DOAExample.stoichVec_eq]; exact sameSign_refl _⟩

/-- **The run of the presented algorithm on the example** `0 → A`, `0 → B`, `A + B → 0`: the shelf
partition places `A` on the upper shelf, `B` on the lower shelf and the two nonterminal complexes
`0` and `A + B` on the middle shelf, the confluence vector is the cut-space vector
`e_A + e_B − 2 e_0`, and the log-ratio is `μ = (1, −1)`. -/
noncomputable def run : DOARun DOAExample.N :=
  DOARun.ofData DOAExample.g DOAExample.g_isConfluence DOAExample.g_ne_zero
    DOAExample.sp DOAExample.μ mu_ne_zero signCompatible DOAExample.imposes

/-- **The source of the reaction `0 → A` is on the middle shelf.** -/
lemma shelf_source_r1 :
    run.sp.shelf (DOAExample.N.sourceIdx DOAExample.Rxn.r1) = Shelf.middle := by
  have h : DOAExample.N.sourceIdx DOAExample.Rxn.r1 =
      ⟨DOAExample.c0, DOAExample.mem_c0⟩ := Subtype.ext (by rfl)
  rw [h]
  show DOAExample.shelfOf DOAExample.c0 = Shelf.middle
  decide

/-- **The target of the reaction `0 → A` is on the upper shelf.** -/
lemma shelf_target_r1 :
    run.sp.shelf (DOAExample.N.targetIdx DOAExample.Rxn.r1) = Shelf.upper := by
  have h : DOAExample.N.targetIdx DOAExample.Rxn.r1 =
      ⟨DOAExample.cA, DOAExample.mem_cA⟩ := Subtype.ext (by rfl)
  rw [h]
  show DOAExample.shelfOf DOAExample.cA = Shelf.upper
  decide

/-- **The source of the reaction `A + B → 0` is on the middle shelf.** -/
lemma shelf_source_r3 :
    run.sp.shelf (DOAExample.N.sourceIdx DOAExample.Rxn.r3) = Shelf.middle := by
  have h : DOAExample.N.sourceIdx DOAExample.Rxn.r3 =
      ⟨DOAExample.cAB, DOAExample.mem_cAB⟩ := Subtype.ext (by rfl)
  rw [h]
  show DOAExample.shelfOf DOAExample.cAB = Shelf.middle
  decide

/-- **The target of the reaction `A + B → 0` is on the middle shelf.** -/
lemma shelf_target_r3 :
    run.sp.shelf (DOAExample.N.targetIdx DOAExample.Rxn.r3) = Shelf.middle := by
  have h : DOAExample.N.targetIdx DOAExample.Rxn.r3 =
      ⟨DOAExample.c0, DOAExample.mem_c0⟩ := Subtype.ext (by rfl)
  rw [h]
  show DOAExample.shelfOf DOAExample.c0 = Shelf.middle
  decide

/-- **The μ-step of the reaction `0 → A` is positive**: its source `0` lies on the middle shelf
and its target `A` on the upper one. -/
theorem pairingStep_r1 : 0 < pairingStep DOAExample.N run.μ DOAExample.Rxn.r1 :=
  run.pairingStep_pos DOAExample.Rxn.r1 shelf_source_r1 shelf_target_r1

/-- **The μ-step of the reaction `A + B → 0` is flat**: both its source and its target lie on the
middle shelf. -/
theorem pairingStep_r3 : pairingStep DOAExample.N run.μ DOAExample.Rxn.r3 = 0 :=
  run.pairingStep_eq_zero_of_middle DOAExample.Rxn.r3 shelf_source_r3 shelf_target_r3

/-- **The unit flux balances the reaction set of the example.** -/
lemma unitFlux_balance : ∀ s : DOAExample.Species,
    ∑ r ∈ (Finset.univ : Finset DOAExample.Rxn),
      (1 : ℝ) * DOAExample.N.reactionVector r s = 0 := by
  intro s
  rw [DOAExample.univ_Rxn]
  cases s <;>
    simp [reactionVector_apply, DOAExample.reaction, DOAExample.c0, DOAExample.cA,
      DOAExample.cB, DOAExample.cAB, Finset.sum_insert, Finset.sum_singleton]

/-- **The incidence image of the unit flux is a confluence vector.** -/
theorem confluenceVector_example :
    DOAExample.N.IsConfluenceVector
      (DOAExample.N.incidenceMap
        (fun r => if r ∈ (Finset.univ : Finset DOAExample.Rxn) then (1 : ℝ) else 0)) :=
  confluenceVector_of_shelfFlux DOAExample.N (Finset.univ : Finset DOAExample.Rxn)
    (fun _ => (1 : ℝ)) (by intro r _; norm_num) unitFlux_balance

/-- **The complex map of the incidence image of the unit flux vanishes.** -/
theorem complexMap_example :
    DOAExample.N.complexMap
      (DOAExample.N.incidenceMap
        (fun r => if r ∈ (Finset.univ : Finset DOAExample.Rxn) then (1 : ℝ) else 0)) = 0 :=
  complexMap_incidenceMap_shelfFlux DOAExample.N (Finset.univ : Finset DOAExample.Rxn)
    (fun _ => (1 : ℝ)) unitFlux_balance

end DOAStepExample

end Network

end CRNT

/-! ## Axiom audit of the principal declarations -/

#print axioms CRNT.Network.DOARun.pairingStep_pos
#print axioms CRNT.Network.DOARun.pairingStep_eq_zero_of_middle
#print axioms CRNT.Network.DOARun.pairingStep_neg
#print axioms CRNT.Network.doaRun_twoShelf_capacity
#print axioms CRNT.Network.stoichMap_eq_zero_of_shelfLowerBalanced
#print axioms CRNT.Network.complexMap_incidenceMap_shelfFlux
#print axioms CRNT.Network.confluenceVector_of_shelfFlux
#print axioms CRNT.Network.DOAStepExample.pairingStep_r1
#print axioms CRNT.Network.DOAStepExample.pairingStep_r3
#print axioms CRNT.Network.DOAStepExample.confluenceVector_example
#print axioms CRNT.Network.DOAStepExample.complexMap_example
