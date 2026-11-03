import CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness

/-!
# The shelf fluxes of the Deficiency One Algorithm: the construction

`CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness` proves the correctness of the *presented*
Deficiency One Algorithm, but its bridge theorem `CRNT.Network.doaRun_hasMultistationarityCapacity`
takes the **shelf-wise confluence vectors** (`CRNT.Network.DOAShelfFluxes`) as an *extra
hypothesis*.  This module makes the **construction** explicit: it records the Feinberg datum

> a *shelf* is a set of reactions whose reaction vectors admit a **strictly positive
> dependence**, and the *confluence vector* of the shelf is that dependence,

as a structure (`CRNT.Network.ShelfDependence`), assembles a family of such shelves into the
shelf-wise confluence vectors of the algorithm (`CRNT.Network.ShelfDependenceFamily.toShelfFluxes`),
checks the two flux balances that the assembly produces, and proves the **reduction** of the
Deficiency One Algorithm to the construction problem.

## The positive-dependence formulation

* `ShelfDependence N sh lam` — the flux `lam` is supported on the shelf `sh`, strictly positive on it,
  and balances the shelf at the lower state, `∑_{r ∈ sh} lam_r (y'_r − y_r) = 0`.  This is
  Feinberg's *confluence vector* of a shelf (Feinberg 1995b, *The deficiency one algorithm*,
  §3; Feinberg 2019, *Foundations of Chemical Reaction Network Theory*, ch. 8).
* `ShelfDependenceFamily N` — a **shelf decomposition with positive dependences**: a partition of
  the reaction set into shelves, each carrying a strictly positive dependence.
* `ShelfDependenceFamily.toShelfFluxes` — the **assembly lemma**: such a family *is* the
  shelf-wise confluence vector data `CRNT.Network.DOAShelfFluxes` of the algorithm.

## The balances

* `ShelfDependenceFamily.globalFlux_pos` — the global flux (the sum of the shelf fluxes) is
  strictly positive on every reaction;
* `ShelfDependenceFamily.globalFlux_lower_balance` — the global flux balances the network at the
  lower state;
* `ShelfDependenceFamily.globalFlux_upper_balance` — the global flux balances the network at the
  upper state `e^{μ}` whenever every shelf does.

## The reduction

* `doaRun_hasMultistationarityCapacity_of_shelfDependences` — **the reduction of the Deficiency
  One Algorithm to the construction problem**: a run of the algorithm together with a shelf
  decomposition with positive dependences yields the capacity for multiple positive steady
  states.  The *placement* condition — the sources of the reactions of a shelf lie on the middle
  shelf of the run's shelf partition — is the hypothesis which makes the exponential factor
  `e^{⟨y_r, μ⟩}` constant on the shelf.
* `doaRun_hasMultistationarityCapacity_of_shelfDependences_exists` — the same, with the shelf
  decomposition bundled into one existential.
* `doaRun_hasMultistationarityCapacity_of_shelfDependences_of_upperBalance` — the same, with the
  *upper balance* of each shelf in place of the placement condition.

## The remaining combinatorial core

The reduction above is **not** the algorithm: it assumes the shelf decomposition with positive
dependences.  What Feinberg's algorithm *produces* — and what is still missing — is the lemma

```lean
theorem doaRun_implies_shelfDependenceFamily (run : DOARun N) :
    ∃ (f : ShelfDependenceFamily N),
      ∀ sh ∈ f.shelves, ∀ r ∈ sh, run.sp.shelf (N.sourceIdx r) = Shelf.middle
```

i.e. that the **shelves built from the run's confluence vector `g` and shelf partition `sp`** —
the classes of reactions with a common *reduced* source — carry strictly positive dependences of
their reaction vectors.  This is the heart of Feinberg's algorithm: the *reduced reaction
vectors* of a shelf have a positive dependence because the shelf is a **dependent** set of
reaction vectors, and the deficiency-one dimension count `n − ℓ − s = 1` is what makes the
dependence exist and be unique up to scaling.  The module documents precisely which part of the
construction is combinatorial (which reactions belong to which shelf) and which part is
linear-algebraic (the existence of the positive dependence).

## A concrete instance

`CRNT.Network.DOAExample` — the deficiency-one network `0 → X`, `0 → Y`, `X + Y → 0` on the
species `{A, B}` — is worked out completely: the whole reaction set is a single shelf, the unit
flux is a strictly positive dependence of its three reaction vectors, and the reduction yields
the capacity for multiple positive steady states.

## The placement condition is not decoration

The reduction of the Deficiency One Algorithm to the shelf construction **cannot** drop the
placement condition, and the module contains a machine-checked obstruction to that effect.
`CRNT.Network.TwoWay` is the network `0 → A`, `A → 0` on the species `{A}`: its whole reaction
set is a single shelf and the unit flux is a strictly positive dependence of its two reaction
vectors `(1)` and `−(1)` (`CRNT.Network.TwoWay.oneShelfDependence`), yet the network has **no**
capacity (`CRNT.Network.TwoWay.not_hasCapacity`): the lower flux balance forces the two fluxes
to be equal and the upper flux balance then forces `e^{μ} = 1`, i.e. `μ = 0`, which is
incompatible with the sign compatibility of `μ` with the stoichiometric subspace.  The reason is
that the two sources of the two-way network do **not** pair equally with `μ`; the placement
condition of the run is exactly what forces the pairing to be constant on a shelf.

Depends on: `CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness`.
-/

-- the `unnecessarySeqFocus` linter fires on the `<;>`-chains of the `Fintype` instances and of
-- the case splits below; the chains are genuinely focused, so the linter is switched off.
set_option linter.unnecessarySeqFocus false

namespace CRNT

namespace Network

open scoped BigOperators
open Finset

section General

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-! ### The positive-dependence formulation -/

/-- **A shelf dependence**: a flux `lam` on a set `sh` of reactions which is supported on `sh`,
strictly positive on it, and which **balances the shelf at the lower state**,
`∑_{r ∈ sh} lam_r (y'_r − y_r) = 0`.

This is the Feinberg datum (Feinberg 1995b, *The deficiency one algorithm*, §3; Feinberg 2019,
*Foundations of Chemical Reaction Network Theory*, ch. 8): the **confluence vector** of a shelf is
the strictly positive dependence of the reaction vectors of the shelf. Positivity means that
every reaction in the shelf carries a strictly positive coefficient in this balancing flux; it
is an explicit algebraic condition, not a claim that the shelf or the whole network is endotactic. -/
structure ShelfDependence (N : Network S) (sh : Finset N.R) (lam : N.R → ℝ) : Prop where
  /-- **Support**: the dependence vanishes off the shelf. -/
  support : ∀ r, r ∉ sh → lam r = 0
  /-- **Positivity**: the dependence is strictly positive on the shelf. -/
  positive : ∀ r ∈ sh, 0 < lam r
  /-- **The lower balance of the shelf**: `∑_{r ∈ sh} lam_r (y'_r − y_r) = 0`. -/
  balance : ∀ s, ∑ r ∈ sh, lam r * N.reactionVector r s = 0

/-- **A shelf decomposition with positive dependences**: a partition of the reaction set into
shelves, each of which carries a strictly positive dependence of its reaction vectors.  This is
the datum Feinberg's algorithm is supposed to *produce*. -/
structure ShelfDependenceFamily (N : Network S) where
  /-- The shelves: a partition of the reaction set. -/
  shelves : Finset (Finset N.R)
  /-- The dependence of each shelf. -/
  lam : Finset N.R → N.R → ℝ
  /-- **Each shelf carries a positive dependence** of its reaction vectors. -/
  dependence : ∀ sh ∈ shelves, ShelfDependence N sh (fun r => lam sh r)
  /-- **Disjointness**: two distinct shelves are disjoint. -/
  disjoint : ∀ sh ∈ shelves, ∀ sh' ∈ shelves, sh ≠ sh' → sh ∩ sh' = ∅
  /-- **Covering**: every reaction of the network lies on some shelf. -/
  cover : ∀ r : N.R, ∃ sh ∈ shelves, r ∈ sh

/-- **The assembly lemma.**  A shelf decomposition with positive dependences *is* the shelf-wise
confluence vector data of the Deficiency One Algorithm: the flux of a shelf is its positive
dependence, and the shelf balances at the lower state.  This is the step which turns the
*combinatorial* datum (a partition of the reaction set into dependent sets) into the *analytic*
datum (`DOAShelfFluxes`) that the algorithm's feasibility test consumes. -/
def ShelfDependenceFamily.toShelfFluxes (f : ShelfDependenceFamily N) : DOAShelfFluxes N where
  shelves := f.shelves
  cover := f.cover
  disjoint := f.disjoint
  flux := f.lam
  support := fun sh hsh r hr => (f.dependence sh hsh).support r hr
  positive := fun sh hsh r hr => (f.dependence sh hsh).positive r hr
  lower_balance := fun sh hsh s => (f.dependence sh hsh).balance s

/-- **The global flux of a shelf decomposition with positive dependences is the sum of the shelf
dependences.** -/
theorem ShelfDependenceFamily.globalFlux_eq_sum (f : ShelfDependenceFamily N) (r : N.R) :
    f.toShelfFluxes.globalFlux r = ∑ sh ∈ f.shelves, f.lam sh r := rfl

/-- **The global flux is strictly positive on every reaction.**  The shelves cover the reaction
set, and each shelf dependence is strictly positive on its shelf. -/
theorem ShelfDependenceFamily.globalFlux_pos (f : ShelfDependenceFamily N) (r : N.R) :
    0 < f.toShelfFluxes.globalFlux r :=
  f.toShelfFluxes.globalFlux_pos r

/-- **The global flux satisfies the lower balance** `∑_r lam_r (y'_r − y_r) = 0`: it is the sum of
the shelf fluxes, and each shelf balances on its own. -/
theorem ShelfDependenceFamily.globalFlux_lower_balance (f : ShelfDependenceFamily N) (s : S) :
    ∑ r, f.toShelfFluxes.globalFlux r * N.reactionVector r s = 0 :=
  f.toShelfFluxes.globalFlux_lower_balance s

/-- **The upper balance of a shelf**: `∑_{r ∈ sh} lam_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`.  This is the
balance of the shelf at the *upper* state `e^{μ}`; it is the balance which the exponential factor
of the algorithm's second flux equation produces. -/
def ShelfUpperBalance (N : Network S) (sh : Finset N.R) (lam : N.R → ℝ) (μ : S → ℝ) : Prop :=
  ∀ s, ∑ r ∈ sh, lam r * Real.exp (complexPairing (N.reaction r).source μ) *
    N.reactionVector r s = 0

/-- **The global flux satisfies the upper balance** whenever every shelf does.  The global flux is
the sum of the shelf fluxes, and the flux of a shelf vanishes off the shelf, so the global
balance is the sum of the shelf balances. -/
theorem ShelfDependenceFamily.globalFlux_upper_balance (f : ShelfDependenceFamily N) (μ : S → ℝ)
    (hup : ∀ sh ∈ f.shelves, ShelfUpperBalance N sh (f.lam sh) μ) (s : S) :
    ∑ r, f.toShelfFluxes.globalFlux r * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s = 0 := by
  classical
  have hbal : ∀ sh ∈ f.shelves,
      (∑ r, f.lam sh r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s) = 0 := by
    intro sh hsh'
    have h1 : (∑ r, f.lam sh r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s) = ∑ r ∈ sh, f.lam sh r *
          Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s := by
      symm
      refine Finset.sum_subset (Finset.subset_univ sh) ?_
      intro r _ hr
      rw [(f.dependence sh hsh').support r hr]
      simp
    rw [h1]
    exact hup sh hsh' s
  calc ∑ r, f.toShelfFluxes.globalFlux r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s
      = ∑ r, (∑ sh ∈ f.shelves, f.lam sh r) *
          Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s := rfl
    _ = ∑ r ∈ (Finset.univ : Finset N.R), ∑ sh ∈ f.shelves,
        f.lam sh r * Real.exp (complexPairing (N.reaction r).source μ) *
          N.reactionVector r s := by
      refine Finset.sum_congr rfl fun r _ => ?_
      calc (∑ sh ∈ f.shelves, f.lam sh r) *
          Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s
          = (∑ sh ∈ f.shelves, f.lam sh r) *
            (Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s) := by ring
        _ = ∑ sh ∈ f.shelves, f.lam sh r *
            (Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s) :=
          Finset.sum_mul _ _ _
        _ = ∑ sh ∈ f.shelves, f.lam sh r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := by
          refine Finset.sum_congr rfl fun sh _ => ?_
          ring
    _ = ∑ sh ∈ f.shelves, ∑ r ∈ (Finset.univ : Finset N.R),
        f.lam sh r * Real.exp (complexPairing (N.reaction r).source μ) *
          N.reactionVector r s := Finset.sum_comm
    _ = 0 := by
      refine Finset.sum_eq_zero fun sh hsh => ?_
      exact hbal sh hsh

/-- **A shelf whose sources pair equally with the log-ratio satisfies the upper balance.**  The
exponential factor `e^{⟨y_r, μ⟩}` is constant on the shelf, so the upper balance is the lower
balance.  This is the *quantitative* content of the placement rules: they make the middle shelf a
level set of `μ`, and hence they make the upper balance of the algorithm's second flux equation
follow from the lower balance of the shelf. -/
theorem ShelfDependenceFamily.shelfUpperBalance_of_constPairing (f : ShelfDependenceFamily N)
    (μ : S → ℝ) (sh : Finset N.R) (hsh : sh ∈ f.shelves)
    (hp : ∀ r ∈ sh, ∀ r' ∈ sh,
      complexPairing (N.reaction r).source μ = complexPairing (N.reaction r').source μ) :
    ShelfUpperBalance N sh (f.lam sh) μ := by
  have h := f.toShelfFluxes.shelf_upper_balance μ sh hsh hp
  simpa [ShelfUpperBalance, ShelfDependenceFamily.toShelfFluxes] using h

/-! ### The reduction of the Deficiency One Algorithm to the construction -/

/-- **The reduction of the Deficiency One Algorithm to the shelf construction.**

A *run* of the presented algorithm — a nonzero cut-space confluence vector `g` on the complexes, a
shelf partition `sp` of the complexes, and a nonzero log-ratio `μ` which is sign-compatible with
the stoichiometric subspace and meets the placement rules — together with a **shelf decomposition
with positive dependences** yields the capacity for multiple positive steady states.

The *placement* condition `hmiddle` says that the sources of the reactions of every shelf lie on
the **middle shelf** of the run's shelf partition.  It is what makes the exponential factor
`e^{⟨y_r, μ⟩}` of the algorithm's second flux equation constant on each shelf, hence what makes
the upper balance follow from the lower balance of the shelf.

This is the *exact* shape of Feinberg's algorithm (Feinberg 1995b; Feinberg 2019, ch. 8): the
algorithm's data are the shelf partition and the shelf-wise confluence vectors, and the
correctness theorem is "a signature of the algorithm ⟹ the capacity".  What is **not** proved
here is that the algorithm *produces* the shelf decomposition: see the module docstring. -/
theorem doaRun_hasMultistationarityCapacity_of_shelfDependences
    (run : DOARun N) (f : ShelfDependenceFamily N)
    (hmiddle : ∀ sh ∈ f.shelves, ∀ r ∈ sh, run.sp.shelf (N.sourceIdx r) = Shelf.middle) :
    N.HasMultistationarityCapacity :=
  doaRun_hasMultistationarityCapacity run f.toShelfFluxes hmiddle

/-- **The reduction, in the bundled form**: a run of the algorithm together with a shelf
decomposition with positive dependences — and with the placement condition — yields the capacity
for multiple positive steady states. -/
theorem doaRun_hasMultistationarityCapacity_of_shelfDependences_exists
    (run : DOARun N)
    (hshelves : ∃ (shelves : Finset (Finset N.R)) (lam : Finset N.R → N.R → ℝ),
        (∀ sh ∈ shelves, ShelfDependence N sh (fun r => lam sh r)) ∧
        (∀ sh ∈ shelves, ∀ sh' ∈ shelves, sh ≠ sh' → sh ∩ sh' = ∅) ∧
        (∀ r : N.R, ∃ sh ∈ shelves, r ∈ sh) ∧
        (∀ sh ∈ shelves, ∀ r ∈ sh, run.sp.shelf (N.sourceIdx r) = Shelf.middle)) :
    N.HasMultistationarityCapacity := by
  obtain ⟨shelves, lam, hdep, hdisj, hcover, hmiddle⟩ := hshelves
  exact doaRun_hasMultistationarityCapacity_of_shelfDependences run
    { shelves := shelves, lam := lam, dependence := hdep, disjoint := hdisj, cover := hcover }
    hmiddle

/-- **The reduction, with the upper balance of the shelves in place of the placement
condition.**  This is the *exact* reduction to the two flux balances of the algorithm: a run of
the algorithm together with a shelf decomposition whose shelves have positive dependences *and*
satisfy the upper balance yields the capacity. -/
theorem doaRun_hasMultistationarityCapacity_of_shelfDependences_of_upperBalance
    (run : DOARun N) (f : ShelfDependenceFamily N)
    (hup : ∀ sh ∈ f.shelves, ShelfUpperBalance N sh (f.lam sh) run.μ) :
    N.HasMultistationarityCapacity := by
  refine N.doaFeasible_implies_capacity
    ⟨DOACandidate.ofData N run.μ run.μ_ne_zero f.toShelfFluxes.globalFlux
      f.toShelfFluxes.globalFlux_pos run.sign_compatible
      f.toShelfFluxes.globalFlux_lower_balance ?_⟩
  exact f.globalFlux_upper_balance run.μ hup

/-- **The reduction, in the form of the algorithm's two flux balances.**  A run of the algorithm
together with a shelf decomposition with positive dependences, whose shelves satisfy the upper
balance, yields a **feasible system of the Deficiency One Algorithm**: a strictly positive flux
with the two flux balances at the log-ratio `μ` of the run. -/
theorem doaRun_doaFeasible_of_shelfDependences_of_upperBalance
    (run : DOARun N) (f : ShelfDependenceFamily N)
    (hup : ∀ sh ∈ f.shelves, ShelfUpperBalance N sh (f.lam sh) run.μ) :
    N.DOAFeasible := by
  refine ⟨DOACandidate.ofData N run.μ run.μ_ne_zero f.toShelfFluxes.globalFlux
    f.toShelfFluxes.globalFlux_pos run.sign_compatible
    f.toShelfFluxes.globalFlux_lower_balance ?_⟩
  exact f.globalFlux_upper_balance run.μ hup

end General

/-! ### A concrete deficiency-one instance -/

namespace DOAExample
namespace ShelfFlux

open Species

/-- **The unit flux is a strictly positive dependence of the reaction vectors of the example.**
The three reaction vectors of the network `0 → X`, `0 → Y`, `X + Y → 0` are `e_A`, `e_B` and
`− e_A − e_B`; their sum vanishes, so the unit flux is a positive dependence, and the whole
reaction set is a single **shelf** of the algorithm. -/
theorem oneShelfDependence : ShelfDependence N (Finset.univ : Finset Rxn) (fun _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp at hr
  · intro r hr
    norm_num
  · intro s
    cases s <;>
      simp [univ_Rxn, Finset.sum_insert, Finset.sum_singleton, reaction, c0, cA, cB, cAB]

/-- **The shelf decomposition of the example**: the whole reaction set is a single shelf, whose
confluence vector is the unit flux. -/
def family : ShelfDependenceFamily N where
  shelves := {Finset.univ}
  lam := fun _ _ => (1 : ℝ)
  dependence := by
    intro sh hsh
    have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
    subst h1
    exact oneShelfDependence
  disjoint := by
    intro sh hsh sh' hsh' hne
    have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
    have h2 : sh' = Finset.univ := Finset.mem_singleton.mp hsh'
    rw [h1, h2] at hne
    rw [h1, h2]
    exact (hne rfl).elim
  cover := by
    intro r
    exact ⟨Finset.univ, by simp, Finset.mem_univ r⟩

/-- **The run of the Deficiency One Algorithm on the example**: the confluence vector
`e_A + e_B − 2 e_0`, the shelf partition placing `A` on the upper shelf, `B` on the lower shelf
and the two nonterminal complexes `0` and `A + B` on the middle shelf, and the log-ratio
`μ = (1, −1)`. -/
noncomputable def run : DOARun N where
  g := g
  g_isConfluence := g_isConfluence
  g_ne_zero := g_ne_zero
  sp := sp
  μ := μ
  μ_ne_zero := by
    intro h
    have h' := congrFun h Species.A
    simp [μ] at h'
  sign_compatible := by
    refine ⟨N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2, ?_, ?_⟩
    · exact N.stoichSubspace.sub_mem (N.reactionVector_mem_stoichSubspace Rxn.r1)
        (N.reactionVector_mem_stoichSubspace Rxn.r2)
    · rw [stoichVec_eq]
      exact sameSign_refl _
  imposes := imposes

/-- **Every reaction of the example has its source on the middle shelf** of the run's shelf
partition: the sources are `0` (of `0 → A` and `0 → B`) and `A + B` (of `A + B → 0`), and the
middle shelf of the enumeration carries the two nonterminal complexes `0` and `A + B`.  This is
the *placement* condition of the reduction. -/
theorem middle_sources (r : Rxn) : run.sp.shelf (N.sourceIdx r) = Shelf.middle := by
  cases r with
  | r1 =>
      show shelfOf c0 = Shelf.middle
      simp [shelfOf, rankOf_c0]
  | r2 =>
      show shelfOf c0 = Shelf.middle
      simp [shelfOf, rankOf_c0]
  | r3 =>
      show shelfOf cAB = Shelf.middle
      simp [shelfOf, rankOf_cAB]

/-- **The Deficiency One Algorithm's construction on the example yields the capacity for multiple
positive steady states.**  The network `0 → X`, `0 → Y`, `X + Y → 0` is the standard
deficiency-one example (four complexes, one linkage class, stoichiometric rank two, hence
`δ = 4 − 1 − 2 = 1`); the shelf decomposition constructed above is the one the algorithm
produces, and the reduction turns it into the capacity.  The proof goes through the *shelf
construction* and not through the flux certificate: the flux is assembled from the shelf-wise
positive dependences. -/
theorem hasCapacity_of_shelfDependence : N.HasMultistationarityCapacity := by
  refine doaRun_hasMultistationarityCapacity_of_shelfDependences run family ?_
  intro sh hsh r hr
  have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
  subst h1
  exact middle_sources r

end ShelfFlux
end DOAExample

/-! ### An obstruction: a positive dependence alone does not give the capacity -/

namespace TwoWay

/-- The species of the two-way network: `{A}`. -/
inductive Species where
  | A
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A}
  complete := by intro s; cases s <;> simp

/-- The reactions of the two-way network: `0 → A` and `A → 0`. -/
inductive Rxn where
  | r1 | r2
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2}
  complete := by intro r; cases r <;> simp

/-- The zero complex. -/
def c0 : Complex Species := fun _ => 0

/-- The complex `A`. -/
def cA : Complex Species := fun _ => 1

/-- The two reactions. -/
def reaction : Rxn → Reaction Species
  | .r1 => { source := c0, target := cA }
  | .r2 => { source := cA, target := c0 }

/-- The two-way network `0 → A`, `A → 0`. -/
abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- The univ of the reaction index. -/
lemma univ_Rxn : (Finset.univ : Finset Rxn) = {Rxn.r1, Rxn.r2} := by
  ext r
  cases r <;> simp

/-- The univ of the species index. -/
lemma univ_Species : (Finset.univ : Finset Species) = {Species.A} := by
  ext s
  cases s <;> simp

/-- **The whole reaction set of the two-way network is a single shelf, and the unit flux is a
strictly positive dependence of its reaction vectors**: the two reaction vectors are `(1)` and
`−(1)`, and they sum to zero. -/
theorem oneShelfDependence : ShelfDependence N (Finset.univ : Finset Rxn) (fun _ => (1 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro r hr
    simp at hr
  · intro r hr
    norm_num
  · intro s
    rw [univ_Rxn]
    simp [Finset.sum_insert, Finset.sum_singleton, reaction, c0, cA, reactionVector_apply]

/-- **The two-way network has no capacity for multiple positive steady states.**  The lower flux
balance forces the two fluxes to be equal; the upper flux balance then forces
`e^{⟨A, μ⟩} = e^{⟨0, μ⟩} = 1`, hence `μ = 0`, which is incompatible with the sign compatibility
of `μ` with the stoichiometric subspace. -/
theorem not_hasCapacity : ¬ N.HasMultistationarityCapacity := by
  intro h
  obtain ⟨α, μ, σ, hα, hσS, hσ0, hsign, hflux, hflux'⟩ :=
    (N.hasMultistationarityCapacity_iff_flux_sign).1 h
  -- the lower balance forces the two fluxes to be equal
  have hlow : α Rxn.r1 = α Rxn.r2 := by
    have h := hflux Species.A
    rw [univ_Rxn] at h
    simp [Finset.sum_insert, Finset.sum_singleton, reaction, c0, cA, reactionVector_apply] at h
    linarith
  -- the upper balance forces `e^{μ A} = 1`
  have hupp : α Rxn.r1 = α Rxn.r2 * Real.exp (μ Species.A) := by
    have h := hflux' Species.A
    rw [univ_Rxn] at h
    simp [Finset.sum_insert, Finset.sum_singleton, reaction, c0, cA, reactionVector_apply,
      complexPairing, univ_Species, Finset.sum_insert, Finset.sum_singleton] at h
    linarith
  have hα2 : 0 < α Rxn.r2 := hα Rxn.r2
  have hexp : Real.exp (μ Species.A) = 1 := by
    have hx : α Rxn.r2 = α Rxn.r2 * Real.exp (μ Species.A) := hlow.symm.trans hupp
    have hy : α Rxn.r2 * (1 : ℝ) = α Rxn.r2 * Real.exp (μ Species.A) := by simpa using hx
    have h2 : (1 : ℝ) = Real.exp (μ Species.A) := mul_left_cancel₀ (ne_of_gt hα2) hy
    simpa using h2.symm
  have hμA : μ Species.A = 0 := by
    have h1 : Real.exp (μ Species.A) = Real.exp 0 := by rw [hexp, Real.exp_zero]
    have h2 := Real.exp_injective h1
    simpa using h2
  have hμ0 : μ = 0 := by
    funext s
    cases s
    exact hμA
  have h1 : SignType.sign (σ Species.A) = 0 := by
    rw [hsign]
    simp [hμ0]
  have hσA : σ Species.A = 0 := by
    rw [sign_eq_zero_iff] at h1
    exact h1
  have h2 : σ = 0 := by
    funext s
    cases s
    exact hσA
  exact hσ0 h2

end TwoWay

end Network

end CRNT
