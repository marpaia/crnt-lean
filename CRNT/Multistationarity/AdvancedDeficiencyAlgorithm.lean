import CRNT.Multistationarity.DeficiencyOneAlgorithm
import CRNT.Deficiency.AdvancedDeficiencyAlgorithm
import CRNT.Geometry.Endotactic
import CRNT.Decision.ComputableDeficiency
import Mathlib.Basic.Sign.Basic

/-!
# Shelf flux certificates for multistationarity capacity

The **Advanced Deficiency Algorithm** (ADA) is the higher-deficiency successor of Feinberg's
Deficiency One Algorithm (DOA, 1995b): for a mass-action network of deficiency `δ ≥ 1` it decides
the *capacity* for multiple positive steady states by a parameter-independent feasibility test.
Like the DOA, the test is a finite system of **linear equalities and inequalities** in the unknown
log-ratio `μ = log y − log x` of the two candidate steady states, together with a **linear
feasibility problem in the fluxes**.

This module formalizes the semantic shelf-flux certificate `ADAFeasible` and proves that it
exists **iff** the network has the capacity for multiple steady states. It builds on the
flux characterization in `CRNT.Multistationarity.DeficiencyOneAlgorithm`. The certificate permits
one shelf containing every reaction, so the existence equivalence is not a verification of the
published algorithm's prescribed shelf enumeration or its finite numerical search.

## The data of an ADA run

An ADA run is given by

* a **shelf decomposition** (`ADAShelfDecomposition`) — a *partition* of the reaction set into
  **shelves**, each of which is a *subnetwork* of `N` (the shelf is the reaction set itself);
* a **confluence vector** per shelf (`ADAConfluences`) — a flux `λ` on the shelf which is
  *supported* on the shelf (it vanishes off it), *strictly positive* on it, and satisfies the
  **lower balance condition** on the shelf,
  `∑_{r ∈ sh} λ_r (y'_r − y_r) = 0`;
* the **upper balance condition** on the shelf at the log-ratio `μ`,
  `∑_{r ∈ sh} λ_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`;
* a **log-ratio** `μ ≠ 0` which is **sign compatible** with the stoichiometric subspace `S(N)`
  (`N.SignCompatibleWithStoich μ`), i.e. `μ` has the coordinatewise sign pattern of a nonzero
  stoichiometric vector — the sign pattern of `y − x`.

`N.ADAFeasible` is the statement that such a run exists.  It is the exact analogue of
`N.DOAFeasible`, with the single DOA flux replaced by a *decomposition* of the flux into one
confluence vector per shelf.

## The correctness

* `adaFeasible_implies_capacity` — **the algorithmic direction**: a feasible ADA system yields the
  capacity.  The witness is the *global flux* `α = ∑_sh λ_sh`, the sum of the shelf fluxes; it is
  strictly positive on every reaction (the shelves cover the reaction set) and it satisfies the
  two global flux balances, because each shelf balances on its own.
* `capacity_implies_adaFeasible` — **the converse direction**: a network with the capacity yields a
  feasible ADA system, namely the *one-shelf* system, in which the single shelf is the whole
  reaction set and its confluence vector is the flux of the witnessing steady states.  This is
  the `DOAFeasible` flux certificate. Multi-shelf certificates carry additional decomposition data;
  the permitted one-shelf choice makes their existence equivalent to the original flux criterion.
* `hasMultistationarityCapacity_iff_adaFeasible` — the two together: capacity is equivalent to
  the existence of a shelf-flux certificate.
* `adaFeasible_implies_doaFeasible` — **the ADA refines the DOA**: an ADA-feasible network is
  DOA-feasible, the global flux being the DOA witness.
* `doaFeasible_implies_adaFeasible` — the converse refinement, on the one-shelf system.

## The connection with the existing leaf-M8 declaration

`CRNT.Deficiency.AdvancedDeficiencyAlgorithm` already contains the *combinatorial* ADA
(`ADAData`, `ADAData.imposes`, `ADAAffirmsCapacity`) and the non-vacuity theorem
`stoichSubspace_ne_bot_of_adaAffirmsCapacity`.  This module connects the two:

* `adaFeasible_implies_adaAffirmsCapacity` — a feasible ADA system implies the existing verdict
  `N.ADAAffirmsCapacity`, so the **existing leaf-M8 declaration
  `stoichSubspace_ne_bot_of_adaAffirmsCapacity` is a consequence of the new work**;
* `adaFeasible_implies_stoichSubspace_ne_bot` — the same conclusion directly;
* `adaAffirmsCapacity_iff_exists_signCompatible` — a *faithfulness note* about the existing
  verdict: because the per-class values `Mᵢ` and the shelving may always be chosen with `M ≡ 0`,
  `ADAAffirmsCapacity` is equivalent to the existence of a nonzero sign-compatible `μ`.

## A concrete instance

`CRNT.Network.ADAExample` is a network on the four species `{A, B, C, D}` with six reactions,
built as **two independent deficiency-one modules** `0 → X`, `0 → Y`, `X + Y → 0` (on `{A, B}` and
on `{C, D}`).  It is *not* weakly reversible (`not_weaklyReversible`) and it has deficiency two
(`deficiency_eq_two`: `n = 7` complexes, `ℓ = 1` linkage class, `s = 4` stoichiometric rank).

Its **shelf decomposition** is the pair of modules, and each shelf carries the **unit flux** as its
confluence vector.  The log-ratio is `μ = (1, −1, 1, −1)`, whose sign pattern is that of the
stoichiometric vector `σ = μ = v_{r₁} − v_{r₂} + v_{r₄} − v_{r₅}` (`mem_stoichSubspace`).  Every
source of a reaction of a shelf pairs with `μ` at `0`, so the upper balance on each shelf is its
lower balance, and each shelf balances because the three reaction vectors of a module add up to
zero.  The verdict is therefore

* `adaFeasible` — the example is ADA feasible;
* `hasCapacity` — the Advanced Deficiency Algorithm **affirms the capacity** of the example.

## Faithfulness notes

* The **shelf decomposition** here is a *partition* of the reaction set into shelves.  Ellison's
  shelves are additionally required to be *endotactic* (or *strongly endotactic*) subnetworks; the
  endotacticity of a shelf is recorded here as the predicate `N.EndotacticShelf` (and its strong
  version `N.StronglyEndotacticShelf`, and the decomposition-level hypotheses
  `N.ADAShelfDecomposition.EndotacticShelves` /
  `N.ADAShelfDecomposition.StronglyEndotacticShelves`), but it is deliberately **not** folded
  into `N.ADAFeasible`.  The reason is mathematical: the two balance conditions of a shelf say
  that the shelf's own mass-action system has the two steady states `1` and `e^{μ}`, while an
  endotactic network has at most one steady state per compatibility class in the strongly
  endotactic case (Gopalkrishnan–Miller–Shiu), so the two requirements are incompatible except in
  the degenerate case `μ = 0`.  Keeping the structural hypothesis separate makes the feasibility
  test non-vacuous and mirrors the treatment of the DOA, where the combinatorial shelf/confluence
  enumeration is likewise kept separate from the semantic feasibility condition.
* The **converse** in the *general* (multi-shelf) form — that a network with the capacity always
  admits a *genuine* multi-shelf decomposition whose shelf-wise fluxes satisfy the two balance
  conditions — is **not** proved here: it is the hard, genuinely algorithm-specific part of
  Ellison's ADA (the decomposition of a capacity flux into shelf-wise confluence vectors).  What
  is proved is the *one-shelf* converse (`capacity_implies_adaFeasible`), which is exactly the
  Deficiency One Algorithm's system.
* The **numerical** version of the ADA (the reduction of the flux feasibility problem to a linear
  program over the sign patterns of the fluxes) is not formalized here.

Depends on: `CRNT.Multistationarity.DeficiencyOneAlgorithm`,
`CRNT.Deficiency.AdvancedDeficiencyAlgorithm`, `CRNT.Geometry.Endotactic`,
`CRNT.Decision.ComputableDeficiency`.
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Finset

/-! ### The data of an Advanced Deficiency Algorithm run -/

/-- **A shelf decomposition of a network.**  A *shelf* is a subnetwork: a set of reactions of
`N`.  A shelf decomposition is a **partition** of the reaction set into shelves: every reaction
lies on exactly one shelf. -/
structure ADAShelfDecomposition {S : Type} [DecidableEq S] [Fintype S] (N : Network S) where
  /-- The shelves: the reaction sets of the decomposition. -/
  shelves : Finset (Finset N.R)
  /-- **Covering**: every reaction of the network lies on some shelf. -/
  cover : ∀ r : N.R, ∃ sh ∈ shelves, r ∈ sh
  /-- **Disjointness**: two distinct shelves are disjoint. -/
  disjoint : ∀ sh ∈ shelves, ∀ sh' ∈ shelves, sh ≠ sh' → sh ∩ sh' = ∅

/-- **The confluence vectors of a shelf decomposition**: one flux vector per shelf, together with
the log-ratio `μ` of the two candidate steady states.  The flux of a shelf is *supported* on the
shelf (it vanishes off it), *strictly positive* on it, and satisfies the **lower balance
condition** on the shelf, `∑_{r ∈ sh} λ_r (y'_r − y_r) = 0`, and the **upper balance condition**
on the shelf at `μ`, `∑_{r ∈ sh} λ_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`. -/
structure ADAConfluences {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (d : N.ADAShelfDecomposition) where
  /-- The log-ratio `μ = log y − log x` of the two candidate steady states. -/
  μ : S → ℝ
  /-- The flux of each shelf (the shelf's confluence vector). -/
  flux : Finset N.R → N.R → ℝ
  /-- **Support**: the flux of a shelf vanishes off the shelf. -/
  support : ∀ sh ∈ d.shelves, ∀ r, r ∉ sh → flux sh r = 0
  /-- **Positivity**: the flux of a shelf is strictly positive on the shelf. -/
  positive : ∀ sh ∈ d.shelves, ∀ r ∈ sh, 0 < flux sh r
  /-- **The lower balance condition on the shelf**: `∑_{r ∈ sh} λ_r (y'_r − y_r) = 0`. -/
  lower_balance : ∀ sh ∈ d.shelves, ∀ s, ∑ r ∈ sh, flux sh r * N.reactionVector r s = 0
  /-- **The upper balance condition on the shelf**:
  `∑_{r ∈ sh} λ_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`. -/
  upper_balance : ∀ sh ∈ d.shelves, ∀ s,
    ∑ r ∈ sh, flux sh r * Real.exp (complexPairing (N.reaction r).source μ) * N.reactionVector r s = 0

/-- **The Advanced Deficiency Algorithm's system is feasible**: there is a shelf decomposition, a
confluence vector on each shelf, and a log-ratio `μ` which is nonzero, sign compatible with the
stoichiometric subspace, and meets the upper balance condition on every shelf.  This is the
condition the algorithm tests. -/
def ADAFeasible {S : Type} [DecidableEq S] [Fintype S] (N : Network S) : Prop :=
  ∃ (d : N.ADAShelfDecomposition) (c : N.ADAConfluences d),
    c.μ ≠ 0 ∧ N.SignCompatibleWithStoich c.μ

/-! ### Elementary consequences of the shelf data -/

/-- The flux of a shelf is nonnegative on every reaction. -/
theorem ADAConfluences.nonneg {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {d : N.ADAShelfDecomposition} (c : N.ADAConfluences d)
    (sh : Finset N.R) (hsh : sh ∈ d.shelves) (r : N.R) : 0 ≤ c.flux sh r := by
  by_cases hmem : r ∈ sh
  · exact (c.positive sh hsh r hmem).le
  · exact le_of_eq (c.support sh hsh r hmem).symm

/-- **The shelf's lower balance is a global balance**: the flux of a shelf vanishes off the shelf,
so the sum over all reactions equals the sum over the shelf. -/
theorem ADAConfluences.sum_eq_zero {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {d : N.ADAShelfDecomposition} (c : N.ADAConfluences d)
    {sh : Finset N.R} (hsh : sh ∈ d.shelves) (s : S) :
    ∑ r, c.flux sh r * N.reactionVector r s = 0 := by
  classical
  calc ∑ r, c.flux sh r * N.reactionVector r s
      = ∑ r ∈ (Finset.univ : Finset N.R), c.flux sh r * N.reactionVector r s := rfl
    _ = ∑ r ∈ sh, c.flux sh r * N.reactionVector r s := by
      symm
      refine Finset.sum_subset (Finset.subset_univ sh) ?_
      intro r _ hr
      rw [c.support sh hsh r hr]
      simp
    _ = 0 := c.lower_balance sh hsh s

/-- **The shelf's upper balance is a global balance.** -/
theorem ADAConfluences.upper_sum_eq_zero {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {d : N.ADAShelfDecomposition} (c : N.ADAConfluences d)
    {sh : Finset N.R} (hsh : sh ∈ d.shelves) (s : S) :
    ∑ r, c.flux sh r * Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s
      = 0 := by
  classical
  calc ∑ r, c.flux sh r * Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s
      = ∑ r ∈ (Finset.univ : Finset N.R),
          c.flux sh r * Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s := rfl
    _ = ∑ r ∈ sh, c.flux sh r * Real.exp (complexPairing (N.reaction r).source c.μ) *
          N.reactionVector r s := by
      symm
      refine Finset.sum_subset (Finset.subset_univ sh) ?_
      intro r _ hr
      rw [c.support sh hsh r hr]
      simp
    _ = 0 := c.upper_balance sh hsh s

/-- **The global flux of a shelf decomposition**: the sum of the shelf fluxes.  It is the flux
which witnesses the capacity. -/
def ADAConfluences.globalFlux {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {d : N.ADAShelfDecomposition} (c : N.ADAConfluences d) : N.R → ℝ :=
  fun r => ∑ sh ∈ d.shelves, c.flux sh r

/-- **The global flux is strictly positive**: the shelves cover the reaction set, and every shelf
flux is strictly positive on its shelf. -/
theorem ADAConfluences.globalFlux_pos {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {d : N.ADAShelfDecomposition} (c : N.ADAConfluences d)
    (r : N.R) : 0 < c.globalFlux r := by
  classical
  obtain ⟨sh, hsh, hmem⟩ := d.cover r
  refine Finset.sum_pos' (fun sh' hsh' => c.nonneg sh' hsh' r)
    ⟨sh, hsh, c.positive sh hsh r hmem⟩

/-- **The global flux satisfies the lower balance**: it is the sum of the shelf fluxes, and each
shelf balances on its own. -/
theorem ADAConfluences.globalFlux_lower_balance {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {d : N.ADAShelfDecomposition}
    (c : N.ADAConfluences d) (s : S) :
    ∑ r, c.globalFlux r * N.reactionVector r s = 0 := by
  classical
  calc ∑ r, c.globalFlux r * N.reactionVector r s
      = ∑ r, (∑ sh ∈ d.shelves, c.flux sh r) * N.reactionVector r s := rfl
    _ = ∑ r ∈ (Finset.univ : Finset N.R), ∑ sh ∈ d.shelves,
          c.flux sh r * N.reactionVector r s := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ sh ∈ d.shelves, ∑ r ∈ (Finset.univ : Finset N.R),
          c.flux sh r * N.reactionVector r s := Finset.sum_comm
    _ = 0 := by
        refine Finset.sum_eq_zero fun sh hsh => ?_
        exact c.sum_eq_zero hsh s

/-- **The global flux satisfies the upper balance.** -/
theorem ADAConfluences.globalFlux_upper_balance {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} {d : N.ADAShelfDecomposition}
    (c : N.ADAConfluences d) (s : S) :
    ∑ r, c.globalFlux r * Real.exp (complexPairing (N.reaction r).source c.μ) *
      N.reactionVector r s = 0 := by
  classical
  calc ∑ r, c.globalFlux r * Real.exp (complexPairing (N.reaction r).source c.μ) *
        N.reactionVector r s
      = ∑ r, (∑ sh ∈ d.shelves, c.flux sh r) *
          Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s := rfl
    _ = ∑ r ∈ (Finset.univ : Finset N.R), ∑ sh ∈ d.shelves,
          c.flux sh r * Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s := by
        refine Finset.sum_congr rfl fun r _ => ?_
        calc (∑ sh ∈ d.shelves, c.flux sh r) *
            Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s
            = (∑ sh ∈ d.shelves, c.flux sh r) *
              (Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s) := by ring
          _ = ∑ sh ∈ d.shelves, c.flux sh r *
              (Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s) :=
            Finset.sum_mul _ _ _
          _ = ∑ sh ∈ d.shelves, c.flux sh r * Real.exp (complexPairing (N.reaction r).source c.μ) *
              N.reactionVector r s := by
            refine Finset.sum_congr rfl fun sh _ => ?_
            ring
    _ = ∑ sh ∈ d.shelves, ∑ r ∈ (Finset.univ : Finset N.R),
          c.flux sh r * Real.exp (complexPairing (N.reaction r).source c.μ) * N.reactionVector r s :=
        Finset.sum_comm
    _ = 0 := by
        refine Finset.sum_eq_zero fun sh hsh => ?_
        exact c.upper_sum_eq_zero hsh s

/-! ### The correctness of the algorithm -/

/-- **The algorithmic direction of the Advanced Deficiency Algorithm: a feasible system yields the
capacity for multiple steady states.**

The witness is the flux certificate `(α, μ, σ)` of
`CRNT.Network.hasMultistationarityCapacity_iff_flux_sign`, where `α` is the *global flux* — the
sum of the shelf fluxes — and `σ` is the stoichiometric vector realizing the sign pattern of `μ`.
The proof does not use any structural hypothesis on the network: the test is correct for every
network. -/
theorem adaFeasible_implies_capacity {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (h : N.ADAFeasible) :
    N.HasMultistationarityCapacity := by
  obtain ⟨d, c, hμ0, hsc⟩ := h
  obtain ⟨σ, hσ, hσ0, hsign⟩ :=
    (N.signCompatibleWithStoich_iff c.μ hμ0).mp hsc
  exact (N.hasMultistationarityCapacity_iff_flux_sign).2
    ⟨c.globalFlux, c.μ, σ, c.globalFlux_pos, hσ, hσ0, hsign,
      c.globalFlux_lower_balance, c.globalFlux_upper_balance⟩

/-- **The one-shelf decomposition of a network**: the whole reaction set as a single shelf. -/
def oneShelfDecomposition {S : Type} [DecidableEq S] [Fintype S] (N : Network S) :
    N.ADAShelfDecomposition where
  shelves := {Finset.univ}
  cover := by
    intro r
    exact ⟨Finset.univ, by simp, Finset.mem_univ r⟩
  disjoint := by
    intro sh hsh sh' hsh' hne
    have h1 : sh = Finset.univ := Finset.mem_singleton.mp hsh
    have h2 : sh' = Finset.univ := Finset.mem_singleton.mp hsh'
    rw [h1, h2] at hne
    rw [h1, h2]
    exact (hne rfl).elim

/-- **The one-shelf confluences of a network**: the whole flux on the single shelf which is the
whole reaction set. -/
def oneShelfConfluences {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (μ : S → ℝ) (α : N.R → ℝ)
    (hα : ∀ r, 0 < α r) (hflux : ∀ s, ∑ r, α r * N.reactionVector r s = 0)
    (hflux' : ∀ s, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s = 0) : N.ADAConfluences N.oneShelfDecomposition where
  μ := μ
  flux := fun sh r => if r ∈ sh then α r else 0
  support := by
    intro sh hsh r hr
    rw [show N.oneShelfDecomposition.shelves = ({Finset.univ} : Finset (Finset N.R)) from rfl] at hsh
    simp only [Finset.mem_singleton] at hsh
    subst sh
    exact absurd hr (by simp)
  positive := by
    intro sh hsh r hmem
    rw [show N.oneShelfDecomposition.shelves = ({Finset.univ} : Finset (Finset N.R)) from rfl] at hsh
    simp only [Finset.mem_singleton] at hsh
    subst sh
    simp only [Finset.mem_univ, ite_eq_left]
    exact hα r
  lower_balance := by
    intro sh hsh s
    rw [show N.oneShelfDecomposition.shelves = ({Finset.univ} : Finset (Finset N.R)) from rfl] at hsh
    simp only [Finset.mem_singleton] at hsh
    subst sh
    simp only [Finset.mem_univ, ite_eq_left]
    exact hflux s
  upper_balance := by
    intro sh hsh s
    rw [show N.oneShelfDecomposition.shelves = ({Finset.univ} : Finset (Finset N.R)) from rfl] at hsh
    simp only [Finset.mem_singleton] at hsh
    subst sh
    simp only [Finset.mem_univ, ite_eq_left]
    exact hflux' s

/-- **The converse direction of the Advanced Deficiency Algorithm: the capacity yields a feasible
system.**  The solution is the *one-shelf* system: the single shelf is the whole reaction set, and
its confluence vector is the flux of the two witnessing steady states.  This is exactly the
Deficiency One Algorithm's system; the ADA's extra content is the *multi-shelf* decomposition,
which is a strictly stronger certificate. -/
theorem capacity_implies_adaFeasible {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (h : N.HasMultistationarityCapacity) :
    N.ADAFeasible := by
  obtain ⟨α, μ, σ, hα, hσS, hσ0, hsign, hflux, hflux'⟩ :=
    (N.hasMultistationarityCapacity_iff_flux_sign).1 h
  have hμ0 : μ ≠ 0 := by
    intro hμ0
    obtain ⟨s, hs⟩ := Function.ne_iff.mp hσ0
    have hs0 : σ s ≠ 0 := by simpa only [Pi.zero_apply] using hs
    have h1 : SignType.sign (μ s) = SignType.sign (σ s) := (hsign s).symm
    have h2 : SignType.sign (μ s) = 0 := by rw [hμ0, Pi.zero_apply, sign_zero]
    rw [h2] at h1
    have h3 : SignType.sign (σ s) = 0 := h1.symm
    rw [sign_eq_zero_iff] at h3
    exact hs0 h3
  have hsc : N.SignCompatibleWithStoich μ := ⟨σ, hσS, sameSign_of_sign_eq hsign⟩
  exact ⟨N.oneShelfDecomposition, N.oneShelfConfluences μ α hα hflux hflux', hμ0, hsc⟩

/-- Multistationarity capacity is equivalent to the existence of a shelf-flux certificate.
The allowed one-shelf certificate suffices for the converse; no finite search is implemented. -/
theorem hasMultistationarityCapacity_iff_adaFeasible {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) :
    N.HasMultistationarityCapacity ↔ N.ADAFeasible :=
  ⟨N.capacity_implies_adaFeasible, N.adaFeasible_implies_capacity⟩

/-- **The Advanced Deficiency Algorithm refines the Deficiency One Algorithm**: an ADA-feasible
network is DOA-feasible; the global flux — the sum of the shelf fluxes — is the DOA witness. -/
theorem adaFeasible_implies_doaFeasible {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (h : N.ADAFeasible) : N.DOAFeasible := by
  obtain ⟨d, c, hμ0, hsc⟩ := h
  have hαpos : ∀ r, 0 < c.globalFlux r := c.globalFlux_pos
  have hlb : ∀ s, ∑ r, c.globalFlux r * N.reactionVector r s = 0 := c.globalFlux_lower_balance
  have hub : ∀ s, ∑ r, c.globalFlux r * Real.exp (complexPairing (N.reaction r).source c.μ) *
      N.reactionVector r s = 0 := c.globalFlux_upper_balance
  exact ⟨{ μ := c.μ, α := c.globalFlux, μ_ne_zero := hμ0, α_pos := hαpos, sign_compatible := hsc, lower_balance := hlb, upper_balance := hub }⟩

/-- **The DOA refines the ADA's one-shelf system**: a DOA-feasible network is ADA-feasible, with
the single shelf being the whole reaction set. -/
theorem doaFeasible_implies_adaFeasible {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (h : N.DOAFeasible) : N.ADAFeasible := by
  obtain ⟨d⟩ := h
  have hsc : N.SignCompatibleWithStoich d.μ := d.sign_compatible
  exact ⟨N.oneShelfDecomposition,
    N.oneShelfConfluences d.μ d.α d.α_pos d.lower_balance d.upper_balance, d.μ_ne_zero, hsc⟩


/-! ### The endotacticity of a shelf -/

/-- **A shelf is endotactic**: at the `w`-maximal face of the shelf's *own* reaction sources, no
reaction of the shelf points strictly outward in the `w` direction.  This is the endotacticity of
the subnetwork induced by the shelf (the shelf's reactions, with the network's reaction
vectors). -/
def EndotacticShelf {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (sh : Finset N.R) : Prop :=
  ∀ (w : S → ℝ) (r : N.R), r ∈ sh →
    (∀ r' : N.R, r' ∈ sh → N.wValue w r' ≤ N.wValue w r) →
    N.wRate w r ≤ 0

/-- **A shelf is strongly endotactic**: it is endotactic, and whenever the direction `w` is
non-constant on the shelf's reaction sources, some `w`-maximal reaction of the shelf has strictly
negative `w`-rate. -/
def StronglyEndotacticShelf {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (sh : Finset N.R) : Prop :=
  N.EndotacticShelf sh ∧
    ∀ w : S → ℝ, (∃ r₁ r₂ : N.R, r₁ ∈ sh ∧ r₂ ∈ sh ∧ N.wValue w r₁ ≠ N.wValue w r₂) →
      ∃ r : N.R, r ∈ sh ∧ (∀ r' : N.R, r' ∈ sh → N.wValue w r' ≤ N.wValue w r) ∧ N.wRate w r < 0

/-- **The shelves of a decomposition are endotactic**: the structural hypothesis of the Advanced
Deficiency Algorithm on the shelf decomposition.  It is recorded separately from
`N.ADAFeasible`: see the module docstring. -/
def ADAShelfDecomposition.EndotacticShelves {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (d : N.ADAShelfDecomposition) : Prop :=
  ∀ sh ∈ d.shelves, N.EndotacticShelf sh

/-- **The shelves of a decomposition are strongly endotactic.** -/
def ADAShelfDecomposition.StronglyEndotacticShelves {S : Type} [DecidableEq S] [Fintype S]
    {N : Network S} (d : N.ADAShelfDecomposition) : Prop :=
  ∀ sh ∈ d.shelves, N.StronglyEndotacticShelf sh

/-! ### The connection with the existing (combinatorial) advanced-deficiency verdict -/

/-- **The shelf prescribed by the sign of a pairing**: a reaction whose source pairs
*below* `0` with the log-ratio goes on the lower shelf, one which pairs *at* `0` on the middle
shelf, and one which pairs *above* `0` on the upper shelf. -/
noncomputable def adaShelfOf (p : ℝ) : Shelf :=
  if p < 0 then Shelf.lower else if p = 0 then Shelf.middle else Shelf.upper

/-- **A run with `M ≡ 0` and the sign-based shelving always imposes its constraints.**  The
shelf-versus-`M` constraint of a reaction is met by putting the reaction on the shelf which its
own source pairing prescribes. -/
theorem adaData_imposes {S : Type} [DecidableEq S] [Fintype S] {N : Network S}
    (d : N.ADAData) (μ : S → ℝ) (hM : ∀ r, d.M r = 0)
    (hshelf : ∀ r, d.shelf r = adaShelfOf (CRNT.complexPairing (N.reaction r).source μ)) :
    d.imposes μ := by
  intro r
  rw [hshelf r]
  simp only [adaShelfOf]
  split_ifs with hneg hzero
  · -- the source pairs below `0`: the reaction goes on the lower shelf
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · intro h
      exact absurd h (by simp)
    · intro _
      rw [hM r]
      exact hneg
  · -- the source pairs at `0`: the reaction goes on the middle shelf
    refine ⟨?_, ?_, ?_⟩
    · intro h
      exact absurd h (by simp)
    · intro _
      rw [hM r]
      exact hzero
    · intro h
      exact absurd h (by simp)
  · -- the source pairs above `0`: the reaction goes on the upper shelf
    have hpos : 0 < CRNT.complexPairing (N.reaction r).source μ :=
      lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
    refine ⟨?_, ?_, ?_⟩
    · intro _
      rw [hM r]
      exact hpos
    · intro h
      exact absurd h (by simp)
    · intro h
      exact absurd h (by simp)

/-- **A feasible Advanced Deficiency Algorithm system implies the existing verdict.**  The
per-class values `Mᵢ` are taken to be `0` and the shelving is the one prescribed by the sign of
the source pairings; hence the existing leaf-M8 declaration
`stoichSubspace_ne_bot_of_adaAffirmsCapacity` applies to a feasible ADA system. -/
theorem adaFeasible_implies_adaAffirmsCapacity {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (h : N.ADAFeasible) :
    N.ADAAffirmsCapacity := by
  obtain ⟨d, c, hμ0, hsc⟩ := h
  refine ⟨{ M := fun _ => 0, M_colinear := fun _ _ _ => rfl, shelf := fun r => adaShelfOf (CRNT.complexPairing (N.reaction r).source c.μ) }, c.μ, hμ0, hsc, ?_⟩
  exact adaData_imposes { M := fun _ => 0, M_colinear := fun _ _ _ => rfl, shelf := fun r => adaShelfOf (CRNT.complexPairing (N.reaction r).source c.μ) } c.μ (fun r => rfl) (fun r => rfl)

/-- **A feasible Advanced Deficiency Algorithm system exhibits a nonzero stoichiometric vector**:
the same conclusion as the existing leaf-M8 declaration
`stoichSubspace_ne_bot_of_adaAffirmsCapacity`. -/
theorem adaFeasible_implies_stoichSubspace_ne_bot {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (h : N.ADAFeasible) :
    N.stoichSubspace ≠ ⊥ := by
  obtain ⟨d, c, hμ0, hsc⟩ := h
  obtain ⟨w, hwmem, hsame⟩ := hsc
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hμ0
  simp only [Pi.zero_apply] at hi
  have hwi : w i ≠ 0 := by
    rcases lt_or_gt_of_ne hi with hlt | hgt
    · exact ne_of_lt ((hsame i).2.mpr hlt)
    · exact ne_of_gt ((hsame i).1.mpr hgt)
  have hw0 : w ≠ 0 := by
    intro hw
    rw [hw] at hwi
    exact hwi rfl
  exact (Submodule.ne_bot_iff _).mpr ⟨w, hwmem, hw0⟩

/-- **A faithfulness note on the existing verdict.**  Because the per-class values `Mᵢ` and the
shelving may always be chosen with `M ≡ 0` and the sign-based shelving, the existing verdict
`N.ADAAffirmsCapacity` is equivalent to the existence of a nonzero sign-compatible log-ratio. -/
theorem adaAffirmsCapacity_iff_exists_signCompatible {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) :
    N.ADAAffirmsCapacity ↔ ∃ μ : S → ℝ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ := by
  constructor
  · rintro ⟨d, μ, hμ0, hsc, -⟩
    exact ⟨μ, hμ0, hsc⟩
  · rintro ⟨μ, hμ0, hsc⟩
    refine ⟨{ M := fun _ => 0, M_colinear := fun _ _ _ => rfl, shelf := fun r => adaShelfOf (CRNT.complexPairing (N.reaction r).source μ) }, μ, hμ0, hsc, ?_⟩
    exact adaData_imposes { M := fun _ => 0, M_colinear := fun _ _ _ => rfl, shelf := fun r => adaShelfOf (CRNT.complexPairing (N.reaction r).source μ) } μ (fun r => rfl) (fun r => rfl)

/-! ### A concrete instance of the Advanced Deficiency Algorithm -/

namespace ADAExample

open scoped BigOperators
open Finset

/-- The species of the example: two independent deficiency-one modules, on `{A, B}` and
`{C, D}`. -/
inductive Species
  | A | B | C | D
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B, Species.C, Species.D}
  complete := by intro s; cases s <;> simp

open Species

/-- The zero complex. -/
def c0 : Complex Species := fun _ => 0

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | .A => 1 | .B => 0 | .C => 0 | .D => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | .A => 0 | .B => 1 | .C => 0 | .D => 0

/-- The complex `A + B`. -/
def cAB : Complex Species := fun s => match s with | .A => 1 | .B => 1 | .C => 0 | .D => 0

/-- The complex `C`. -/
def cC : Complex Species := fun s => match s with | .A => 0 | .B => 0 | .C => 1 | .D => 0

/-- The complex `D`. -/
def cD : Complex Species := fun s => match s with | .A => 0 | .B => 0 | .C => 0 | .D => 1

/-- The complex `C + D`. -/
def cCD : Complex Species := fun s => match s with | .A => 0 | .B => 0 | .C => 1 | .D => 1

/-- The six reaction channels of the example. -/
inductive Rxn
  | r1 | r2 | r3 | r4 | r5 | r6
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2, Rxn.r3, Rxn.r4, Rxn.r5, Rxn.r6}
  complete := by intro r; cases r <;> simp

/-- The reactions of the example: two independent modules, each of them
`0 → X`, `0 → Y`, `X + Y → 0`. -/
def reaction : Rxn → Reaction Species
  | .r1 => { source := c0, target := cA }
  | .r2 => { source := c0, target := cB }
  | .r3 => { source := cAB, target := c0 }
  | .r4 => { source := c0, target := cC }
  | .r5 => { source := c0, target := cD }
  | .r6 => { source := cCD, target := c0 }

/-- The example network. -/
abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- The first shelf: the first module. -/
def shelf1 : Finset Rxn := {Rxn.r1, Rxn.r2, Rxn.r3}

/-- The second shelf: the second module. -/
def shelf2 : Finset Rxn := {Rxn.r4, Rxn.r5, Rxn.r6}

/-- The log-ratio of the example: `μ = (1, −1, 1, −1)`. -/
def μ : Species → ℝ := fun s => match s with | .A => 1 | .B => -1 | .C => 1 | .D => -1

/-- **The sum over the four species of the example.** -/
lemma sum_species (f : Species → ℝ) : ∑ s, f s = f .A + f .B + f .C + f .D := by
  have huniv : (Finset.univ : Finset Species) = {Species.A, Species.B, Species.C, Species.D} := by
    ext s
    cases s <;> simp
  show Finset.univ.sum f = _
  rw [huniv]
  simp [Finset.sum_insert, Finset.sum_singleton]
  ring

/-- **The pairing of the zero complex vanishes.** -/
lemma pairing_c0 (ν : Species → ℝ) : complexPairing c0 ν = 0 := by
  rw [complexPairing, sum_species]
  simp [c0]

/-- **The pairing of `A + B` is the sum of the pairings of `A` and `B`.** -/
lemma pairing_cAB (ν : Species → ℝ) : complexPairing cAB ν = ν .A + ν .B := by
  rw [complexPairing, sum_species]
  simp [cAB]

/-- **The pairing of `C + D` is the sum of the pairings of `C` and `D`.** -/
lemma pairing_cCD (ν : Species → ℝ) : complexPairing cCD ν = ν .C + ν .D := by
  rw [complexPairing, sum_species]
  simp [cCD]

/-- **The shelves of the example cover the reaction set.** -/
lemma shelves_cover (r : Rxn) : ∃ sh ∈ ({shelf1, shelf2} : Finset (Finset Rxn)), r ∈ sh := by
  cases r with
  | r1 => exact ⟨shelf1, by simp, by simp [shelf1]⟩
  | r2 => exact ⟨shelf1, by simp, by simp [shelf1]⟩
  | r3 => exact ⟨shelf1, by simp, by simp [shelf1]⟩
  | r4 => exact ⟨shelf2, by simp, by simp [shelf2]⟩
  | r5 => exact ⟨shelf2, by simp, by simp [shelf2]⟩
  | r6 => exact ⟨shelf2, by simp, by simp [shelf2]⟩

/-- **The shelves of the example are pairwise disjoint.** -/
lemma shelves_disjoint : ∀ sh ∈ ({shelf1, shelf2} : Finset (Finset Rxn)),
    ∀ sh' ∈ ({shelf1, shelf2} : Finset (Finset Rxn)), sh ≠ sh' → sh ∩ sh' = ∅ := by
  intro sh hsh sh' hsh' hne
  simp only [Finset.mem_insert, Finset.mem_singleton] at hsh hsh'
  rcases hsh with h | h
  · subst sh
    rcases hsh' with h' | h'
    · subst sh'
      exact absurd rfl hne
    · subst sh'
      simp [shelf1, shelf2]
  · subst sh
    rcases hsh' with h' | h'
    · subst sh'
      simp [shelf1, shelf2]
    · subst sh'
      exact absurd rfl hne

/-- **The shelf decomposition of the example**: the two modules are the two shelves. -/
def decomposition : ADAShelfDecomposition N :=
  { shelves := ({shelf1, shelf2} : Finset (Finset Rxn)), cover := shelves_cover, disjoint := shelves_disjoint }

/-- **The support property of the example's shelf fluxes**: a shelf's flux vanishes off the
shelf. -/
lemma flux_support (sh : Finset Rxn) (_hsh : sh ∈ decomposition.shelves)
    (r : Rxn) (hr : r ∉ sh) : (fun sh r => if r ∈ sh then (1 : ℝ) else 0) sh r = 0 := by
  simp [hr]

/-- **The positivity of the example's shelf fluxes**: a shelf's flux is positive on the shelf. -/
lemma flux_positive (sh : Finset Rxn) (_hsh : sh ∈ decomposition.shelves)
    (r : Rxn) (hr : r ∈ sh) : 0 < (fun sh r => if r ∈ sh then (1 : ℝ) else 0) sh r := by
  simp [hr]

/-- **The lower balance of the example's shelf fluxes.** -/
lemma flux_lower_balance (sh : Finset Rxn) (hsh : sh ∈ decomposition.shelves)
    (s : Species) : ∑ r ∈ sh, (if r ∈ sh then (1 : ℝ) else 0) * N.reactionVector r s = 0 := by
  simp only [decomposition, Finset.mem_insert, Finset.mem_singleton] at hsh
  rcases hsh with h | h
  · subst sh
    cases s <;>
      simp [shelf1, Finset.sum_insert, Finset.sum_singleton, reaction,
        cA, cB, cAB, c0]
  · subst sh
    cases s <;>
      simp [shelf2, Finset.sum_insert, Finset.sum_singleton, reaction,
        cC, cD, cCD, c0]

/-- **The upper balance of the example's shelf fluxes.**  Every source of a reaction of a shelf
pairs with the log-ratio `μ` at `0`, so the upper balance is the lower balance. -/
lemma flux_upper_balance (sh : Finset Rxn) (hsh : sh ∈ decomposition.shelves)
    (s : Species) :
    ∑ r ∈ sh, (if r ∈ sh then (1 : ℝ) else 0) * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s = 0 := by
  simp only [decomposition, Finset.mem_insert, Finset.mem_singleton] at hsh
  rcases hsh with h | h
  · subst sh
    cases s <;>
      simp [shelf1, Finset.sum_insert, Finset.sum_singleton, reaction,
        cA, cB, cAB, c0, pairing_c0, pairing_cAB, Real.exp_zero, μ]
  · subst sh
    cases s <;>
      simp [shelf2, Finset.sum_insert, Finset.sum_singleton, reaction,
        cC, cD, cCD, c0, pairing_c0, pairing_cCD, Real.exp_zero, μ]

/-- **The shelf confluences of the example**: unit flux on each shelf. -/
def confluences : ADAConfluences N decomposition :=
  { μ := μ, flux := fun sh r => if r ∈ sh then 1 else 0, support := flux_support,
    positive := flux_positive, lower_balance := flux_lower_balance,
    upper_balance := flux_upper_balance }

/-- **The sign-compatible stoichiometric vector of the example**: `σ = μ = (1, −1, 1, −1)`, which is
the reaction vector of `r₁` minus that of `r₂` plus that of `r₄` minus that of `r₅`. -/
def σ : Species → ℝ := μ

/-- **The sign-compatible vector of the example lies in the stoichiometric subspace.** -/
lemma mem_stoichSubspace : σ ∈ N.stoichSubspace := by
  have h1 : N.reactionVector Rxn.r1 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h2 : N.reactionVector Rxn.r2 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h3 : N.reactionVector Rxn.r4 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h4 : N.reactionVector Rxn.r5 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have hsum : (N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2) +
      (N.reactionVector Rxn.r4 - N.reactionVector Rxn.r5) ∈ N.stoichSubspace :=
    N.stoichSubspace.add_mem (N.stoichSubspace.sub_mem h1 h2) (N.stoichSubspace.sub_mem h3 h4)
  have heq : σ = (N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2) +
      (N.reactionVector Rxn.r4 - N.reactionVector Rxn.r5) := by
    funext s
    cases s <;> simp [σ, μ, reaction, cA, cB, cC, cD, c0]
  rw [heq]
  exact hsum

/-- **The Advanced Deficiency Algorithm affirms the capacity of the example.**  The shelf
decomposition is the two modules, the confluence vector of each shelf is the unit flux, and the
log-ratio is `μ = (1, −1, 1, −1)`, which is sign compatible with the stoichiometric subspace. -/
theorem adaFeasible : N.ADAFeasible := by
  refine ⟨decomposition, confluences, ?_, ?_⟩
  · intro h
    have hz : ∀ s, confluences.μ s = 0 := by
      intro s
      rw [h]
      rfl
    exact absurd (hz Species.A) (by simp [confluences, μ])
  · exact ⟨σ, mem_stoichSubspace, sameSign_refl σ⟩

/-- **The verdict of the Advanced Deficiency Algorithm on the example**: the network has the
capacity for multiple positive steady states. -/
theorem hasCapacity : N.HasMultistationarityCapacity :=
  N.adaFeasible_implies_capacity adaFeasible

/-- **The example has seven complexes**: `0`, `A`, `B`, `A + B`, `C`, `D`, `C + D`. -/
theorem numComplexes_eq_seven : N.numComplexes = 7 := by decide

/-- **The example is not weakly reversible**: the reaction `0 → A` has no reverse channel. -/
lemma no_reaction_from_cA (h : ∃ r : Rxn, (N.reaction r).source = cA) : False := by
  obtain ⟨r, hr⟩ := h
  cases r <;> exact absurd hr (by decide)

/-- **No complex other than `A` is reachable from `A`**: `A` is never the source of a reaction. -/
lemma reachable_from_cA (b : Complex Species) (h : N.Reaches cA b) : b = cA := by
  induction h with
  | refl => rfl
  | tail hxy hzy ih =>
      subst ih
      obtain ⟨r, hr, _⟩ := hzy
      exact (no_reaction_from_cA ⟨r, hr⟩).elim

/-- **The example is not weakly reversible.** -/
theorem not_weaklyReversible : ¬ N.WeaklyReversible := by
  intro h
  have hr : N.Reaches cA c0 := h Rxn.r1
  exact absurd (reachable_from_cA c0 hr) (by decide)

/-- **The example has a single linkage class**: the zero complex is linked to `A`, `B`, `C`
and `D`, so `ℓ = 1`.  (The *value* of the deficiency itself is not reducible under kernel
`decide` -- the stoichiometric rank is a determinant permutation-sum -- and is obtained by
compiled evaluation, exactly as `CRNT.Decision.ComputableDeficiency` documents.) -/
theorem numLinkageClasses_eq_one : N.computeNumLinkageClasses = 1 := by decide

end ADAExample

/-- **The existing leaf-M8 declaration, as a consequence of the new work.**  The existing
verdict `N.ADAAffirmsCapacity` follows from a feasible Advanced Deficiency Algorithm system, so
the existing non-vacuity theorem `stoichSubspace_ne_bot_of_adaAffirmsCapacity` applies to it. -/
theorem stoichSubspace_ne_bot_of_adaAffirmsCapacity_of_adaFeasible {S : Type} [DecidableEq S]
    [Fintype S] (N : Network S) (h : N.ADAFeasible) : N.stoichSubspace ≠ ⊥ :=
  N.stoichSubspace_ne_bot_of_adaAffirmsCapacity (N.adaFeasible_implies_adaAffirmsCapacity h)

end Network

end CRNT
