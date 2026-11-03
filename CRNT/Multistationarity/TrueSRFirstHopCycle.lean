import CRNT.Multistationarity.TrueChemistrySRCriterion
import CRNT.Multistationarity.TrueSRFirstHop

/-!
# The first hop out of an on-cycle species is the leftEdge step

This module restates the pure combinatorics of `CRNT.Multistationarity.TrueSRFirstHop` at the
level of the true-chemistry SR graph of `CRNT.Multistationarity.TrueChemistrySRGraph`, i.e. in
the exact vocabulary of `Network.TrueSRCycle` and
`Network.TrueInternalAggregateCausalEdge`.

It exists because the residue comment of
`CRNT/Multistationarity/TrueChemistrySRCriterion.lean:8600-8607` asserts a fact about first hops
that is (a) misattributed to `hopp` and (b) misstated as to target.  See
`research/routes/firsthop.md`.

## Main statements

`Network.oneStep_fromCycleSpecies_eq_leftEdge`:

> Let `C` be a true-SR cycle in a reactant/product-separated network satisfying the strong SR
> criterion.  Let `s` be a cycle species with `s = C.species j`.  If the aggregate causal edge out
> of `s` lands on a *cycle* reaction class, that class is `C.reaction j`, i.e. the hop is the
> single leftEdge step `s → C.reaction j`.

`Network.leftEdge_step_exists` is the existence half, and
`Network.onCycle_out_neighbour_leftEdge` packages both directions.
`Network.no_oneStep_to_pos_of_cycleSpecies` is the machine-checked refutation of the residue
comment's stated target.

**Scope note.** `hopp` is *not* a hypothesis of `oneStep_fromCycleSpecies_eq_leftEdge`; it is
needed only for `leftEdge_step_exists` and for the mirror direction.  The forcing comes from
`hcausal` (line 8036) plus the non-neighbour cycle-class flux vanishing (the negated `hnc` at
line 8537, packaged here as `nonneighbour_cycleClassFlux_eq_zero`).
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The non-neighbour cycle-class flux vanishing at the residue, from `¬hnc`
(`TrueChemistrySRCriterion.lean:8537`) via `nonAdjacent_cycleClassFlux_eq_zero`
(`TrueChemistrySRCriterion.lean:6979`). -/
theorem nonneighbour_cycleClassFlux_eq_zero (N : Network S)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (a b : Fin n) (h1 : a.1 ≠ b.1) (h2 : b.1 ≠ (a.1 + 1) % n) :
    N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0 := by
  rw [nonAdjacent_cycleClassFlux_eq_zero N hsep hSR C hC b a h1 h2.symm]
  exact zero_mul _

/-- The reaction class `C.reaction j` is active for the aggregate causal graph at the cycle
species `C.species j`: its class flux there is nonzero and the species is active.  This is the
subtype datum `N.ActiveAggregateTrueReaction` requires, discharged from `hopp` at `j`. -/
theorem cycleReaction_active_at_cycleSpecies (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n)
    (hopp : ∀ i : Fin n, N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)) < 0)
    (j : Fin n) (hσ : σ (C.species j) ≠ 0) :
    ∃ s : S, σ s ≠ 0 ∧ N.trueInternalClassFlux α (C.reaction j) s ≠ 0 := by
  refine ⟨C.species j, hσ, ?_⟩
  intro hz
  have h := CRNT.hopp_at
    (φ := fun a b => N.trueInternalClassFlux α (C.reaction a) (C.species b))
    (σs := fun b => σ (C.species b)) hopp j
  rw [hz, zero_mul] at h
  exact lt_irrefl 0 h

/-- **The first hop out of an on-cycle species that lands on the cycle is the leftEdge step.**

Let `s` be the cycle species `C.species j`.  If a species-to-reaction aggregate causal edge out
of `s` lands on a cycle reaction class `ρ`, then `ρ = C.reaction j`: the edge is
`C.leftEdge j`, whose species is `C.species j` and whose reaction is `C.reaction j`
(`TrueChemistrySRGraph.lean:141-144`).

Hypotheses (all in scope at `TrueChemistrySRCriterion.lean:8600`, see `research/routes/firsthop.md`):

* `hzero` — non-neighbour cycle-class fluxes vanish; see
  `nonneighbour_cycleClassFlux_eq_zero` for the packaged form.
* `hcausal` — line 8036.
* `hopp` is **not** needed for this direction; it is needed for the mirror
  (`CRNT.hop_backward_forced`) and for existence (`leftEdge_step_exists`). -/
theorem oneStep_fromCycleSpecies_eq_leftEdge (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n)
    (hzero : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n →
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)))
    (j : Fin n) {s : AggregateActiveSpecies σ} (hs : s.1 = C.species j)
    {ρ : N.ActiveAggregateTrueReaction α σ} (hρC : C.HasReaction ρ.1)
    (h : N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ)) :
    ρ.1 = C.reaction j := by
  classical
  change N.trueInternalClassFlux α ρ.1 s.1 * σ s.1 < 0 at h
  obtain ⟨a, ha⟩ := hρC
  have hfa : a = j := CRNT.firstHop_forced_leftEdge
    (φ := fun x y => N.trueInternalClassFlux α (C.reaction x) (C.species y))
    (σs := fun y => σ (C.species y)) hzero hcausal j a (by
      rw [← hs, ha]
      exact h)
  exact ha.symm.trans (congrArg C.reaction hfa)

/-- **Existence of the one-hop leftEdge step.**  `hopp` re-indexed at `j` says the cycle's left
incidence at `j` carries a strictly negative species-times-flux term, i.e. it *is* a
species-to-reaction aggregate causal edge `C.species j → C.reaction j`. -/
theorem leftEdge_step_exists (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n)
    (hopp : ∀ i : Fin n, N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)) < 0)
    (j : Fin n) (hσ : σ (C.species j) ≠ 0) :
    N.TrueInternalAggregateCausalEdge
      (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ))
      (Sum.inr ⟨C.reaction j, cycleReaction_active_at_cycleSpecies N C hopp j hσ⟩) := by
  change N.trueInternalClassFlux α (C.reaction j) (C.species j) * σ (C.species j) < 0
  exact CRNT.hopp_at
    (φ := fun x y => N.trueInternalClassFlux α (C.reaction x) (C.species y))
    (σs := fun y => σ (C.species y)) hopp j

/-- **Both directions of the forcing, together.**

The aggregate causal out-neighbours of the cycle species `C.species j` that are cycle reaction
classes form exactly the singleton `{C.reaction j}`.  The `⊆` direction is
`oneStep_fromCycleSpecies_eq_leftEdge`; the `⊇` direction is `hopp` re-indexed at `j`.

Consequently: if all out-neighbours of `s` are on the cycle, then the unique one-step
species-to-reaction route out of `s` is `C.leftEdge j`, and no other cycle reaction is reachable
in one hop.  Any longer on-cycle route advances the cycle index by one per hop
(`CRNT.two_hop_onCycle`), so the on-cycle distance from `C.species j` to `C.reaction a` is never
`1` unless `a = j`. -/
theorem onCycle_out_neighbour_leftEdge (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n)
    (hzero : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n →
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)))
    (hopp : ∀ i : Fin n, N.trueInternalClassFlux α (C.reaction (finRotate n i))
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)) < 0)
    (j : Fin n) (hσ : σ (C.species j) ≠ 0) :
    (∀ {ρ : N.ActiveAggregateTrueReaction α σ}, C.HasReaction ρ.1 →
        N.TrueInternalAggregateCausalEdge
          (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ)) (Sum.inr ρ) →
        ρ.1 = C.reaction j) ∧
      N.TrueInternalAggregateCausalEdge
        (Sum.inl (⟨C.species j, hσ⟩ : AggregateActiveSpecies σ))
        (Sum.inr ⟨C.reaction j, cycleReaction_active_at_cycleSpecies N C hopp j hσ⟩) := by
  refine ⟨fun {ρ} hρC h =>
    oneStep_fromCycleSpecies_eq_leftEdge N C hzero hcausal j rfl hρC h, ?_⟩
  exact leftEdge_step_exists N C hopp j hσ

/-- **Refutation, at CRNT level, of the residue comment's stated target.**

`TrueChemistrySRCriterion.lean:8603` says the first hop is "`s₀ → C.reaction (pos s₀)`", where
`pos s₀` is fixed by `s₀ = C.species (finRotate n i)` (line 8052) and endpoint
`qC.1 = C.reaction i` (line 8219), i.e. `pos (C.species j) = (finRotate n).symm j`.

That hop does not exist: the only on-cycle target of a one-hop out of `C.species j` is
`C.reaction j`, and for a nontrivial cycle `j ≠ (finRotate n).symm j`. -/
theorem no_oneStep_to_pos_of_cycleSpecies (N : Network S)
    {n : ℕ} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}
    (C : N.TrueSRCycle n) (hn2 : 2 ≤ n)
    (hzero : ∀ a b : Fin n, a.1 ≠ b.1 → b.1 ≠ (a.1 + 1) % n →
      N.trueInternalClassFlux α (C.reaction a) (C.species b) * σ (C.species b) = 0)
    (hcausal : ∀ i : Fin n, 0 < N.trueInternalClassFlux α (C.reaction i)
      (C.species (finRotate n i)) * σ (C.species (finRotate n i)))
    (j : Fin n) {ρ : N.ActiveAggregateTrueReaction α σ}
    (hρpos : ρ.1 = C.reaction ((finRotate n).symm j))
    (hρC : C.HasReaction ρ.1) {s : AggregateActiveSpecies σ} (hs : s.1 = C.species j)
    (h : N.TrueInternalAggregateCausalEdge (Sum.inl s) (Sum.inr ρ)) : False := by
  have heq := oneStep_fromCycleSpecies_eq_leftEdge N C hzero hcausal j hs hρC h
  have hij : j = (finRotate n).symm j := by
    apply C.reaction_injective
    rw [← heq, hρpos]
  exact (CRNT.finRotate_ne_self hn2 j)
    ((CRNT.rot_of_symm_apply (e := finRotate n) (a := j) (b := j) hij.symm).symm)

end Network
end CRNT