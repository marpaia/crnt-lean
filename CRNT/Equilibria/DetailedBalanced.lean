import CRNT.Dynamics.MassActionAlgebra
import CRNT.Graph.Reversibility
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Detailed balance

Detailed balance is stronger than complex balance.  At a concentration `x`, it asks
that the total mass-action flux from every complex `c` to every complex `d` equal
the total flux in the reverse direction.

The definition is deliberately **aggregate over reaction channels**.  `Network`
permits parallel reactions, so defining detailed balance by choosing one distinguished
reverse reaction would add non-canonical data.  The pair-flux formulation is invariant
under splitting or merging parallel channels and is the standard reaction-graph notion.

Main results:

* `pairFlux` -- total flux from one complex to another;
* `outflow_eq_sum_pairFlux` / `inflow_eq_sum_pairFlux` -- decompose complex flow into
  pairwise complex fluxes;
* `IsDetailedBalanced` -- pairwise flux symmetry;
* `isComplexBalanced_of_isDetailedBalanced` -- detailed balance implies complex balance;
* `IsPositiveDetailedBalanced` -- the usual positive-equilibrium formulation.

This file does not yet impose Wegscheider's cycle conditions on rate constants; those
belong in `CRNT.Equilibria.Wegscheider`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Total mass-action flux carried by reaction channels from complex `c` to complex `d`. -/
def pairFlux (N : Network S) (κ : RateConstants N) (x : Concentration S)
    (c d : Complex S) : ℝ :=
  ∑ r : N.R,
    if (N.reaction r).source = c ∧ (N.reaction r).target = d then
      N.massActionRate κ r x
    else 0

/-- A pair flux with a left endpoint absent from the network is zero. -/
theorem pairFlux_eq_zero_of_source_not_mem (N : Network S) (κ : RateConstants N)
    (x : Concentration S) {c d : Complex S} (hc : c ∉ N.complexes) :
    N.pairFlux κ x c d = 0 := by
  classical
  unfold pairFlux
  apply Finset.sum_eq_zero
  intro r _
  have hsrc : (N.reaction r).source ≠ c := by
    intro h
    apply hc
    rw [← h]
    exact N.source_mem_complexes r
  simp [hsrc]

/-- A pair flux with a right endpoint absent from the network is zero. -/
theorem pairFlux_eq_zero_of_target_not_mem (N : Network S) (κ : RateConstants N)
    (x : Concentration S) {c d : Complex S} (hd : d ∉ N.complexes) :
    N.pairFlux κ x c d = 0 := by
  classical
  unfold pairFlux
  apply Finset.sum_eq_zero
  intro r _
  have htgt : (N.reaction r).target ≠ d := by
    intro h
    apply hd
    rw [← h]
    exact N.target_mem_complexes r
  simp [htgt]

/-- Outflow from a complex is the sum of its pairwise outgoing complex fluxes. -/
theorem outflow_eq_sum_pairFlux (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (c : Complex S) :
    N.outflow κ x c = ∑ d ∈ N.complexes, N.pairFlux κ x c d := by
  classical
  unfold outflow pairFlux
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hs : (N.reaction r).source = c
  · simp only [hs, if_true]
    rw [Finset.sum_eq_single (N.reaction r).target]
    · simp
    · intro d hd hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (N.target_mem_complexes r)).elim
  · simp [hs]

/-- Inflow to a complex is the sum of its pairwise incoming complex fluxes. -/
theorem inflow_eq_sum_pairFlux (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (c : Complex S) :
    N.inflow κ x c = ∑ d ∈ N.complexes, N.pairFlux κ x d c := by
  classical
  unfold inflow pairFlux
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  by_cases ht : (N.reaction r).target = c
  · simp only [ht, if_true]
    rw [Finset.sum_eq_single (N.reaction r).source]
    · simp
    · intro d hd hne
      simp [hne.symm]
    · intro hnot
      exact (hnot (N.source_mem_complexes r)).elim
  · simp [ht]

/-- Pair fluxes are nonnegative at nonnegative concentrations. -/
theorem pairFlux_nonneg (N : Network S) (κ : RateConstants N) {x : Concentration S}
    (hx : x.Nonnegative) (c d : Complex S) :
    0 ≤ N.pairFlux κ x c d := by
  classical
  unfold pairFlux
  apply Finset.sum_nonneg
  intro r _
  split_ifs
  · exact N.massActionRate_nonneg κ r hx
  · exact le_rfl

/-- Any actual reaction channel contributes strictly positive pair flux at a positive
concentration.  Other parallel channels can only add nonnegative flux. -/
theorem pairFlux_pos_of_reaction (N : Network S) (κ : RateConstants N)
    {x : Concentration S} (hx : x.Positive) (r : N.R) :
    0 < N.pairFlux κ x (N.reaction r).source (N.reaction r).target := by
  classical
  unfold pairFlux
  apply Finset.sum_pos'
  · intro q _
    split_ifs
    · exact N.massActionRate_nonneg κ q hx.nonnegative
    · exact le_rfl
  · refine ⟨r, Finset.mem_univ r, ?_⟩
    simp only [and_self, if_true]
    exact N.massActionRate_pos κ r hx

/-- `x` is detailed-balanced when every ordered pair of network complexes carries the
same total flux as its reverse pair.  Quantifying only over `N.complexes` is enough,
because pair fluxes involving absent complexes vanish. -/
def IsDetailedBalanced (N : Network S) (κ : RateConstants N) (x : Concentration S) : Prop :=
  ∀ c ∈ N.complexes, ∀ d ∈ N.complexes,
    N.pairFlux κ x c d = N.pairFlux κ x d c

/-- Detailed balance is symmetric in the two complexes by definition. -/
theorem detailedBalance_pair_symm (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (hdb : N.IsDetailedBalanced κ x)
    {c d : Complex S} (hc : c ∈ N.complexes) (hd : d ∈ N.complexes) :
    N.pairFlux κ x d c = N.pairFlux κ x c d :=
  (hdb c hc d hd).symm

/-- **Detailed balance implies complex balance.**  Pairwise flux cancellation implies
that total inflow and outflow agree at every complex. -/
theorem isComplexBalanced_of_isDetailedBalanced (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (hdb : N.IsDetailedBalanced κ x) :
    N.IsComplexBalanced κ x := by
  intro c hc
  rw [N.inflow_eq_sum_pairFlux κ x c, N.outflow_eq_sum_pairFlux κ x c]
  apply Finset.sum_congr rfl
  intro d hd
  exact hdb d hd c hc

/-- The usual positive detailed-balanced equilibrium predicate.  Positivity is kept
explicit rather than baked into `IsDetailedBalanced`, matching the rest of the library's
separation between algebraic balance equations and concentration-domain hypotheses. -/
def IsPositiveDetailedBalanced (N : Network S) (κ : RateConstants N)
    (x : Concentration S) : Prop :=
  x.Positive ∧ N.IsDetailedBalanced κ x

/-- **Positive detailed balance forces structural reversibility.**  Every forward
reaction has strictly positive pair flux. Detailed balance makes the reverse pair flux
strictly positive as well, which is impossible unless at least one reverse reaction channel
exists. This implication does not choose a pairing of parallel channels. -/
theorem reversible_of_positiveDetailedBalanced (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (hdb : N.IsPositiveDetailedBalanced κ x) :
    N.Reversible := by
  intro r
  let c := (N.reaction r).source
  let d := (N.reaction r).target
  have hc : c ∈ N.complexes := N.source_mem_complexes r
  have hd : d ∈ N.complexes := N.target_mem_complexes r
  have hfwd : 0 < N.pairFlux κ x c d := N.pairFlux_pos_of_reaction κ hdb.1 r
  have hrev : 0 < N.pairFlux κ x d c := by
    rw [← hdb.2 c hc d hd]
    exact hfwd
  by_contra hnone
  push_neg at hnone
  have hz : N.pairFlux κ x d c = 0 := by
    classical
    unfold pairFlux
    apply Finset.sum_eq_zero
    intro q _
    have hpair : ¬ ((N.reaction q).source = d ∧ (N.reaction q).target = c) := by
      intro hq
      exact hnone q hq.1 hq.2
    simp [hpair]
  rw [hz] at hrev
  exact (lt_irrefl 0) hrev

/-- A network admitting a positive detailed-balanced state is weakly reversible. -/
theorem weaklyReversible_of_positiveDetailedBalanced (N : Network S) (κ : RateConstants N)
    (x : Concentration S) (hdb : N.IsPositiveDetailedBalanced κ x) :
    N.WeaklyReversible :=
  (N.reversible_of_positiveDetailedBalanced κ x hdb).weaklyReversible

/-- A positive detailed-balanced concentration is positive and complex-balanced. -/
theorem positiveComplexBalanced_of_positiveDetailedBalanced
    (N : Network S) (κ : RateConstants N) (x : Concentration S)
    (h : N.IsPositiveDetailedBalanced κ x) :
    x.Positive ∧ N.IsComplexBalanced κ x :=
  ⟨h.1, N.isComplexBalanced_of_isDetailedBalanced κ x h.2⟩

/-- Detailed balance is, in particular, a mass-action steady-state condition. -/
theorem IsDetailedBalanced.isMassActionSteadyState
    (N : Network S) (κ : RateConstants N) (x : Concentration S)
    (h : N.IsDetailedBalanced κ x) :
    N.IsMassActionSteadyState κ x :=
  (N.isComplexBalanced_of_isDetailedBalanced κ x h).isMassActionSteadyState N κ

end Network
end CRNT
