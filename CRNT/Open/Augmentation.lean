import CRNT.Stoich.Subspace
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Open networks: inflows, outflows, and the fully open extension

Closed reaction networks conserve total amounts along the reactions' stoichiometry. A
reactor exchanges material with its surroundings: each species can be synthesised (`0 → s`)
and degraded (`s → 0`). Adjoining these pseudo-reactions for every species gives the
**fully open extension** of a network.

The open extension's reaction vectors include the standard basis `±e_s`, so its
stoichiometric subspace is the whole species space:

* `stoichSubspace_fullyOpen_eq_top`: `S(N⁺) = ⊤`;
* `stoichRank_fullyOpen`: the stoichiometric rank is `card S`;
* `orthSum_stoichSubspace_fullyOpen_eq_bot`: the conservation laws vanish — the only
  vector orthogonal to every reaction vector is `0`.

This module depends on: `CRNT.Stoich.Subspace`, `CRNT.LinearAlgebra.OrthogonalComplement`.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The singleton complex `e_s`: one molecule of species `s`, nothing else. -/
def singletonComplex (s : S) : Complex S := Pi.single s 1

omit [Fintype S] in
@[simp] theorem singletonComplex_apply (s s' : S) :
    singletonComplex s s' = if s' = s then 1 else 0 := by
  rw [singletonComplex, Pi.single_apply]

/-- The synthesis (inflow) pseudo-reaction `0 → s`. -/
def inflowReaction (s : S) : Reaction S := { source := Complex.zero, target := singletonComplex s }

/-- The degradation (outflow) pseudo-reaction `s → 0`. -/
def outflowReaction (s : S) : Reaction S := { source := singletonComplex s, target := Complex.zero }

namespace Network

/-- **The fully open extension** of a network: the original reactions together with a
synthesis `0 → s` and a degradation `s → 0` for every species. Reactions are indexed by
`N.R ⊕ S ⊕ S` — original, inflows, outflows. -/
def fullyOpen (N : Network S) : Network S where
  R := N.R ⊕ S ⊕ S
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := Sum.elim N.reaction (Sum.elim inflowReaction outflowReaction)

@[simp] theorem fullyOpen_reaction_inl (N : Network S) (r : N.R) :
    N.fullyOpen.reaction (Sum.inl r) = N.reaction r := rfl

@[simp] theorem fullyOpen_reaction_inflow (N : Network S) (s : S) :
    N.fullyOpen.reaction (Sum.inr (Sum.inl s)) = inflowReaction s := rfl

@[simp] theorem fullyOpen_reaction_outflow (N : Network S) (s : S) :
    N.fullyOpen.reaction (Sum.inr (Sum.inr s)) = outflowReaction s := rfl

/-- The inflow reaction's vector is the standard basis vector `e_s`. -/
theorem reactionVector_inflow (N : Network S) (s : S) :
    N.fullyOpen.reactionVector (Sum.inr (Sum.inl s)) = Pi.single s (1 : ℝ) := by
  funext s'
  change ((inflowReaction s).target s' : ℝ) - ((inflowReaction s).source s' : ℝ) =
    ((Pi.single s (1 : ℝ) : S → ℝ) s')
  simp only [inflowReaction, singletonComplex_apply, Complex.zero_apply, Pi.single_apply]
  split <;> simp_all

/-- The outflow reaction's vector is `-e_s`. -/
theorem reactionVector_outflow (N : Network S) (s : S) :
    N.fullyOpen.reactionVector (Sum.inr (Sum.inr s)) = -Pi.single s (1 : ℝ) := by
  funext s'
  change ((outflowReaction s).target s' : ℝ) - ((outflowReaction s).source s' : ℝ) =
    ((-Pi.single s (1 : ℝ) : S → ℝ) s')
  simp only [outflowReaction, singletonComplex_apply, Complex.zero_apply, Pi.neg_apply,
    Pi.single_apply]
  split <;> simp_all

/-- **The stoichiometric subspace of the fully open extension is everything.** The inflow
reaction vectors are the standard basis, which spans the species space. -/
theorem stoichSubspace_fullyOpen_eq_top (N : Network S) :
    N.fullyOpen.stoichSubspace = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ s : S, v s • (Pi.single s (1 : ℝ)) := by
    funext s'
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [hv]
  refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
  rw [← reactionVector_inflow N s]
  exact N.fullyOpen.reactionVector_mem_stoichSubspace _

/-- **The stoichiometric rank of the fully open extension is `card S`.** -/
theorem stoichRank_fullyOpen (N : Network S) :
    N.fullyOpen.stoichRank = Fintype.card S := by
  rw [Network.stoichRank, stoichSubspace_fullyOpen_eq_top, finrank_top, Module.finrank_pi]

/-- The orthogonal complement of the full space is trivial: only `0` is orthogonal to
every vector. -/
theorem orthSum_top_eq_bot : orthSum (⊤ : Submodule ℝ (S → ℝ)) = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  rw [mem_orthSum] at hw
  rw [Submodule.mem_bot]
  funext i
  have hi := hw (Pi.single i 1) Submodule.mem_top
  rwa [Finset.sum_eq_single i (fun j _ hj => by rw [Pi.single_eq_of_ne hj, mul_zero])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same, mul_one] at hi

/-- **Conservation laws vanish in the fully open extension.** No nonzero vector is
orthogonal to every reaction vector — the open system has no nontrivial conserved
quantity. -/
theorem orthSum_stoichSubspace_fullyOpen_eq_bot (N : Network S) :
    orthSum N.fullyOpen.stoichSubspace = ⊥ := by
  rw [stoichSubspace_fullyOpen_eq_top, orthSum_top_eq_bot]

end Network

end CRNT
