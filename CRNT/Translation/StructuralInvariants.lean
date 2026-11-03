import CRNT.Translation.ReactionTranslation
import CRNT.Stoich.Subspace
import CRNT.Deficiency.Definition
import CRNT.Equilibria.CompatibilityClass

/-!
# Structural invariants of a reaction-wise translation

What a translation `τ : N.R → Complex S` preserves, and what it does not.

## Rewritten: the previous draft was unprovable as written

The earlier version of this module stated six results about a complex bijection induced by a
"complex-faithful" translation: `complexEquiv`, `complexEquiv_source`, `complexEquiv_target`,
`numComplexes_eq`, `directlyLinked_iff`, `linked_iff`. Every one was `sorry`, and they were phrased
against three names that do not exist anywhere in the repository -- a structure
`N.ReactionTranslation` (16 references), a predicate `T.ComplexFaithful`, and a relation
`N.DirectlyLinked`. So the module established nothing and could not be repaired by fixing tactics.

What is provable now, on the real API, is the *stoichiometric* half, and that is what this module
contains. Every result below is proved.

## Deliberately not claimed

Complex-count and linkage-class invariance are **not** here. A translation shifts each reaction's
source and target by the same complex, so it can identify two previously distinct complexes or
separate them; neither `numComplexes` nor the linkage-class partition is invariant in general. The
earlier draft's `numComplexes_eq` was therefore false without a faithfulness hypothesis, and
designing that hypothesis -- so that the induced map on complexes is well defined and injective --
is the open work. Since deficiency is `n - ℓ - s` and only `s` is shown invariant here, deficiency
invariance does not follow either, and is not stated.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-! The subspace and rank invariance themselves are already proved in
`CRNT/Translation/ReactionTranslation.lean` as `translate_stoichSubspace` and
`translate_stoichRank`; this module records the consequences. -/

/-- Compatibility classes coincide, since they are cosets of the stoichiometric subspace. -/
theorem translate_stoichCompatible (N : Network S) (τ : N.R → Complex S)
    (x y : Concentration S) :
    (N.translate τ).StoichCompatible x y ↔ N.StoichCompatible x y := by
  unfold StoichCompatible
  rw [N.translate_stoichSubspace τ]

/-- A translation preserves membership of the stoichiometric subspace for every reaction. -/
theorem translate_reactionVector_mem_stoichSubspace (N : Network S) (τ : N.R → Complex S)
    (r : N.R) :
    (N.translate τ).reactionVector r ∈ N.stoichSubspace := by
  rw [← N.translate_stoichSubspace τ]
  exact (N.translate τ).reactionVector_mem_stoichSubspace r

/-- The zero translation is the identity on the underlying stoichiometry. -/
theorem zeroTranslation_stoichSubspace (N : Network S) :
    (N.translate (N.zeroTranslation)).stoichSubspace = N.stoichSubspace :=
  N.translate_stoichSubspace _

end Network

end CRNT
