import CRNT.Deficiency.DeficiencyOne
import CRNT.Decision.Linkage
import CRNT.LinearAlgebra.FinrankSup
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Per-linkage-class deficiency and the decomposition inequality

Each linkage class `θ` carries its own deficiency `δ_θ = n_θ − 1 − s_θ`, where `n_θ` is the
number of complexes in the class and `s_θ` the rank of the span of the reaction vectors of
the reactions within it. Feinberg's structural inequality

```text
∑_θ δ_θ ≤ δ
```

(`sum_linkageDeficiency_le_deficiency`) holds because the complexes partition into linkage
classes (`sum_numComplexesIn`), the class count is `ℓ` (`card_quotient_eq`), and the
stoichiometric subspace is the join of the per-class subspaces, so its rank is at most the sum
of the per-class ranks (`stoichRank_le_sum`). Equality is exactly the deficiency-one theorem's
condition `∑_θ δ_θ = δ`. The structural equality criterion is proved below:
equality holds iff the linkage stoichiometric subspaces form an independent family.

Depends on: `CRNT.Deficiency.DeficiencyOne`, `CRNT.Decision.Linkage`,
`CRNT.LinearAlgebra.FinrankSup`.
-/

namespace CRNT

namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable instance instFintypeQuotientLinked (N : Network S) :
    Fintype (Quotient N.linkedSetoid) := Fintype.ofFinite _

/-- The linkage class of a complex of the network. -/
def classOf (N : Network S) (c : N.ComplexIdx) : Quotient N.linkedSetoid :=
  Quotient.mk N.linkedSetoid c

/-- The number of complexes in a linkage class. -/
noncomputable def numComplexesIn (N : Network S) (q : Quotient N.linkedSetoid) : ℕ :=
  (Finset.univ.filter (fun c : N.ComplexIdx => N.classOf c = q)).card

/-- The per-linkage-class stoichiometric subspace: the span of the reaction vectors of the
reactions whose source lies in the class. -/
def linkageStoichSubspace (N : Network S) (q : Quotient N.linkedSetoid) :
    Submodule ℝ (S → ℝ) :=
  Submodule.span ℝ {v | ∃ r : N.R, N.classOf (N.sourceIdx r) = q ∧ N.reactionVector r = v}

/-- The per-linkage-class stoichiometric rank. -/
noncomputable def linkageStoichRank (N : Network S) (q : Quotient N.linkedSetoid) : ℕ :=
  Module.finrank ℝ (N.linkageStoichSubspace q)

/-- The deficiency of a single linkage class, `δ_θ = n_θ − 1 − s_θ` (over `ℤ`). -/
noncomputable def linkageDeficiency (N : Network S) (q : Quotient N.linkedSetoid) : ℤ :=
  (N.numComplexesIn q : ℤ) - 1 - (N.linkageStoichRank q : ℤ)

/-- **The complexes partition into linkage classes:** `∑_θ n_θ = n`. -/
theorem sum_numComplexesIn (N : Network S) :
    ∑ q, N.numComplexesIn q = N.numComplexes := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset N.ComplexIdx)) (t := (Finset.univ : Finset (Quotient N.linkedSetoid)))
    (f := N.classOf) (fun c _ => Finset.mem_univ _)
  rw [Finset.card_univ, Fintype.card_coe] at h
  exact h.symm

/-- The number of linkage classes equals `ℓ`. -/
theorem card_quotient_eq (N : Network S) :
    Fintype.card (Quotient N.linkedSetoid) = N.numLinkageClasses := by
  rw [numLinkageClasses, Nat.card_eq_fintype_card]

/-- Each reaction vector lies in its class's stoichiometric subspace. -/
theorem reactionVector_mem_linkageStoichSubspace (N : Network S) (r : N.R) :
    N.reactionVector r ∈ N.linkageStoichSubspace (N.classOf (N.sourceIdx r)) :=
  Submodule.subset_span ⟨r, rfl, rfl⟩

/-- Each per-class subspace sits inside the stoichiometric subspace. -/
theorem linkageStoichSubspace_le (N : Network S) (q : Quotient N.linkedSetoid) :
    N.linkageStoichSubspace q ≤ N.stoichSubspace := by
  rw [linkageStoichSubspace, Submodule.span_le]
  rintro _ ⟨r, _, rfl⟩
  exact N.reactionVector_mem_stoichSubspace r

/-- **The stoichiometric subspace is the join of the per-class subspaces.** -/
theorem stoichSubspace_eq_sup (N : Network S) :
    N.stoichSubspace = Finset.univ.sup N.linkageStoichSubspace := by
  apply le_antisymm
  · rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact SetLike.le_def.mp
      (Finset.le_sup (Finset.mem_univ (N.classOf (N.sourceIdx r))))
      (N.reactionVector_mem_linkageStoichSubspace r)
  · exact Finset.sup_le fun q _ => N.linkageStoichSubspace_le q

/-- **The stoichiometric rank is at most the sum of the per-class ranks.** -/
theorem stoichRank_le_sum (N : Network S) :
    N.stoichRank ≤ ∑ q, N.linkageStoichRank q := by
  rw [stoichRank, stoichSubspace_eq_sup]
  exact finrank_finset_sup_le Finset.univ N.linkageStoichSubspace

/-- **The per-linkage-class deficiency decomposition inequality** `∑_θ δ_θ ≤ δ`. Equality is
Feinberg's deficiency-one condition. -/
theorem sum_linkageDeficiency_le_deficiency (N : Network S) :
    ∑ q, N.linkageDeficiency q ≤ N.deficiencyInt := by
  have hn : (∑ q, (N.numComplexesIn q : ℤ)) = (N.numComplexes : ℤ) := by
    rw [← Nat.cast_sum, N.sum_numComplexesIn]
  have hC : (N.stoichRank : ℤ) ≤ ∑ q, (N.linkageStoichRank q : ℤ) := by
    rw [← Nat.cast_sum]; exact_mod_cast N.stoichRank_le_sum
  have hsum : ∑ q, N.linkageDeficiency q
      = (∑ q, (N.numComplexesIn q : ℤ)) - (Fintype.card (Quotient N.linkedSetoid) : ℤ)
        - ∑ q, (N.linkageStoichRank q : ℤ) := by
    simp only [linkageDeficiency, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  rw [hsum, deficiencyInt, hn, card_quotient_eq]
  omega

/-- **Each linkage class has nonnegative deficiency** `0 ≤ δ_θ`. The reaction vectors of a
class are differences of the position vectors of its complexes, so their span sits inside the
`vectorSpan` of those `n_θ` points, of dimension at most `n_θ − 1`; hence `s_θ ≤ n_θ − 1`. -/
theorem linkageDeficiency_nonneg (N : Network S) (q : Quotient N.linkedSetoid) :
    0 ≤ N.linkageDeficiency q := by
  obtain ⟨c0, hc0⟩ := Quotient.exists_rep q
  set ι := {c : N.ComplexIdx // N.classOf c = q} with hι
  haveI : Nonempty ι := ⟨⟨c0, hc0⟩⟩
  set p : ι → (S → ℝ) := fun c => Complex.toRealVector c.val.val with hp
  have hWle : N.linkageStoichSubspace q ≤ vectorSpan ℝ (Set.range p) := by
    rw [linkageStoichSubspace, Submodule.span_le]
    rintro _ ⟨r, hr, rfl⟩
    have hlink : N.classOf (N.sourceIdx r) = N.classOf (N.targetIdx r) :=
      Quotient.sound (N.linked_of_reaction r)
    have htgt : N.classOf (N.targetIdx r) = q := by rw [← hlink]; exact hr
    have hmem : N.reactionVector r
        = p ⟨N.targetIdx r, htgt⟩ -ᵥ p ⟨N.sourceIdx r, hr⟩ := by
      funext s
      simp only [hp, vsub_eq_sub, Pi.sub_apply, Complex.toRealVector_apply, reactionVector_apply,
        sourceIdx, targetIdx]
    rw [hmem]
    exact vsub_mem_vectorSpan ℝ (Set.mem_range_self _) (Set.mem_range_self _)
  have hs : N.linkageStoichRank q ≤ Module.finrank ℝ (vectorSpan ℝ (Set.range p)) :=
    Submodule.finrank_mono hWle
  have hv := finrank_vectorSpan_range_add_one_le (k := ℝ) p
  have hn : Fintype.card ι = N.numComplexesIn q := by
    rw [numComplexesIn]; exact Fintype.card_subtype _
  rw [linkageDeficiency]
  omega

/-- **In a deficiency-zero network every linkage class has deficiency zero.** Each `δ_θ ≥ 0`
and `∑ δ_θ ≤ δ = 0`, so all are zero. -/
theorem linkageDeficiency_eq_zero_of_deficiencyZero (N : Network S) (h : N.DeficiencyZero)
    (q : Quotient N.linkedSetoid) : N.linkageDeficiency q = 0 := by
  have hsum := N.sum_linkageDeficiency_le_deficiency
  rw [(h : N.deficiencyInt = 0)] at hsum
  have hsum0 : ∑ q', N.linkageDeficiency q' = 0 :=
    le_antisymm hsum (Finset.sum_nonneg fun q' _ => N.linkageDeficiency_nonneg q')
  exact (Finset.sum_eq_zero_iff_of_nonneg fun q' _ => N.linkageDeficiency_nonneg q').mp hsum0 q
    (Finset.mem_univ q)

/-- The decomposition is tight exactly when the network deficiency is at most the sum of the
per-class deficiencies — the reverse of the always-valid inequality. -/
theorem sum_linkageDeficiency_eq_deficiency_iff (N : Network S) :
    (∑ q, N.linkageDeficiency q = N.deficiencyInt) ↔
      N.deficiencyInt ≤ ∑ q, N.linkageDeficiency q :=
  ⟨fun h => h ▸ le_refl _, fun h => le_antisymm N.sum_linkageDeficiency_le_deficiency h⟩

/-- Equality of linkage deficiencies is equivalent to additivity of the linkage ranks. -/
theorem sum_linkageDeficiency_eq_deficiency_iff_rank_additive (N : Network S) :
    (∑ q, N.linkageDeficiency q = N.deficiencyInt) ↔
      N.stoichRank = ∑ q, N.linkageStoichRank q := by
  have hn : (∑ q, (N.numComplexesIn q : ℤ)) = (N.numComplexes : ℤ) := by
    rw [← Nat.cast_sum, N.sum_numComplexesIn]
  have hsum : ∑ q, N.linkageDeficiency q =
      (∑ q, (N.numComplexesIn q : ℤ)) - (Fintype.card (Quotient N.linkedSetoid) : ℤ)
        - ∑ q, (N.linkageStoichRank q : ℤ) := by
    simp only [linkageDeficiency, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one]
  rw [hsum, deficiencyInt, hn, card_quotient_eq, ← Nat.cast_sum]
  constructor
  · intro h
    have heq : (N.stoichRank : ℤ) = (∑ q, N.linkageStoichRank q : ℕ) := by omega
    exact_mod_cast heq
  · intro h
    exact_mod_cast congrArg (fun n : ℕ =>
      (N.numComplexes : ℤ) - N.numLinkageClasses - n) h.symm

/-- The linkage-deficiency inequality is tight exactly when the linkage
stoichiometric subspaces form an independent family (an internal direct sum). -/
theorem sum_linkageDeficiency_eq_deficiency_iff_independent (N : Network S) :
    (∑ q, N.linkageDeficiency q = N.deficiencyInt) ↔
      iSupIndep N.linkageStoichSubspace := by
  rw [N.sum_linkageDeficiency_eq_deficiency_iff_rank_additive]
  constructor
  · intro h
    rw [iSupIndep_iff_supIndep_univ]
    apply supIndep_of_finrank_sup_eq_sum
    rw [← N.stoichSubspace_eq_sup]
    simpa only [stoichRank, linkageStoichRank] using h
  · intro h
    have heq := finrank_finset_sup_eq_sum_of_iSupIndep Finset.univ N.linkageStoichSubspace h
    rw [← N.stoichSubspace_eq_sup] at heq
    simpa only [stoichRank, linkageStoichRank] using heq

/-- **Feinberg's per-linkage-class deficiency conditions:** every linkage class has deficiency
at most one, and the class deficiencies sum to the network deficiency. These are conditions (i)
and (ii) of the deficiency-one theorem; the remaining condition is that each linkage class has
exactly one terminal strong linkage class. -/
structure DeficiencyOneConditions (N : Network S) : Prop where
  /-- Each linkage class has deficiency at most one. -/
  linkageDeficiency_le_one : ∀ q, N.linkageDeficiency q ≤ 1
  /-- The per-class deficiencies sum to the network deficiency (the decomposition is tight). -/
  sum_eq : ∑ q, N.linkageDeficiency q = N.deficiencyInt

end Network

end CRNT
