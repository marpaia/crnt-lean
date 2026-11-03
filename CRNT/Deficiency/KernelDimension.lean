import CRNT.Dynamics.MassActionAlgebra
import CRNT.Stoich.Subspace
import CRNT.Deficiency.Definition
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Deficiency as a kernel dimension

The deficiency `δ = n − ℓ − s` has a linear-algebraic meaning. Introduce two linear
maps out of the reaction space `R → ℝ`:

* the **stoichiometric map** `stoichMap` (the stoichiometric matrix), `e_r ↦` reaction
  vector `r`, whose range is the stoichiometric subspace, so `s = rank(stoichMap)`;
* the **incidence map** `incidenceMap` (the boundary map `∂`), `e_r ↦ δ_{target r} −
  δ_{source r}` into the complex space, whose range `Im ∂` is the cut space of the
  reaction graph.

These factor as `stoichMap = Y ∘ ∂` (`complexMap_comp_incidenceMap`). Restricting `Y`
to `Im ∂` and applying rank–nullity gives the bridge

```text
rank(∂) = s + dim(ker Y ∩ Im ∂)
```

(`incidenceRank_eq_stoichRank_add`). Writing `deficiencySubspace := ker Y ⊓ Im ∂`, the
deficiency equals `dim(deficiencySubspace)` (`deficiencyInt_eq_finrank_deficiencySubspace`),
using the graph identity `rank(∂) = n − ℓ` — the rank of the incidence map equals vertices
minus connected components — established here as `incidenceRank_add_numLinkageClasses`.

Depends on the dynamics and stoichiometry layers.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

open scoped BigOperators
open Matrix

/-- The stoichiometric map (stoichiometric matrix) `(R → ℝ) →ₗ (S → ℝ)`, sending the
unit reaction `e_r` to its reaction vector. -/
noncomputable def stoichMap (N : Network S) : (N.R → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun v := ∑ r : N.R, v r • N.reactionVector r
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum]

theorem stoichMap_apply (N : Network S) (v : N.R → ℝ) (s : S) :
    N.stoichMap v s = ∑ r : N.R, v r * N.reactionVector r s := by
  simp [stoichMap, Finset.sum_apply]

theorem stoichMap_single (N : Network S) (r : N.R) :
    N.stoichMap (Pi.single r 1) = N.reactionVector r := by
  simp [stoichMap]

/-- The range of the stoichiometric map is the stoichiometric subspace. -/
theorem range_stoichMap (N : Network S) :
    LinearMap.range N.stoichMap = N.stoichSubspace := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    show (∑ r : N.R, v r • N.reactionVector r) ∈ N.stoichSubspace
    exact Submodule.sum_mem _ fun r _ =>
      Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)
  · rw [stoichSubspace, Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    exact ⟨Pi.single r 1, N.stoichMap_single r⟩

/-- The stoichiometric rank is the dimension of the range of the stoichiometric map. -/
theorem stoichRank_eq_finrank_range (N : Network S) :
    N.stoichRank = Module.finrank ℝ (LinearMap.range N.stoichMap) := by
  show Module.finrank ℝ N.stoichSubspace = _
  rw [range_stoichMap]

/-- The incidence map (boundary map `∂`) `(R → ℝ) →ₗ (ComplexIdx → ℝ)`, sending the
unit reaction `e_r` to `δ_{target r} − δ_{source r}`. -/
noncomputable def incidenceMap (N : Network S) :
    (N.R → ℝ) →ₗ[ℝ] (N.ComplexIdx → ℝ) where
  toFun v := fun c => ∑ r : N.R, v r *
    ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0))
  map_add' v w := by
    funext c
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring
  map_smul' a v := by
    funext c
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    ring

@[simp] theorem incidenceMap_apply (N : Network S) (v : N.R → ℝ) (c : N.ComplexIdx) :
    N.incidenceMap v c = ∑ r : N.R, v r *
      ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)) := rfl

/-- The stoichiometric map factors as the complex matrix after the incidence map:
`stoichMap = Y ∘ ∂`. -/
theorem complexMap_comp_incidenceMap (N : Network S) :
    N.complexMap.comp N.incidenceMap = N.stoichMap := by
  apply LinearMap.ext
  intro v
  funext s
  simp only [LinearMap.comp_apply, complexMap_apply, incidenceMap_apply, stoichMap_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hexpand : ∀ c : N.ComplexIdx,
      v r * ((if N.targetIdx r = c then (1 : ℝ) else 0) - (if N.sourceIdx r = c then 1 else 0)) *
          (c.val s : ℝ)
        = v r * ((if N.targetIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ)
            - (if N.sourceIdx r = c then (1 : ℝ) else 0) * (c.val s : ℝ)) := fun c => by ring
  simp only [hexpand]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, sum_ite_complexMap, sum_ite_complexMap,
    reactionVector_apply]
  simp only [targetIdx, sourceIdx]

/-- The rank of the incidence map: `rank(∂)`, the dimension of the cut space. -/
noncomputable def incidenceRank (N : Network S) : ℕ :=
  Module.finrank ℝ (LinearMap.range N.incidenceMap)

/-- The deficiency subspace `ker Y ∩ Im ∂`. Its dimension is the deficiency once the
incidence rank is identified with `n − ℓ`. -/
noncomputable def deficiencySubspace (N : Network S) : Submodule ℝ (N.ComplexIdx → ℝ) :=
  LinearMap.ker N.complexMap ⊓ LinearMap.range N.incidenceMap

/-- **Rank bridge.** `rank(∂) = s + dim(ker Y ∩ Im ∂)`: restricting the complex matrix
to the cut space and applying rank–nullity. -/
theorem incidenceRank_eq_stoichRank_add (N : Network S) :
    N.incidenceRank = N.stoichRank + Module.finrank ℝ N.deficiencySubspace := by
  have hrn := LinearMap.finrank_range_add_finrank_ker
    (N.complexMap.domRestrict (LinearMap.range N.incidenceMap))
  have hr : Module.finrank ℝ
      (LinearMap.range (N.complexMap.domRestrict (LinearMap.range N.incidenceMap)))
      = N.stoichRank := by
    rw [LinearMap.range_domRestrict, ← LinearMap.range_comp, complexMap_comp_incidenceMap,
      ← stoichRank_eq_finrank_range]
  have hk : Module.finrank ℝ
      (LinearMap.ker (N.complexMap.domRestrict (LinearMap.range N.incidenceMap)))
      = Module.finrank ℝ N.deficiencySubspace := by
    rw [← Submodule.finrank_map_subtype_eq (LinearMap.range N.incidenceMap)
      (LinearMap.ker (N.complexMap.domRestrict (LinearMap.range N.incidenceMap)))]
    rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype, deficiencySubspace, inf_comm]
  rw [incidenceRank, ← hrn, hr, hk]

/-! ### The incidence-rank identity `rank(∂) = n − ℓ`

We discharge the graph identity via the matrix-transpose route: `rank(∂) = rank(∂ᵀ)`
(`Matrix.rank_transpose`), and `dim(ker ∂ᵀ) = ℓ`, because the kernel of the transpose
is exactly the functions on complexes that are constant on each linkage class — a space
isomorphic to functions on the quotient by linkage. -/

/-- The incidence matrix `M : Matrix ComplexIdx R ℝ`, `M c r = [target r = c] −
[source r = c]`. The incidence map is multiplication by `M`. -/
noncomputable def incidenceMatrix (N : Network S) : Matrix N.ComplexIdx N.R ℝ :=
  fun c r => (if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)

theorem incidenceMap_eq_mulVecLin (N : Network S) :
    N.incidenceMap = N.incidenceMatrix.mulVecLin := by
  apply LinearMap.ext
  intro v
  funext c
  rw [Matrix.mulVecLin_apply, incidenceMap_apply]
  simp only [Matrix.mulVec, dotProduct, incidenceMatrix]
  exact Finset.sum_congr rfl fun r _ => by ring

theorem incidenceRank_eq_matrixRank (N : Network S) :
    N.incidenceRank = N.incidenceMatrix.rank := by
  show Module.finrank ℝ (LinearMap.range N.incidenceMap) = _
  rw [incidenceMap_eq_mulVecLin]
  rfl

/-- `finrank (ComplexIdx → ℝ) = n`. -/
theorem finrank_complexIdx_fun (N : Network S) :
    Module.finrank ℝ (N.ComplexIdx → ℝ) = N.numComplexes := by
  rw [Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_coe _

/-- Collapse of a single indicator against an arbitrary vector: `∑_c [C = c] · g c = g C`. -/
theorem sum_ite_one_mul (N : Network S) (C : N.ComplexIdx) (g : N.ComplexIdx → ℝ) :
    (∑ c : N.ComplexIdx, (if C = c then (1 : ℝ) else 0) * g c) = g C := by
  rw [Finset.sum_eq_single C]
  · simp
  · intro c _ hc; rw [if_neg (Ne.symm hc), zero_mul]
  · intro h; exact absurd (Finset.mem_univ C) h

/-- The transpose of the incidence map sends `w` to `r ↦ w(target r) − w(source r)`. -/
theorem incidenceTranspose_apply (N : Network S) (w : N.ComplexIdx → ℝ) (r : N.R) :
    N.incidenceMatrixᵀ.mulVecLin w r = w (N.targetIdx r) - w (N.sourceIdx r) := by
  rw [Matrix.mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, incidenceMatrix, sub_mul]
  rw [Finset.sum_sub_distrib, sum_ite_one_mul, sum_ite_one_mul]

/-- Pairing a complex potential with the incidence image of one reaction basis vector gives its
target-minus-source increment. -/
theorem sum_mul_incidenceMap_single_eq_edgeIncrement (N : Network S)
    (w : N.ComplexIdx → ℝ) (r : N.R) :
    (∑ c : N.ComplexIdx, w c * N.incidenceMap (Pi.single r (1 : ℝ)) c) =
      w (N.targetIdx r) - w (N.sourceIdx r) := by
  let e : N.R → ℝ := Pi.single r 1
  have hinc (c : N.ComplexIdx) :
      N.incidenceMap e c =
          (if N.targetIdx r = c then (1 : ℝ) else 0) -
          (if N.sourceIdx r = c then 1 else 0) := by
    rw [N.incidenceMap_apply]
    simp only [e, Pi.single_apply]
    rw [Finset.sum_eq_single r]
    · simp
    · intro r' _ hne
      simp [hne]
    · intro h
      exact False.elim (h (Finset.mem_univ r))
  have hsplit :
      (∑ c : N.ComplexIdx, w c * N.incidenceMap e c) =
        (∑ c : N.ComplexIdx,
          w c * (if N.targetIdx r = c then (1 : ℝ) else 0)) -
        ∑ c : N.ComplexIdx,
          w c * (if N.sourceIdx r = c then (1 : ℝ) else 0) := by
    calc
      _ = ∑ c : N.ComplexIdx,
          w c * ((if N.targetIdx r = c then (1 : ℝ) else 0) -
            (if N.sourceIdx r = c then 1 else 0)) := by
              apply Finset.sum_congr rfl
              intro c _
              rw [hinc c]
      _ = _ := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro c _
        ring
  have htarget :
      (∑ c : N.ComplexIdx,
        w c * (if N.targetIdx r = c then (1 : ℝ) else 0)) =
          w (N.targetIdx r) := by
    calc
      _ = ∑ c : N.ComplexIdx,
          (if N.targetIdx r = c then (1 : ℝ) else 0) * w c := by
            apply Finset.sum_congr rfl
            intro c _
            ring
      _ = _ := N.sum_ite_one_mul (N.targetIdx r) w
  have hsource :
      (∑ c : N.ComplexIdx,
        w c * (if N.sourceIdx r = c then (1 : ℝ) else 0)) =
          w (N.sourceIdx r) := by
    calc
      _ = ∑ c : N.ComplexIdx,
          (if N.sourceIdx r = c then (1 : ℝ) else 0) * w c := by
            apply Finset.sum_congr rfl
            intro c _
            ring
      _ = _ := N.sum_ite_one_mul (N.sourceIdx r) w
  change (∑ c : N.ComplexIdx, w c * N.incidenceMap e c) = _
  rw [hsplit, htarget, hsource]

/-- A function on complexes that is constant along every reaction edge is constant on
each linkage class. -/
theorem linked_imp_eq_of_edge_const (N : Network S) {w : N.ComplexIdx → ℝ}
    (hw : ∀ r, w (N.targetIdx r) = w (N.sourceIdx r))
    (c : Complex S) (hc : c ∈ N.complexes) :
    ∀ (d : Complex S), N.Linked c d → ∀ (hd : d ∈ N.complexes), w ⟨c, hc⟩ = w ⟨d, hd⟩ := by
  intro d hcd
  induction hcd with
  | refl => intro _; rfl
  | @tail e f _ hef ih =>
    intro hf
    rcases hef with ⟨r, hs, ht⟩ | ⟨r, hs, ht⟩
    · have he : e ∈ N.complexes := hs ▸ N.source_mem_complexes r
      have hwe : w ⟨e, he⟩ = w ⟨f, hf⟩ := by
        have e1 : N.sourceIdx r = (⟨e, he⟩ : N.ComplexIdx) := Subtype.ext hs
        have e2 : N.targetIdx r = (⟨f, hf⟩ : N.ComplexIdx) := Subtype.ext ht
        have h := hw r
        rw [e1, e2] at h
        exact h.symm
      rw [ih he, hwe]
    · have he : e ∈ N.complexes := ht ▸ N.target_mem_complexes r
      have hwe : w ⟨e, he⟩ = w ⟨f, hf⟩ := by
        have e1 : N.sourceIdx r = (⟨f, hf⟩ : N.ComplexIdx) := Subtype.ext hs
        have e2 : N.targetIdx r = (⟨e, he⟩ : N.ComplexIdx) := Subtype.ext ht
        have h := hw r
        rw [e1, e2] at h
        exact h
      rw [ih he, hwe]

/-- Pullback of a function on linkage classes to a function on complexes (constant on
each class). -/
noncomputable def linkageLift (N : Network S) :
    (Quotient N.linkedSetoid → ℝ) →ₗ[ℝ] (N.ComplexIdx → ℝ) where
  toFun f := fun c => f (Quotient.mk N.linkedSetoid c)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem linkageLift_apply (N : Network S) (f : Quotient N.linkedSetoid → ℝ)
    (c : N.ComplexIdx) : N.linkageLift f c = f (Quotient.mk N.linkedSetoid c) := rfl

theorem linkageLift_injective (N : Network S) : Function.Injective N.linkageLift := by
  intro f g h
  funext q
  obtain ⟨c, rfl⟩ := Quotient.exists_rep q
  exact congrFun h c

/-- The kernel of the incidence transpose is exactly the pullbacks of functions on
linkage classes. -/
theorem ker_incidenceTranspose (N : Network S) :
    LinearMap.ker N.incidenceMatrixᵀ.mulVecLin = LinearMap.range N.linkageLift := by
  apply le_antisymm
  · intro w hw
    have hw' : ∀ r, w (N.targetIdx r) = w (N.sourceIdx r) := by
      intro r
      have h0 : N.incidenceMatrixᵀ.mulVecLin w r = 0 := by
        rw [LinearMap.mem_ker.mp hw]; rfl
      rw [incidenceTranspose_apply, sub_eq_zero] at h0
      exact h0
    refine ⟨Quotient.lift w (fun a b hab => ?_), ?_⟩
    · have key := N.linked_imp_eq_of_edge_const hw' a.val a.2 b.val hab b.2
      rwa [Subtype.coe_eta, Subtype.coe_eta] at key
    · funext c; rfl
  · rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    funext r
    rw [incidenceTranspose_apply, Pi.zero_apply, sub_eq_zero, linkageLift_apply,
      linkageLift_apply]
    congr 1
    exact Quotient.sound (Relation.ReflTransGen.single (Or.inr ⟨r, rfl, rfl⟩))

/-- `dim(ker ∂ᵀ) = ℓ`: the linkage-constant functions are isomorphic to functions on
the linkage-class quotient. -/
theorem finrank_ker_incidenceTranspose (N : Network S) :
    Module.finrank ℝ (LinearMap.ker N.incidenceMatrixᵀ.mulVecLin) = N.numLinkageClasses := by
  rw [ker_incidenceTranspose, LinearMap.finrank_range_of_inj N.linkageLift_injective]
  letI : Fintype (Quotient N.linkedSetoid) := Fintype.ofFinite _
  rw [Module.finrank_fintype_fun_eq_card, numLinkageClasses, Nat.card_eq_fintype_card]

/-- **Fact B: the incidence-rank identity** `rank(∂) + ℓ = n`. -/
theorem incidenceRank_add_numLinkageClasses (N : Network S) :
    N.incidenceRank + N.numLinkageClasses = N.numComplexes := by
  have h := LinearMap.finrank_range_add_finrank_ker N.incidenceMatrixᵀ.mulVecLin
  rw [finrank_ker_incidenceTranspose, finrank_complexIdx_fun] at h
  have hrank : Module.finrank ℝ (LinearMap.range N.incidenceMatrixᵀ.mulVecLin)
      = N.incidenceRank :=
    calc Module.finrank ℝ (LinearMap.range N.incidenceMatrixᵀ.mulVecLin)
        = N.incidenceMatrixᵀ.rank := rfl
      _ = N.incidenceMatrix.rank := Matrix.rank_transpose _
      _ = N.incidenceRank := (incidenceRank_eq_matrixRank N).symm
  rwa [hrank] at h

/-- The incidence-rank identity in integer form: `rank(∂) = n − ℓ`. -/
theorem incidenceRank_eq (N : Network S) :
    (N.incidenceRank : ℤ) = (N.numComplexes : ℤ) - (N.numLinkageClasses : ℤ) := by
  have := N.incidenceRank_add_numLinkageClasses
  omega

/-- **Deficiency as a kernel dimension**: `δ = dim(ker Y ∩ Im ∂)`. -/
theorem deficiencyInt_eq_finrank_deficiencySubspace (N : Network S) :
    N.deficiencyInt = (Module.finrank ℝ N.deficiencySubspace : ℤ) := by
  have hb2 : (N.incidenceRank : ℤ)
      = (N.stoichRank : ℤ) + (Module.finrank ℝ N.deficiencySubspace : ℤ) := by
    exact_mod_cast N.incidenceRank_eq_stoichRank_add
  have hB := N.incidenceRank_eq
  rw [deficiencyInt]
  omega

/-- **Deficiency zero as vanishing of the deficiency subspace.** This is the form
consumed by the deficiency-zero theorem: a deficiency-zero network is exactly one for
which the complex matrix `Y` is injective on the cut space `Im ∂`, so the monomial
vector of any complex-balanced concentration is forced into `ker A_k`. -/
theorem deficiencyZero_iff_deficiencySubspace_eq_bot (N : Network S) :
    N.DeficiencyZero ↔ N.deficiencySubspace = ⊥ := by
  unfold DeficiencyZero
  rw [deficiencyInt_eq_finrank_deficiencySubspace N, Nat.cast_eq_zero,
    Submodule.finrank_eq_zero]

end Network

end CRNT
