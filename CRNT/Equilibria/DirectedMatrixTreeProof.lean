import CRNT.Equilibria.MatrixTreeCofactorDefs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Order.Extension.Linear
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Finite combinatorial architecture for the directed Matrix--Tree theorem

The kinetic matrix used by CRNT is `A_κ = inflow - outflow`.  The positive Matrix--Tree
cofactor is therefore the determinant of the reduced **outflow Laplacian** `-A_κ`.

There is a particularly clean finite expansion of this determinant.  Multilinearity in the
columns chooses one outgoing reaction from every non-root complex.  Such a choice is a
functional reaction selection.  Its scalar coefficient is exactly the product of the chosen
rate constants.  What remains is the determinant of a reduced incidence matrix whose column
for `c → d` is `e_c - e_d` (with the root coordinate deleted).

For a functional selection that incidence determinant is:

* `1` when every vertex reaches the root, i.e. the selection is a rooted in-arborescence;
* `0` otherwise, because a non-root directed cycle gives a linear dependence.

This formulation avoids two defects of the previous proof skeleton: it does not sum over a
proof-carrying structure without a finite enumeration, and it does not attach an arbitrary
`±1` sign to a reaction selection.  All signs are determined by the incidence determinant.
-/

namespace CRNT
namespace Network

open scoped BigOperators
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Predicate saying that `T` chooses exactly one outgoing reaction from every non-root
complex in the linkage class of `root`, chooses none from the root, and contains no reactions
sourced outside that class.  Reachability of the root is deliberately not required. -/
def IsFunctionalReactionSelectionSet (N : Network S) (root : N.ComplexIdx)
    (T : Finset N.R) : Prop :=
  (∀ c : N.ComplexIdx, N.SameLinkage root c → c ≠ root →
    ∃! r : N.R, r ∈ T ∧ N.sourceIdx r = c) ∧
  (∀ r, r ∈ T → N.sourceIdx r ≠ root) ∧
  (∀ r, r ∈ T → N.SameLinkage root (N.sourceIdx r))

/-- Finite enumeration of all functional reaction-selection sets. -/
noncomputable def functionalReactionSelectionSets (N : Network S) (root : N.ComplexIdx) :
    Finset (Finset N.R) := by
  classical
  exact Finset.univ.filter (N.IsFunctionalReactionSelectionSet root)

@[simp] theorem mem_functionalReactionSelectionSets_iff
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R) :
    T ∈ N.functionalReactionSelectionSets root ↔
      N.IsFunctionalReactionSelectionSet root T := by
  classical
  simp [functionalReactionSelectionSets]

/-- Every rooted in-arborescence is, after forgetting reachability, a functional selection. -/
theorem IsRootedInArborescence.isFunctionalReactionSelectionSet
    {N : Network S} {root : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T) :
    N.IsFunctionalReactionSelectionSet root T :=
  ⟨hT.1, hT.2.1, hT.2.2.1⟩

/-- Reduced incidence matrix attached to a reaction selection.

For a selected reaction with source equal to column `j`, its contribution is
`e_j - e_target`; the target coordinate is simply absent when the target is the deleted root.
For a functional selection there is exactly one such reaction in each column. -/
noncomputable def selectionIncidenceMatrix
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R) :
    Matrix (N.WithoutLinkageRoot root) (N.WithoutLinkageRoot root) ℝ :=
  fun i j => ∑ r ∈ T,
    if N.sourceIdx r = j.1.1 then
      (if j.1.1 = i.1.1 then (1 : ℝ) else 0) -
        (if N.targetIdx r = i.1.1 then 1 else 0)
    else 0


/-- An outgoing reaction chosen for one non-root linkage-class complex. -/
abbrev ReducedOutgoingReaction (N : Network S) (root : N.ComplexIdx)
    (j : N.WithoutLinkageRoot root) :=
  {r : N.R // N.sourceIdx r = j.1.1}

/-- Forget a dependent choice of one outgoing reaction per non-root complex to its reaction set. -/
noncomputable def functionalSelectionOfChoice
    (N : Network S) (root : N.ComplexIdx)
    (f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j) :
    Finset N.R := by
  classical
  exact Finset.univ.image (fun j => (f j).1)

lemma functionalSelectionOfChoice_mem
    (N : Network S) (root : N.ComplexIdx)
    (f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j)
    (j : N.WithoutLinkageRoot root) :
    (f j).1 ∈ N.functionalSelectionOfChoice root f := by
  classical
  simp [functionalSelectionOfChoice]

lemma functionalSelectionOfChoice_source_unique
    (N : Network S) (root : N.ComplexIdx)
    (f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j)
    {j k : N.WithoutLinkageRoot root}
    (h : (f j).1 = (f k).1) : j = k := by
  apply Subtype.ext
  apply Subtype.ext
  exact (f j).2.symm.trans (h ▸ (f k).2)

lemma functionalSelectionOfChoice_injective
    (N : Network S) (root : N.ComplexIdx) :
    Function.Injective (N.functionalSelectionOfChoice root) := by
  classical
  intro f g hset
  funext j
  apply Subtype.ext
  have hm : (f j).1 ∈ N.functionalSelectionOfChoice root g := by
    rw [← hset]
    exact N.functionalSelectionOfChoice_mem root f j
  simp only [functionalSelectionOfChoice, Finset.mem_image] at hm
  rcases hm with ⟨k, _, hk⟩
  have hjk : j = k := by
    apply Subtype.ext
    apply Subtype.ext
    exact (f j).2.symm.trans (hk ▸ (g k).2)
  subst k
  exact hk.symm

lemma functionalSelectionOfChoice_isFunctional
    (N : Network S) (root : N.ComplexIdx)
    (f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j) :
    N.IsFunctionalReactionSelectionSet root (N.functionalSelectionOfChoice root f) := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · intro c hc hcr
    let jc : N.WithoutLinkageRoot root :=
      ⟨⟨c, hc⟩, by
        intro heq
        apply hcr
        exact congrArg Subtype.val heq⟩
    refine ⟨(f jc).1, ⟨N.functionalSelectionOfChoice_mem root f jc, (f jc).2⟩, ?_⟩
    intro r hr
    rcases hr with ⟨hrmem, hrsrc⟩
    simp only [functionalSelectionOfChoice, Finset.mem_image] at hrmem
    rcases hrmem with ⟨j, _, hjr⟩
    have hjc : j = jc := by
      apply Subtype.ext
      apply Subtype.ext
      exact (f j).2.symm.trans (hjr ▸ hrsrc)
    subst j
    exact hjr.symm
  · intro r hr
    simp only [functionalSelectionOfChoice, Finset.mem_image] at hr
    rcases hr with ⟨j, _, rfl⟩
    intro hsroot
    apply j.2
    apply Subtype.ext
    exact (f j).2.symm.trans hsroot
  · intro r hr
    simp only [functionalSelectionOfChoice, Finset.mem_image] at hr
    rcases hr with ⟨j, _, rfl⟩
    simpa [(f j).2] using j.1.2

/-- Recover the unique outgoing reaction at each non-root source from a functional selection. -/
noncomputable def choiceOfFunctionalSelection
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (j : N.WithoutLinkageRoot root) : N.ReducedOutgoingReaction root j := by
  classical
  have hne : j.1.1 ≠ root := by
    intro h
    apply j.2
    apply Subtype.ext
    exact h
  let hx := hfun.1 j.1.1 j.1.2 hne
  exact ⟨Classical.choose hx, (Classical.choose_spec hx).1.2⟩

lemma choiceOfFunctionalSelection_mem
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (j : N.WithoutLinkageRoot root) :
    (N.choiceOfFunctionalSelection root T hfun j).1 ∈ T := by
  classical
  have hne : j.1.1 ≠ root := by
    intro h
    apply j.2
    apply Subtype.ext
    exact h
  let hx := hfun.1 j.1.1 j.1.2 hne
  change Classical.choose hx ∈ T
  exact (Classical.choose_spec hx).1.1

lemma functionalSelectionOfChoice_choice_eq
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T) :
    N.functionalSelectionOfChoice root (N.choiceOfFunctionalSelection root T hfun) = T := by
  classical
  ext r
  constructor
  · intro hr
    simp only [functionalSelectionOfChoice, Finset.mem_image] at hr
    rcases hr with ⟨j, _, rfl⟩
    exact N.choiceOfFunctionalSelection_mem root T hfun j
  · intro hrT
    have hclass : N.SameLinkage root (N.sourceIdx r) := hfun.2.2 r hrT
    have hne : N.sourceIdx r ≠ root := hfun.2.1 r hrT
    let j : N.WithoutLinkageRoot root :=
      ⟨⟨N.sourceIdx r, hclass⟩, by
        intro heq
        apply hne
        exact congrArg Subtype.val heq⟩
    have hx := hfun.1 (N.sourceIdx r) hclass hne
    have hr_eq_chosen : r = Classical.choose hx :=
      (Classical.choose_spec hx).2 r ⟨hrT, rfl⟩
    have hchosen :
        (N.choiceOfFunctionalSelection root T hfun j).1 = r := by
      change Classical.choose hx = r
      exact hr_eq_chosen.symm
    simp only [functionalSelectionOfChoice, Finset.mem_image]
    exact ⟨j, Finset.mem_univ _, hchosen⟩

lemma functionalReactionSelectionSets_eq_image_choices
    (N : Network S) (root : N.ComplexIdx) :
    N.functionalReactionSelectionSets root =
      Finset.univ.image (N.functionalSelectionOfChoice root) := by
  classical
  ext T
  simp only [N.mem_functionalReactionSelectionSets_iff, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · intro hfun
    refine ⟨N.choiceOfFunctionalSelection root T hfun, ?_⟩
    exact N.functionalSelectionOfChoice_choice_eq root T hfun
  · rintro ⟨f, rfl⟩
    exact N.functionalSelectionOfChoice_isFunctional root f

/-- The reduced incidence column `e_source - e_target` for one selected reaction. -/
noncomputable def reducedIncidenceColumn
    (N : Network S) (root : N.ComplexIdx)
    (j : N.WithoutLinkageRoot root) (r : N.ReducedOutgoingReaction root j) :
    N.WithoutLinkageRoot root → ℝ :=
  fun i => (if j.1.1 = i.1.1 then (1 : ℝ) else 0) -
    (if N.targetIdx r.1 = i.1.1 then 1 else 0)

lemma linkageReducedOutflowLaplacian_col_eq_sum
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx)
    (j : N.WithoutLinkageRoot root) :
    (fun i => N.linkageReducedOutflowLaplacian κ root i j) =
      ∑ r : N.ReducedOutgoingReaction root j,
        κ.k r.1 • N.reducedIncidenceColumn root j r := by
  classical
  funext i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, reducedIncidenceColumn]
  dsimp [linkageReducedOutflowLaplacian, linkageReducedKineticMatrix,
    linkageKineticMatrix, kineticMatrix]
  let F : N.R → ℝ := fun r => κ.k r *
      ((if j.1.1 = i.1.1 then 1 else 0) -
        (if N.targetIdx r = i.1.1 then 1 else 0))
  have hsub :
      (∑ x : {r : N.R // N.sourceIdx r = j.1.1}, F x.1) =
        ∑ r : N.R, if N.sourceIdx r = j.1.1 then F r else 0 := by
    calc
      (∑ x : {r : N.R // N.sourceIdx r = j.1.1}, F x.1) =
          ∑ r ∈ (Finset.univ.filter fun r : N.R => N.sourceIdx r = j.1.1), F r := by
            symm
            apply Finset.sum_subtype
            intro r
            simp
      _ = ∑ r : N.R, if N.sourceIdx r = j.1.1 then F r else 0 := by
            rw [Finset.sum_filter]
  rw [hsub]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro r _
  by_cases hsrc : N.sourceIdx r = j.1.1
  · simp [hsrc, F]
    ring
  · simp [hsrc, F]

/-- Matrix whose `j`th column is the reduced incidence column of the reaction chosen at `j`. -/
noncomputable def choiceIncidenceMatrix
    (N : Network S) (root : N.ComplexIdx)
    (f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j) :
    Matrix (N.WithoutLinkageRoot root) (N.WithoutLinkageRoot root) ℝ :=
  fun i j => N.reducedIncidenceColumn root j (f j) i

lemma kineticCofactor_eq_sum_choices
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    N.kineticCofactor κ root =
      ∑ f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j,
        (∏ j, κ.k (f j).1) * Matrix.det (N.choiceIncidenceMatrix root f) := by
  classical
  rw [kineticCofactor, ← Matrix.det_transpose]
  let L := N.linkageReducedOutflowLaplacian κ root
  have hrow : ∀ j : N.WithoutLinkageRoot root,
      L.transpose j =
        ∑ r : N.ReducedOutgoingReaction root j,
          κ.k r.1 • N.reducedIncidenceColumn root j r := by
    intro j
    funext i
    change L i j = _
    exact congrFun (N.linkageReducedOutflowLaplacian_col_eq_sum κ root j) i
  change Matrix.det L.transpose = _
  change (Matrix.detRowAlternating :
      (N.WithoutLinkageRoot root → ℝ) [⋀^(N.WithoutLinkageRoot root)]→ₗ[ℝ] ℝ)
      L.transpose = _
  rw [show L.transpose = fun j => ∑ r : N.ReducedOutgoingReaction root j,
      κ.k r.1 • N.reducedIncidenceColumn root j r by
    funext j; exact hrow j]
  change (Matrix.detRowAlternating :
      (N.WithoutLinkageRoot root → ℝ) [⋀^(N.WithoutLinkageRoot root)]→ₗ[ℝ] ℝ).toMultilinearMap
      (fun j => ∑ r : N.ReducedOutgoingReaction root j,
        κ.k r.1 • N.reducedIncidenceColumn root j r) = _
  rw [MultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [MultilinearMap.map_smul_univ]
  simp only [smul_eq_mul]
  congr 1
  change Matrix.det (fun i j => N.reducedIncidenceColumn root i (f i) j) = _
  rw [show (fun i j => N.reducedIncidenceColumn root i (f i) j) =
      (N.choiceIncidenceMatrix root f).transpose by rfl, Matrix.det_transpose]

lemma treeWeight_functionalSelectionOfChoice
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx)
    (f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j) :
    N.treeWeight κ (N.functionalSelectionOfChoice root f) =
      ∏ j, κ.k (f j).1 := by
  classical
  unfold treeWeight functionalSelectionOfChoice
  rw [Finset.prod_image]
  intro j hj k hk hfk
  exact N.functionalSelectionOfChoice_source_unique root f hfk

lemma selectionIncidenceMatrix_functionalSelectionOfChoice
    (N : Network S) (root : N.ComplexIdx)
    (f : ∀ j : N.WithoutLinkageRoot root, N.ReducedOutgoingReaction root j) :
    N.selectionIncidenceMatrix root (N.functionalSelectionOfChoice root f) =
      N.choiceIncidenceMatrix root f := by
  classical
  ext i j
  unfold selectionIncidenceMatrix choiceIncidenceMatrix reducedIncidenceColumn
  rw [Finset.sum_eq_single_of_mem (f j).1 (N.functionalSelectionOfChoice_mem root f j)]
  · simp [(f j).2]
  · intro r hrT hrne
    simp only [functionalSelectionOfChoice, Finset.mem_image] at hrT
    rcases hrT with ⟨k, _, hkr⟩
    have hsrcne : N.sourceIdx r ≠ j.1.1 := by
      intro hsrc
      have hjk : j = k := by
        apply Subtype.ext
        apply Subtype.ext
        exact hsrc.symm.trans (hkr ▸ (f k).2)
      subst k
      apply hrne
      exact hkr.symm
    simp [hsrcne]

/-- **Column-multilinear expansion of the positive kinetic cofactor.**

Each column of the reduced outflow Laplacian is the sum, over reactions leaving that
column's complex, of `κ_r (e_source - e_target)`.  Expanding the determinant therefore
amounts to choosing one outgoing reaction in every non-root column. -/
theorem kineticCofactor_eq_sum_functionalSelections
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    N.kineticCofactor κ root =
      ∑ T ∈ N.functionalReactionSelectionSets root,
        N.treeWeight κ T * Matrix.det (N.selectionIncidenceMatrix root T) := by
  classical
  rw [N.kineticCofactor_eq_sum_choices κ root]
  rw [N.functionalReactionSelectionSets_eq_image_choices root]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro f hf
    rw [N.treeWeight_functionalSelectionOfChoice κ root f,
      N.selectionIncidenceMatrix_functionalSelectionOfChoice root f]
  · intro f hf g hg hfg
    exact N.functionalSelectionOfChoice_injective root hfg


/-- Uniqueness of the selected outgoing reaction at a non-root source. -/
lemma choiceOfFunctionalSelection_eq_of_mem_source
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (j : N.WithoutLinkageRoot root) (r : N.R)
    (hrT : r ∈ T) (hrsrc : N.sourceIdx r = j.1.1) :
    r = (N.choiceOfFunctionalSelection root T hfun j).1 := by
  classical
  have hne : j.1.1 ≠ root := by
    intro h
    apply j.2
    apply Subtype.ext
    exact h
  have hx := hfun.1 j.1.1 j.1.2 hne
  have hr := (Classical.choose_spec hx).2 r ⟨hrT, hrsrc⟩
  have hq := (Classical.choose_spec hx).2
    (N.choiceOfFunctionalSelection root T hfun j).1
    ⟨N.choiceOfFunctionalSelection_mem root T hfun j,
      (N.choiceOfFunctionalSelection root T hfun j).2⟩
  exact hr.trans hq.symm

/-- Along a functional selected edge, the source reaches the root iff its target does. -/
lemma choice_reaches_root_iff_target
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (j : N.WithoutLinkageRoot root) :
    N.SelectedReaches T j.1.1 root ↔
      N.SelectedReaches T
        (N.targetIdx (N.choiceOfFunctionalSelection root T hfun j).1) root := by
  classical
  let q := N.choiceOfFunctionalSelection root T hfun j
  have hqmem : q.1 ∈ T := N.choiceOfFunctionalSelection_mem root T hfun j
  have hqsrc : N.sourceIdx q.1 = j.1.1 := q.2
  have hedgeq : N.SelectedEdge T j.1.1 (N.targetIdx q.1) :=
    ⟨q.1, hqmem, hqsrc, rfl⟩
  constructor
  · intro hreach
    rcases Relation.ReflTransGen.cases_head hreach with heq | ⟨d, hedge, hrest⟩
    · exact False.elim (by
        apply j.2
        apply Subtype.ext
        exact heq)
    · rcases hedge with ⟨r, hrT, hrsrc, hrtgt⟩
      have hrq : r = q.1 :=
        N.choiceOfFunctionalSelection_eq_of_mem_source root T hfun j r hrT hrsrc
      have hd : d = N.targetIdx q.1 := by
        simpa [hrq] using hrtgt.symm
      change N.SelectedReaches T (N.targetIdx q.1) root
      unfold SelectedReaches
      simpa [hd] using hrest
  · intro htarget
    exact Relation.ReflTransGen.head hedgeq htarget

/-- A non-rooted functional selection contains a non-root vertex that does not reach the root. -/
lemma exists_nonreaching_vertex_of_not_rooted
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (hnot : ¬ N.IsRootedInArborescence root T) :
    ∃ j : N.WithoutLinkageRoot root, ¬ N.SelectedReaches T j.1.1 root := by
  classical
  have hfail : ¬ (∀ c : N.ComplexIdx, N.SameLinkage root c →
      N.SelectedReaches T c root) := by
    intro hreach
    exact hnot ⟨hfun.1, hfun.2.1, hfun.2.2, hreach⟩
  push_neg at hfail
  obtain ⟨c, hcclass, hcnreach⟩ := hfail
  have hcne : c ≠ root := by
    intro hcr
    subst c
    exact hcnreach Relation.ReflTransGen.refl
  let j : N.WithoutLinkageRoot root :=
    ⟨⟨c, hcclass⟩, by
      intro h
      apply hcne
      exact congrArg Subtype.val h⟩
  exact ⟨j, hcnreach⟩

/-- The target of the chosen reaction stays in the linkage class. -/
lemma choice_target_sameLinkage
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (j : N.WithoutLinkageRoot root) :
    N.SameLinkage root
      (N.targetIdx (N.choiceOfFunctionalSelection root T hfun j).1) := by
  let q := N.choiceOfFunctionalSelection root T hfun j
  have hq : N.SameLinkage j.1.1 (N.targetIdx q.1) := by
    simpa [q.2] using N.reaction_sameLinkage q.1
  exact Network.Linked.trans j.1.2 hq

/-- Indicator of the part of the functional digraph that does not reach the root. -/
noncomputable def nonreachIndicator
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R) :
    N.WithoutLinkageRoot root → ℝ := by
  classical
  exact fun i => if N.SelectedReaches T i.1.1 root then 0 else 1

/-- The non-reachability indicator annihilates every selected incidence column. -/
lemma nonreachIndicator_dot_reducedIncidenceColumn
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (j : N.WithoutLinkageRoot root) :
    N.nonreachIndicator root T ⬝ᵥ N.reducedIncidenceColumn root j
      (N.choiceOfFunctionalSelection root T hfun j) = 0 := by
  classical
  let q := N.choiceOfFunctionalSelection root T hfun j
  let w := N.nonreachIndicator root T
  have hreach := N.choice_reaches_root_iff_target root T hfun j
  have hsource :
      (∑ i : N.WithoutLinkageRoot root,
        w i * (if j.1.1 = i.1.1 then (1 : ℝ) else 0)) = w j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro i hi hij
      have hv : j.1.1 ≠ i.1.1 := by
        intro h
        apply hij
        apply Subtype.ext
        apply Subtype.ext
        exact h.symm
      simp [hv]
    · simp
  by_cases htroot : N.targetIdx q.1 = root
  · have htReach : N.SelectedReaches T (N.targetIdx q.1) root := by
      rw [htroot]
      exact Relation.ReflTransGen.refl
    have hjReach : N.SelectedReaches T j.1.1 root := hreach.mpr htReach
    have hwj : w j = 0 := by
      simp [w, nonreachIndicator, hjReach]
    have htarget :
        (∑ i : N.WithoutLinkageRoot root,
          w i * (if N.targetIdx q.1 = i.1.1 then (1 : ℝ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hne : N.targetIdx q.1 ≠ i.1.1 := by
        rw [htroot]
        intro hri
        apply i.2
        apply Subtype.ext
        exact hri.symm
      simp [hne]
    unfold dotProduct reducedIncidenceColumn
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsource, htarget, hwj]
    simp
  · have htclass : N.SameLinkage root (N.targetIdx q.1) :=
      N.choice_target_sameLinkage root T hfun j
    let k : N.WithoutLinkageRoot root :=
      ⟨⟨N.targetIdx q.1, htclass⟩, by
        intro h
        apply htroot
        exact congrArg Subtype.val h⟩
    have hkval : k.1.1 = N.targetIdx q.1 := rfl
    have hreachk : N.SelectedReaches T k.1.1 root ↔ N.SelectedReaches T j.1.1 root := by
      rw [hkval]
      exact hreach.symm
    have hwjk : w j = w k := by
      dsimp [w]
      unfold nonreachIndicator
      by_cases hjr : N.SelectedReaches T j.1.1 root
      · have hkr : N.SelectedReaches T k.1.1 root := hreachk.mpr hjr
        simp [hjr, hkr]
      · have hkr : ¬ N.SelectedReaches T k.1.1 root := by
          intro hk
          exact hjr (hreachk.mp hk)
        simp [hjr, hkr]
    have htarget :
        (∑ i : N.WithoutLinkageRoot root,
          w i * (if N.targetIdx q.1 = i.1.1 then (1 : ℝ) else 0)) = w k := by
      rw [Finset.sum_eq_single k]
      · simp [hkval]
      · intro i hi hik
        have hv : N.targetIdx q.1 ≠ i.1.1 := by
          intro h
          apply hik
          apply Subtype.ext
          apply Subtype.ext
          exact (hkval.trans h).symm
        simp [hv]
      · simp
    unfold dotProduct reducedIncidenceColumn
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, hsource, htarget, hwjk]
    simp

/-- A rooted functional selection has unit reduced incidence determinant. -/
lemma det_selectionIncidenceMatrix_eq_one
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hT : N.IsRootedInArborescence root T) :
    Matrix.det (N.selectionIncidenceMatrix root T) = 1 := by
  classical
  let hfun : N.IsFunctionalReactionSelectionSet root T :=
    hT.isFunctionalReactionSelectionSet
  let V := N.WithoutLinkageRoot root
  let r : V → V → Prop := fun a b => N.SelectedReaches T b.1 a.1
  letI : IsPartialOrder V r := {
    refl := fun a => Relation.ReflTransGen.refl
    trans := fun a b c hab hbc => hbc.trans hab
    antisymm := by
      intro a b hab hba
      by_contra hne
      have hne' : b.1.1 ≠ a.1.1 := by
        intro h
        apply hne
        apply Subtype.ext
        apply Subtype.ext
        exact h.symm
      have htrans : Relation.TransGen (N.SelectedEdge T) a.1 b.1 :=
        (Relation.reflTransGen_iff_eq_or_transGen.mp hba).resolve_left hne'
      have hcycle : Relation.TransGen (N.SelectedEdge T) a.1 a.1 :=
        htrans.trans_left hab
      have hroot : N.SelectedReaches T a.1 root := hT.2.2.2 a.1 a.1.2
      exact hT.no_selected_cycle hroot hcycle
  }
  let s : V → V → Prop := (extend_partialOrder r).choose
  have hs : IsLinearOrder V s ∧ r ≤ s := (extend_partialOrder r).choose_spec
  letI : LinearOrder V := {
    le := s
    lt := fun a b => s a b ∧ ¬ s b a
    le_refl := hs.1.refl
    le_trans := hs.1.trans
    le_antisymm := hs.1.antisymm
    le_total := hs.1.total
    lt_iff_le_not_ge := by intro a b; rfl
    toDecidableLE := Classical.decRel _
  }
  let M := N.selectionIncidenceMatrix root T
  have hMchoice : M =
      N.choiceIncidenceMatrix root (N.choiceOfFunctionalSelection root T hfun) := by
    dsimp [M]
    have hset := N.functionalSelectionOfChoice_choice_eq root T hfun
    calc
      N.selectionIncidenceMatrix root T =
          N.selectionIncidenceMatrix root
            (N.functionalSelectionOfChoice root
              (N.choiceOfFunctionalSelection root T hfun)) :=
        congrArg (N.selectionIncidenceMatrix root) hset.symm
      _ = N.choiceIncidenceMatrix root (N.choiceOfFunctionalSelection root T hfun) :=
        N.selectionIncidenceMatrix_functionalSelectionOfChoice root
          (N.choiceOfFunctionalSelection root T hfun)
  have hentry : ∀ i j : V,
      M i j =
        (if j.1.1 = i.1.1 then (1 : ℝ) else 0) -
          (if N.targetIdx (N.choiceOfFunctionalSelection root T hfun j).1 = i.1.1
            then 1 else 0) := by
    intro i j
    rw [hMchoice]
    rfl
  have htri : @Matrix.BlockTriangular V V ℝ this.toLT _ M id := by
    intro i j hji
    rw [hentry i j]
    have hij : j ≠ i := by
      intro h
      subst i
      exact hji.2 hji.1
    have hsrczero : j.1.1 ≠ i.1.1 := by
      intro h
      apply hij
      apply Subtype.ext
      apply Subtype.ext
      exact h
    rw [if_neg hsrczero]
    have htgt : N.targetIdx (N.choiceOfFunctionalSelection root T hfun j).1 ≠ i.1.1 := by
      intro ht
      have hmem := N.choiceOfFunctionalSelection_mem root T hfun j
      have hedge : N.SelectedEdge T j.1 i.1 := by
        refine ⟨(N.choiceOfFunctionalSelection root T hfun j).1, hmem, ?_, ?_⟩
        · exact (N.choiceOfFunctionalSelection root T hfun j).2
        · exact ht
      have hr : r i j := Relation.ReflTransGen.single hedge
      have hsij : s i j := hs.2 i j hr
      exact hji.2 hsij
    simp [htgt]
  calc
    Matrix.det M = ∏ i : V, M i i := Matrix.det_of_upperTriangular htri
    _ = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      rw [hentry i i]
      simp only [if_pos rfl]
      have hmem := N.choiceOfFunctionalSelection_mem root T hfun i
      have hne : N.targetIdx (N.choiceOfFunctionalSelection root T hfun i).1 ≠ i.1.1 := by
        intro ht
        have hback : N.SelectedReaches T
            (N.targetIdx (N.choiceOfFunctionalSelection root T hfun i).1)
            (N.sourceIdx (N.choiceOfFunctionalSelection root T hfun i).1) := by
          rw [ht, (N.choiceOfFunctionalSelection root T hfun i).2]
          exact Relation.ReflTransGen.refl
        exact hT.target_not_reaches_source hmem hback
      simp [hne]

/-- A functional selection that is not rooted has singular reduced incidence matrix. -/
lemma det_selectionIncidenceMatrix_eq_zero
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T)
    (hnot : ¬ N.IsRootedInArborescence root T) :
    Matrix.det (N.selectionIncidenceMatrix root T) = 0 := by
  classical
  let f := N.choiceOfFunctionalSelection root T hfun
  let w := N.nonreachIndicator root T
  have hset := N.functionalSelectionOfChoice_choice_eq root T hfun
  have hMchoice : N.selectionIncidenceMatrix root T = N.choiceIncidenceMatrix root f := by
    calc
      N.selectionIncidenceMatrix root T =
          N.selectionIncidenceMatrix root (N.functionalSelectionOfChoice root f) := by
            rw [hset]
      _ = N.choiceIncidenceMatrix root f :=
        N.selectionIncidenceMatrix_functionalSelectionOfChoice root f
  have hv : w ᵥ* N.choiceIncidenceMatrix root f = 0 := by
    funext j
    change w ⬝ᵥ N.reducedIncidenceColumn root j (f j) = 0
    exact N.nonreachIndicator_dot_reducedIncidenceColumn root T hfun j
  obtain ⟨j, hjbad⟩ := N.exists_nonreaching_vertex_of_not_rooted root T hfun hnot
  have hwj : w j = 1 := by
    simp [w, nonreachIndicator, hjbad]
  have hwne : w ≠ 0 := by
    intro hw0
    have hz := congrFun hw0 j
    rw [hwj] at hz
    norm_num at hz
  rw [hMchoice]
  by_contra hdet
  have hw0 : w = 0 := Matrix.eq_zero_of_vecMul_eq_zero hdet hv
  exact hwne hw0

/-- **Incidence determinant dichotomy for a functional digraph.**

The reduced incidence determinant is `1` exactly for rooted in-arborescences and `0` for
all other functional selections.  In the non-tree case, finiteness plus one outgoing edge
per non-root vertex produces a directed cycle away from the root; summing the corresponding
incidence columns gives a nontrivial linear dependence.  In the tree case, repeatedly remove
a leaf (or topologically order vertices by distance to the root) to obtain a unit-triangular
matrix after simultaneous reindexing. -/
theorem det_selectionIncidenceMatrix
    (N : Network S) (root : N.ComplexIdx) (T : Finset N.R)
    (hfun : N.IsFunctionalReactionSelectionSet root T) :
    Matrix.det (N.selectionIncidenceMatrix root T) =
      (by classical exact if N.IsRootedInArborescence root T then 1 else 0) := by
  classical
  by_cases hT : N.IsRootedInArborescence root T
  · simp [hT, N.det_selectionIncidenceMatrix_eq_one root T hT]
  · simp [hT, N.det_selectionIncidenceMatrix_eq_zero root T hfun hT]

/-- The functional-selection sum collapses exactly to the tree-constant sum. -/
theorem sum_functionalSelections_eq_treeConstant
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    (∑ T ∈ N.functionalReactionSelectionSets root,
        N.treeWeight κ T * Matrix.det (N.selectionIncidenceMatrix root T)) =
      N.treeConstant κ root := by
  classical
  have hfilter :
      (N.functionalReactionSelectionSets root).filter
          (N.IsRootedInArborescence root) =
        N.rootedInArborescences root := by
    ext T
    simp only [Finset.mem_filter, N.mem_functionalReactionSelectionSets_iff,
      N.mem_rootedInArborescences_iff]
    constructor
    · exact fun h => h.2
    · intro hT
      exact ⟨hT.isFunctionalReactionSelectionSet, hT⟩
  calc
    (∑ T ∈ N.functionalReactionSelectionSets root,
        N.treeWeight κ T * Matrix.det (N.selectionIncidenceMatrix root T)) =
        ∑ T ∈ N.functionalReactionSelectionSets root,
          if N.IsRootedInArborescence root T then N.treeWeight κ T else 0 := by
      apply Finset.sum_congr rfl
      intro T hT
      have hfun := (N.mem_functionalReactionSelectionSets_iff root T).1 hT
      rw [N.det_selectionIncidenceMatrix root T hfun]
      by_cases htree : N.IsRootedInArborescence root T
      · simp [htree]
      · simp [htree]
    _ = ∑ T ∈ (N.functionalReactionSelectionSets root).filter
          (N.IsRootedInArborescence root), N.treeWeight κ T := by
      rw [Finset.sum_filter]
    _ = ∑ T ∈ N.rootedInArborescences root, N.treeWeight κ T := by
      rw [hfilter]
    _ = N.treeConstant κ root := by
      rfl

/-- Directed Matrix--Tree theorem obtained from the finite incidence expansion. -/
theorem kineticCofactor_eq_treeConstant_combinatorial
    (N : Network S) (κ : N.RateConstants) (root : N.ComplexIdx) :
    N.kineticCofactor κ root = N.treeConstant κ root := by
  rw [N.kineticCofactor_eq_sum_functionalSelections κ root,
    N.sum_functionalSelections_eq_treeConstant κ root]

end Network
end CRNT
