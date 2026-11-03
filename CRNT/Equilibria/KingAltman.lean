import CRNT.Equilibria.MatrixTreeCofactor
import CRNT.Equilibria.SingletonSource
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The King–Altman formula for unimolecular networks

This module formalizes the **King–Altman formula** (King & Altman, *On the steady state of
chemical reactions*, Proc. Roy. Soc. Lond. A **224** (1954), 342–346) and adds the leaf
**S21** ("the King–Altman formula: the steady state of a unimolecular network as a ratio of
spanning trees") to the field map (`docs/field-map.md`).

## The statement

A **unimolecular** network is a network in which every reaction moves exactly one molecule
from one species to another: the source and the target of every reaction are *singleton*
complexes.  For such a network the mass-action field is **linear**

```
ẋ_s = ( ∑_{r : tgt r = s} κ_r x_{src r} ) − ( ∑_{r : src r = s} κ_r ) x_s
    = (total inflow into s) − (total outflow from s) ,
```

so the steady state is the solution of a *linear* homogeneous system (`singletonSource_vectorField_eq_linear`
of `CRNT.Equilibria.SingletonSource`, used here through `uniFieldMatrix`).

For a network whose reaction graph is **strongly connected** (in the language of the
repository: *weakly reversible* with a *single linkage class*) the steady state is unique up to
scaling and is given by the **King–Altman formula**

```
x*_s = ( ∑_{T ∈ 𝒯_s} ∏_{r ∈ T} κ_r )  /  ( ∑_{T ∈ 𝒯} ∏_{r ∈ T} κ_r ) ,
```

where `𝒯_s` is the set of the **spanning trees of the reaction graph rooted at `s`** (the
spanning trees in which `s` is the unique sink) and `𝒯` is the set of all spanning trees of
the reaction graph.  The numerator is the **tree constant** of the repository
(`CRNT.Network.treeConstant`, the sum of the weights of the rooted in-arborescences of the
linkage class of the root) and, by the directed **Matrix–Tree theorem**
(`CRNT.Equilibria.MatrixTreeCofactor`, `CRNT.Equilibria.DirectedMatrixTreeProof`), it is also
the **cofactor** `CRNT.Network.kineticCofactor` of the outflow Laplacian with the row and the
column of the root deleted.  The denominator is the **total tree weight**, the sum of the
weights of all spanning trees.

## The argument

1. **The field is linear** (`massActionVectorField_linear_of_unimolecular`,
   `massActionVectorField_eq_transfer`): every reaction contributes a *transfer* of one
   molecule from its source species to its target species.

2. **The tree vector is a steady state** (`treeConcentration_isSteadyState`): the monomial
   vector of the *tree concentration* — the vector of the tree constants, read at the species —
   is the *tree-constant vector* of the repository, and the latter annihilates the kinetic map
   (`CRNT.Network.treeConstant_kineticKernel`, the "tree equations" of the Matrix–Tree
   theorem).  Since the field factors through the kinetic map
   (`CRNT.Network.massActionVectorField_eq`), the tree concentration is a steady state.

3. **The total tree weight** (`totalTreeWeight`) is the sum of the tree constants over all
   roots; by `totalTreeWeight_eq_sum_spanningTreeWeights` it is the sum of the weights of all
   spanning trees of the reaction graph, each spanning tree being counted once, at its unique
   sink (`root_unique`).

4. **The formula** (`kingAltman`): the *normalized* steady state (`kingAltmanSteadyState`) is
   the tree constant at `s` divided by the total tree weight; equivalently the cofactor ratio
   of the Matrix–Tree theorem.  The ratio is **independent of the choice of a spanning tree**
   (`kingAltman_ratio`): it is a ratio of *sums* of tree weights, and the sum over the trees
   rooted at `s` is exactly the cofactor.

5. **Positivity and uniqueness** (`kingAltmanSteadyState_pos`,
   `eq_zero_of_le_zero_of_kineticKernel`, `exists_smul_eq_of_positive_kineticKernel`,
   `exists_pos_mul_eq_kingAltmanSteadyState`): the tree constants are strictly positive on a
   weakly reversible network
   (`CRNT.Network.treeConstant_pos_of_weaklyReversible`), so the King–Altman steady state is
   strictly positive; and the maximum principle for the balance equations of the reaction
   graph shows that two positive vectors in the kernel of the kinetic map are proportional, so
   the positive steady state is unique up to scaling.

6. **An instance** (`CRNT.Examples.KingAltman`): the reversible pair `X ⇌ Y`.  The spanning
   trees are counted by hand (there are exactly two, one rooted at `X` and one rooted at `Y`),
   and the King–Altman ratio is checked against the directly computed steady state.

## Conventions

The reaction direction is the one of the repository: `Reaction.source` is the *reactant* side
and `Reaction.target` the *product* side, so that

```
ẋ_s = ∑_r κ_r x^{src r} ( (tgt r)_s − (src r)_s ) .
```

For a unimolecular network this is the transfer of one molecule from the source species to
the target species; the mass-action monomial of a singleton source complex is the
corresponding concentration (`massActionMonomial_of_isSingleton`).
-/

namespace CRNT

namespace Network

open scoped BigOperators
open Matrix

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Unimolecular networks -/

/-- A reaction is **unimolecular** when it moves exactly one molecule from one species to
another: both its source and its target are singleton complexes. -/
def IsUnimolecular (r : Reaction S) : Prop :=
  (∃ i : S, r.source = singletonComplex i) ∧ (∃ j : S, r.target = singletonComplex j)

/-- A network is **unimolecular** when every reaction moves exactly one molecule from one
species to another.  The mass-action field of such a network is linear. -/
def Unimolecular (N : Network S) : Prop :=
  ∀ r : N.R, IsUnimolecular (N.reaction r)

omit [Fintype S] in
/-- The source complex of a unimolecular reaction is a singleton complex. -/
theorem IsUnimolecular.source_singleton {r : Reaction S} (h : IsUnimolecular r) :
    ∃ i : S, r.source = singletonComplex i :=
  h.1

omit [Fintype S] in
/-- The target complex of a unimolecular reaction is a singleton complex. -/
theorem IsUnimolecular.target_singleton {r : Reaction S} (h : IsUnimolecular r) :
    ∃ j : S, r.target = singletonComplex j :=
  h.2

/-- The **source species** of a reaction of a unimolecular network: the unique species whose
singleton complex is the source of the reaction. -/
noncomputable def uniSource (N : Network S) (h : N.Unimolecular) (r : N.R) : S :=
  Classical.choose ((h r).source_singleton)

/-- The **target species** of a reaction of a unimolecular network: the unique species whose
singleton complex is the target of the reaction. -/
noncomputable def uniTarget (N : Network S) (h : N.Unimolecular) (r : N.R) : S :=
  Classical.choose ((h r).target_singleton)

/-- The source complex of a reaction of a unimolecular network is the singleton complex at
its source species. -/
theorem uniSource_spec (N : Network S) (h : N.Unimolecular) (r : N.R) :
    (N.reaction r).source = singletonComplex (N.uniSource h r) :=
  (h r).source_singleton.choose_spec

/-- The target complex of a reaction of a unimolecular network is the singleton complex at
its target species. -/
theorem uniTarget_spec (N : Network S) (h : N.Unimolecular) (r : N.R) :
    (N.reaction r).target = singletonComplex (N.uniTarget h r) :=
  (h r).target_singleton.choose_spec

omit [Fintype S] in
/-- A complex that is the singleton complex at a species is a singleton at that species. -/
theorem IsSingleton_of_eq_singletonComplex {y : Complex S} {i : S}
    (h : y = singletonComplex i) : IsSingleton y i := by
  refine ⟨?_, ?_⟩
  · rw [h]
    simp [singletonComplex]
  · intro j hj
    rw [h]
    simp [singletonComplex, hj]

/-- A unimolecular network is a SingletonSource network: every source complex is a singleton. -/
theorem Unimolecular.singletonSource (N : Network S) (h : N.Unimolecular) : N.SingletonSource := by
  intro r
  obtain ⟨i, hi⟩ := (h r).source_singleton
  refine ⟨i, ?_⟩
  exact IsSingleton_of_eq_singletonComplex hi

/-- **Every complex of a unimolecular network is a singleton complex.** -/
theorem complex_eq_singleton_of_unimolecular (N : Network S) (h : N.Unimolecular)
    (c : N.ComplexIdx) : ∃ j : S, c.val = singletonComplex j := by
  rcases Finset.mem_union.mp c.property with hsrc | htgt
  · obtain ⟨r, _, hsrc⟩ := Finset.mem_image.mp hsrc
    obtain ⟨i, hi⟩ := (h r).source_singleton
    exact ⟨i, hsrc.symm.trans hi⟩
  · obtain ⟨r, _, htgt⟩ := Finset.mem_image.mp htgt
    obtain ⟨j, hj⟩ := (h r).target_singleton
    exact ⟨j, htgt.symm.trans hj⟩

/-! ## The mass-action field of a unimolecular network is linear -/

/-- The **linear coefficient matrix** of the mass-action field of a unimolecular network: its
`(s, t)`-entry is the coefficient of `x t` in the `s`-th component of the field. -/
noncomputable def uniFieldMatrix (N : Network S) (κ : N.RateConstants) : Matrix S S ℝ :=
  fun s t => singletonSourceCoeff N κ t s

/-- **The mass-action field of a unimolecular network is the linear map given by
`uniFieldMatrix`.** -/
theorem massActionVectorField_eq_uniFieldMatrix_mulVec (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) (x : Concentration S) :
    N.massActionVectorField κ x = N.uniFieldMatrix κ *ᵥ x := by
  rw [N.singletonSource_vectorField_eq_linear κ h.singletonSource x]
  funext s
  rfl

/-- **The mass-action field of a unimolecular network is linear.**  There is a matrix `A`
(the *linear coefficient matrix* `uniFieldMatrix`) such that the field of the network is
`x ↦ A *ᵥ x`; in particular there is no constant term. -/
theorem massActionVectorField_linear_of_unimolecular (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) :
    ∃ A : Matrix S S ℝ, ∀ x, N.massActionVectorField κ x = A *ᵥ x :=
  ⟨N.uniFieldMatrix κ, fun x => N.massActionVectorField_eq_uniFieldMatrix_mulVec κ h x⟩

/-- **The field of a unimolecular network is a sum of transfers.**  At the species `s` the
field is the total inflow into `s` minus the total outflow from `s`: a reaction `i → j` with
rate constant `κ` transfers one molecule from the species `i` to the species `j`.  This is
the explicit form of the linearity of the field. -/
theorem massActionVectorField_eq_transfer (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) (x : Concentration S) (s : S) :
    N.massActionVectorField κ x s =
      (∑ r : N.R, if N.uniTarget h r = s then κ.k r * x (N.uniSource h r) else 0) -
      (∑ r : N.R, if N.uniSource h r = s then κ.k r * x s else 0) := by
  classical
  have hrate : ∀ r : N.R, N.massActionRate κ r x = κ.k r * x (N.uniSource h r) := by
    intro r
    rw [N.massActionRate_eq, N.complexMonomialVector_apply]
    change κ.k r * (N.reaction r).source.massActionMonomial x = κ.k r * x (N.uniSource h r)
    rw [N.uniSource_spec h r, massActionMonomial_of_isSingleton x
      (isSingleton_singletonComplex (N.uniSource h r))]
  have hvec : ∀ r : N.R, N.reactionVector r s =
      ((if N.uniTarget h r = s then 1 else 0) : ℝ) - ((if N.uniSource h r = s then 1 else 0) : ℝ) := by
    intro r
    rw [N.reactionVector_apply]
    have ht : ((N.reaction r).target s : ℝ) = (if N.uniTarget h r = s then 1 else 0) := by
      rw [N.uniTarget_spec h r]
      by_cases hst : s = N.uniTarget h r
      · simp [singletonComplex, hst]
      · simp [singletonComplex, hst, Ne.symm hst]
    have hs : ((N.reaction r).source s : ℝ) = (if N.uniSource h r = s then 1 else 0) := by
      rw [N.uniSource_spec h r]
      by_cases hst : s = N.uniSource h r
      · simp [singletonComplex, hst]
      · simp [singletonComplex, hst, Ne.symm hst]
    rw [ht, hs]
  rw [N.massActionVectorField_apply]
  simp_rw [hrate, hvec]
  calc (∑ r : N.R, κ.k r * x (N.uniSource h r) *
        ((if N.uniTarget h r = s then 1 else 0) - (if N.uniSource h r = s then 1 else 0)))
      = ∑ r : N.R, ((if N.uniTarget h r = s then κ.k r * x (N.uniSource h r) else 0)
          - (if N.uniSource h r = s then κ.k r * x (N.uniSource h r) else 0)) := by
        apply Finset.sum_congr rfl
        intro r _
        by_cases hP : N.uniTarget h r = s <;> by_cases hQ : N.uniSource h r = s <;>
          simp [hP, hQ]
    _ = (∑ r : N.R, if N.uniTarget h r = s then κ.k r * x (N.uniSource h r) else 0)
          - ∑ r : N.R, if N.uniSource h r = s then κ.k r * x (N.uniSource h r) else 0 := by
        rw [Finset.sum_sub_distrib]
    _ = (∑ r : N.R, if N.uniTarget h r = s then κ.k r * x (N.uniSource h r) else 0)
          - ∑ r : N.R, if N.uniSource h r = s then κ.k r * x s else 0 := by
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        by_cases hQ : N.uniSource h r = s
        · simp [hQ]
        · simp [hQ]

/-! ## The tree-constant concentration is a steady state -/

set_option linter.unusedVariables false in
/-- The **tree-constant concentration** of a unimolecular network: at a species `s` that
occurs in the network it is the tree constant of the complex `singletonComplex s` — the sum
of the weights of the spanning trees of the reaction graph rooted at `s` — and `0` at the
species that do not occur.

The hypothesis `h` is part of the interface: the object is the *species-level* reading of
the tree constants, which is meaningful only when every complex is a singleton complex. -/
noncomputable def treeConcentration (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) : Concentration S :=
  fun s => if hs : singletonComplex s ∈ N.complexes then
      N.treeConstant κ ⟨singletonComplex s, hs⟩ else 0

/-- At an occurring species the tree concentration is the tree constant of the
corresponding complex. -/
theorem treeConcentration_of_occurs (N : Network S) (κ : N.RateConstants) (h : N.Unimolecular)
    {s : S} (hs : singletonComplex s ∈ N.complexes) :
    N.treeConcentration κ h s = N.treeConstant κ ⟨singletonComplex s, hs⟩ := by
  simp [treeConcentration, hs]

/-- At a species that does not occur the tree concentration vanishes. -/
theorem treeConcentration_eq_zero_of_not_occurs (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) {s : S} (hs : singletonComplex s ∉ N.complexes) :
    N.treeConcentration κ h s = 0 := by
  simp [treeConcentration, hs]

/-- **The monomial vector of the tree concentration is the tree-constant vector.**  For a
unimolecular network every complex is a singleton complex, so the mass-action monomial of a
complex is the concentration of the corresponding species. -/
theorem complexMonomialVector_treeConcentration (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) (c : N.ComplexIdx) :
    N.complexMonomialVector (N.treeConcentration κ h) c = N.treeConstant κ c := by
  obtain ⟨j, hj⟩ := N.complex_eq_singleton_of_unimolecular h c
  have hjmem : singletonComplex j ∈ N.complexes := by
    rw [← hj]
    exact c.property
  have hmono : c.val.massActionMonomial (N.treeConcentration κ h)
      = N.treeConcentration κ h j := by
    rw [hj]
    exact massActionMonomial_of_isSingleton (N.treeConcentration κ h)
      (isSingleton_singletonComplex j)
  rw [N.complexMonomialVector_apply, hmono, N.treeConcentration_of_occurs κ h hjmem]
  congr 1
  apply Subtype.ext
  exact hj.symm

/-- **The tree concentration is a steady state of a unimolecular network.**  This is the
"tree equations" of the directed Matrix--Tree theorem in the language of concentrations: the
vector of the tree constants lies in the kernel of the kinetic map, hence in the kernel of
the mass-action field. -/
theorem treeConcentration_isSteadyState (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) : N.IsMassActionSteadyState κ (N.treeConcentration κ h) := by
  show ∀ s : S, N.massActionVectorField κ (N.treeConcentration κ h) s = 0
  rw [N.massActionVectorField_eq κ (N.treeConcentration κ h)]
  have hmono : N.complexMonomialVector (N.treeConcentration κ h) = N.treeConstantVector κ := by
    funext c
    exact N.complexMonomialVector_treeConcentration κ h c
  rw [hmono, N.treeConstant_kineticKernel κ, map_zero]
  intro s
  rfl

/-- **The species-level steady-state condition is the complex-level kinetic-kernel
condition** for a unimolecular network: every complex is a singleton complex, so the
complex map detects the vanishing of the kinetic map. -/
theorem kineticMap_eq_zero_of_isSteadyState (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) :
    N.kineticMap κ (N.complexMonomialVector x) = 0 := by
  classical
  have hx' : ∀ s : S, N.massActionVectorField κ x s = 0 := hx
  rw [N.massActionVectorField_eq κ x] at hx'
  have hmap : N.complexMap (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
    funext s
    exact hx' s
  -- the complexes of the network are singleton complexes, so the complex map is injective
  have hinj : ∀ w : N.ComplexIdx → ℝ, N.complexMap w = 0 → w = 0 := by
    intro w hw
    funext c
    obtain ⟨j, hj⟩ := N.complex_eq_singleton_of_unimolecular h c
    have hjmem : singletonComplex j ∈ N.complexes := by
      rw [← hj]
      exact c.property
    -- the only complex contributing to the `j`-th coordinate is `singletonComplex j`
    have hmain : N.complexMap w j = w c := by
      rw [N.complexMap_apply]
      have hzero : ∀ c' : N.ComplexIdx, c' ≠ c → (c'.val j : ℝ) = 0 := by
        intro c' hc'
        obtain ⟨j', hj'⟩ := N.complex_eq_singleton_of_unimolecular h c'
        have hval : c'.val = singletonComplex j' := hj'
        have hne : j' ≠ j := by
          intro hjj
          subst hjj
          apply hc'
          apply Subtype.ext
          rw [hval, hj]
        rw [hval]
        simp [singletonComplex, Ne.symm hne]
      have hone : (c.val j : ℝ) = 1 := by
        rw [hj]
        simp [singletonComplex]
      rw [Finset.sum_eq_single c]
      · simp [hone]
      · intro c' _ hc'
        simp [hzero c' hc']
      · intro h
        exact absurd (Finset.mem_univ c) h
    have hwj := congrFun hw j
    rw [hmain] at hwj
    exact hwj
  exact hinj _ hmap

/-! ## The total tree weight -/

/-- The **total tree weight** of a network: the sum of the tree constants over all roots,
i.e. the sum of the weights of the spanning trees of the reaction graph, each spanning tree
being counted once, at its unique sink. -/
noncomputable def totalTreeWeight (N : Network S) (κ : N.RateConstants) : ℝ :=
  ∑ c : N.ComplexIdx, N.treeConstant κ c

/-- **The total tree weight is the sum of the tree concentrations.**  The complexes of a
unimolecular network are in bijection with the occurring species, so the two sums agree. -/
theorem sum_treeConcentration_eq_totalTreeWeight (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) :
    (∑ s : S, N.treeConcentration κ h s) = N.totalTreeWeight κ := by
  classical
  show (∑ s : S, N.treeConcentration κ h s) = ∑ c : N.ComplexIdx, N.treeConstant κ c
  have hzeros : ∀ s : S, singletonComplex s ∉ N.complexes → N.treeConcentration κ h s = 0 := by
    intro s hs
    exact N.treeConcentration_eq_zero_of_not_occurs κ h hs
  have hfilter : (∑ s : S, N.treeConcentration κ h s)
      = ∑ s ∈ (Finset.univ.filter (fun s => singletonComplex s ∈ N.complexes)),
          N.treeConcentration κ h s := by
    have h1 : (∑ s : S, N.treeConcentration κ h s)
        = ∑ s : S, (if singletonComplex s ∈ N.complexes then N.treeConcentration κ h s else 0) := by
      apply Finset.sum_congr rfl
      intro s _
      by_cases hs : singletonComplex s ∈ N.complexes
      · simp [hs]
      · simp [hs, hzeros s hs]
    rw [h1, ← Finset.sum_filter]
  rw [hfilter]
  refine Finset.sum_bij
    (s := Finset.univ.filter (fun s => singletonComplex s ∈ N.complexes))
    (t := (Finset.univ : Finset N.ComplexIdx))
    (f := fun s => N.treeConcentration κ h s) (g := fun c => N.treeConstant κ c)
    (fun s (hs : s ∈ Finset.univ.filter (fun t => singletonComplex t ∈ N.complexes)) =>
      ⟨singletonComplex s,
        ((Finset.mem_filter (s := Finset.univ)
          (p := fun t => singletonComplex t ∈ N.complexes)).mp hs).2⟩) ?_ ?_ ?_ ?_
  · intro s hs
    simp
  · intro s₁ hs₁ s₂ hs₂ heq
    apply singletonComplex_inj
    exact congrArg Subtype.val heq
  · intro c hc
    obtain ⟨j, hj⟩ := N.complex_eq_singleton_of_unimolecular h c
    have hjmem : singletonComplex j ∈ N.complexes := by
      rw [← hj]
      exact c.property
    refine ⟨j, (Finset.mem_filter (s := Finset.univ)
      (p := fun t => singletonComplex t ∈ N.complexes)).mpr
      ⟨Finset.mem_univ j, hjmem⟩, ?_⟩
    apply Subtype.ext
    exact hj.symm
  · intro s hs
    have hmem : singletonComplex s ∈ N.complexes :=
      ((Finset.mem_filter (s := Finset.univ)
        (p := fun t => singletonComplex t ∈ N.complexes)).mp hs).2
    rw [N.treeConcentration_of_occurs κ h hmem]

/-! ## The King--Altman formula -/

/-- **The mass-action field of a unimolecular network is linear in the concentration.** -/
theorem massActionVectorField_smul (N : Network S) (κ : N.RateConstants) (h : N.Unimolecular)
    (c : ℝ) (x : Concentration S) :
    N.massActionVectorField κ (c • x) = c • N.massActionVectorField κ x := by
  rw [N.massActionVectorField_eq_uniFieldMatrix_mulVec κ h (c • x),
    N.massActionVectorField_eq_uniFieldMatrix_mulVec κ h x]
  funext s
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  calc (∑ j, N.uniFieldMatrix κ s j * (c * x j))
      = ∑ j, c * (N.uniFieldMatrix κ s j * x j) := by
        apply Finset.sum_congr rfl
        intro j _
        ring
    _ = c * ∑ j, N.uniFieldMatrix κ s j * x j := by
        rw [Finset.mul_sum]

/-- The **normalized King--Altman steady state** of a unimolecular network: the tree
concentration divided by the total tree weight. -/
noncomputable def kingAltmanSteadyState (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) : Concentration S :=
  fun s => N.treeConcentration κ h s / N.totalTreeWeight κ

/-- **The King--Altman steady state is a steady state.** -/
theorem kingAltmanSteadyState_isSteadyState (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) :
    N.IsMassActionSteadyState κ (N.kingAltmanSteadyState κ h) := by
  show ∀ s : S, N.massActionVectorField κ (N.kingAltmanSteadyState κ h) s = 0
  have hs : N.IsMassActionSteadyState κ (N.treeConcentration κ h) :=
    N.treeConcentration_isSteadyState κ h
  have heq : N.kingAltmanSteadyState κ h
      = (N.totalTreeWeight κ)⁻¹ • (N.treeConcentration κ h) := by
    funext s
    simp only [kingAltmanSteadyState, Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [heq]
  intro s
  rw [N.massActionVectorField_smul κ h]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hs s]
  ring

/-- **The King--Altman steady state has total concentration one.** -/
theorem kingAltmanSteadyState_sum_eq_one (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) (hpos : 0 < N.totalTreeWeight κ) :
    (∑ s : S, N.kingAltmanSteadyState κ h s) = 1 := by
  have hsum : (∑ s : S, N.treeConcentration κ h s) = N.totalTreeWeight κ :=
    N.sum_treeConcentration_eq_totalTreeWeight κ h
  unfold kingAltmanSteadyState
  rw [← Finset.sum_div, hsum, div_self (ne_of_gt hpos)]

/-- **The King--Altman steady state is positive at the occurring species** of a weakly
reversible network: the tree constants are strictly positive there. -/
theorem kingAltmanSteadyState_pos (N : Network S) (κ : N.RateConstants) (h : N.Unimolecular)
    (hwr : N.WeaklyReversible) {s : S} (hs : singletonComplex s ∈ N.complexes)
    (hpos : 0 < N.totalTreeWeight κ) : 0 < N.kingAltmanSteadyState κ h s := by
  have htc : 0 < N.treeConstant κ ⟨singletonComplex s, hs⟩ :=
    N.treeConstant_pos_of_weaklyReversible κ hwr ⟨singletonComplex s, hs⟩
  have htcn : 0 < N.treeConcentration κ h s := by
    rw [N.treeConcentration_of_occurs κ h hs]
    exact htc
  unfold kingAltmanSteadyState
  exact div_pos htcn hpos

/-- **The King--Altman formula.**  The steady state of a unimolecular network is the ratio
of the tree sums: at an occurring species `s` it is the sum of the weights of the spanning
trees of the reaction graph rooted at `s`, divided by the total weight of all spanning
trees.  The numerator is the **cofactor** of the outflow Laplacian with the row and the
column of `s` deleted, by the directed Matrix--Tree theorem. -/
theorem kingAltman (N : Network S) (κ : N.RateConstants) (h : N.Unimolecular)
    {s : S} (hs : singletonComplex s ∈ N.complexes) :
    N.kingAltmanSteadyState κ h s =
      N.kineticCofactor κ ⟨singletonComplex s, hs⟩ / N.totalTreeWeight κ := by
  unfold kingAltmanSteadyState
  rw [N.treeConcentration_of_occurs κ h hs, N.kineticCofactor_eq_treeConstant κ]

/-- **The King--Altman formula, in the spanning-tree form.**  The numerator of the ratio is
the sum of the weights of the spanning trees rooted at the species. -/
theorem kingAltman_eq_treeSum (N : Network S) (κ : N.RateConstants) (h : N.Unimolecular)
    {s : S} (hs : singletonComplex s ∈ N.complexes) :
    N.kingAltmanSteadyState κ h s =
      (∑ T ∈ N.rootedInArborescences ⟨singletonComplex s, hs⟩, N.treeWeight κ T) /
        N.totalTreeWeight κ := by
  unfold kingAltmanSteadyState
  rw [N.treeConcentration_of_occurs κ h hs]
  rfl

/-- **The King--Altman ratio is independent of the choice of a spanning tree.**  It is the
ratio of the *sums* of the tree weights, the numerator being the cofactor of the
Matrix--Tree theorem; hence the ratio does not depend on which spanning tree is used to
represent it. -/
theorem kingAltman_ratio (N : Network S) (κ : N.RateConstants) (h : N.Unimolecular)
    (hwr : N.WeaklyReversible) (hpos : 0 < N.totalTreeWeight κ)
    {s t : S} (hs : singletonComplex s ∈ N.complexes) (ht : singletonComplex t ∈ N.complexes) :
    N.kingAltmanSteadyState κ h s / N.kingAltmanSteadyState κ h t =
      N.kineticCofactor κ ⟨singletonComplex s, hs⟩ / N.kineticCofactor κ ⟨singletonComplex t, ht⟩ := by
  have hsc : 0 < N.kineticCofactor κ ⟨singletonComplex s, hs⟩ := by
    rw [N.kineticCofactor_eq_treeConstant κ]
    exact N.treeConstant_pos_of_weaklyReversible κ hwr ⟨singletonComplex s, hs⟩
  have htc : 0 < N.kineticCofactor κ ⟨singletonComplex t, ht⟩ := by
    rw [N.kineticCofactor_eq_treeConstant κ]
    exact N.treeConstant_pos_of_weaklyReversible κ hwr ⟨singletonComplex t, ht⟩
  rw [N.kingAltman κ h hs, N.kingAltman κ h ht]
  field_simp

/-- **The tree constant is the weight of the unique spanning tree**, when the rooted
in-arborescence is unique. -/
theorem treeConstant_eq_of_unique_arborescence (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) (T : Finset N.R) (hT : N.IsRootedInArborescence root T)
    (huniq : ∀ U : Finset N.R, N.IsRootedInArborescence root U → U = T) :
    N.treeConstant κ root = N.treeWeight κ T := by
  classical
  have hmem : T ∈ N.rootedInArborescences root :=
    (N.mem_rootedInArborescences_iff root T).2 hT
  have hfinset : N.rootedInArborescences root = {T} := by
    ext U
    constructor
    · intro hU
      have hUT : U = T := huniq U ((N.mem_rootedInArborescences_iff root U).1 hU)
      simp [hUT]
    · intro hU
      have hUT : U = T := Finset.mem_singleton.mp hU
      subst hUT
      exact hmem
  show (∑ U ∈ N.rootedInArborescences root, N.treeWeight κ U) = N.treeWeight κ T
  rw [hfinset]
  simp

/-! ## Spanning trees and the total tree weight -/

/-- A **spanning tree** of the reaction graph of a network: a set of reactions in which every
complex but one has exactly one selected outgoing reaction, the exceptional complex has
none, and every complex reaches it.  Equivalently, a rooted in-arborescence of some root. -/
def IsSpanningTree (N : Network S) (T : Finset N.R) : Prop :=
  ∃ root : N.ComplexIdx, N.IsRootedInArborescence root T

/-- The finite set of spanning trees of the reaction graph. -/
noncomputable def spanningTrees (N : Network S) : Finset (Finset N.R) := by
  classical
  exact Finset.univ.filter (N.IsSpanningTree)

@[simp] theorem mem_spanningTrees_iff (N : Network S) (T : Finset N.R) :
    T ∈ N.spanningTrees ↔ N.IsSpanningTree T := by
  classical
  simp [spanningTrees]

/-- **Every spanning tree of a network with a single linkage class has a unique root.**  The
root is the unique sink of the tree, i.e. the unique complex with no selected outgoing
reaction; it is the complex at which the tree is counted in the total tree weight. -/
theorem root_unique (N : Network S) (h1 : N.HasSingleLinkageClass) {T : Finset N.R}
    {c c' : N.ComplexIdx} (hT : N.IsRootedInArborescence c T)
    (hT' : N.IsRootedInArborescence c' T) : c = c' := by
  classical
  -- the two roots are in the same linkage class
  have hlink : N.SameLinkage c' c := by
    by_cases hempty : T = ∅
    · subst hempty
      -- the linkage class of `c` is `{c}`
      have hcl : ∀ x : N.ComplexIdx, N.SameLinkage c x → x = c := by
        intro x hx
        by_contra hne
        obtain ⟨r, hr, -⟩ := hT.1 x hx hne
        exact absurd hr (by simp)
      have hmem : N.SameLinkage c c' := by
        show N.Linked c.1 c'.1
        exact h1 c c'
      have hcc : c' = c := hcl c' hmem
      show N.Linked c'.1 c.1
      rw [hcc]
    · obtain ⟨r, hr⟩ := (Finset.nonempty_iff_ne_empty.mpr hempty).exists_mem
      have hl1 : N.SameLinkage c (N.sourceIdx r) := hT.2.2.1 r hr
      have hl2 : N.SameLinkage c' (N.sourceIdx r) := hT'.2.2.1 r hr
      show N.Linked c'.1 c.1
      exact Network.Linked.symm (Network.Linked.trans
        (show N.Linked c.1 (N.sourceIdx r).1 from hl1)
        (Network.Linked.symm (show N.Linked c'.1 (N.sourceIdx r).1 from hl2)))
  -- the second clause of the arborescence at `c` excludes a reaction out of `c`
  by_contra hne
  obtain ⟨r, ⟨hr, hsrc⟩, -⟩ := hT'.1 c hlink hne
  exact hT.2.1 r hr hsrc

/-- **The total tree weight is the sum of the weights of all spanning trees.**  Each
spanning tree is counted once, at its unique root (its unique sink), so the sum of the tree
constants over the roots is the sum of the weights of the spanning trees. -/
theorem totalTreeWeight_eq_sum_spanningTreeWeights (N : Network S) (κ : N.RateConstants)
    (h1 : N.HasSingleLinkageClass) :
    N.totalTreeWeight κ = ∑ T ∈ N.spanningTrees, N.treeWeight κ T := by
  classical
  -- the trees rooted at `c` are among the spanning trees
  have hsub (c : N.ComplexIdx) : N.rootedInArborescences c ⊆ N.spanningTrees := by
    intro T hT
    rw [N.mem_spanningTrees_iff]
    exact ⟨c, (N.mem_rootedInArborescences_iff c T).1 hT⟩
  calc
    (∑ c : N.ComplexIdx, N.treeConstant κ c)
      = ∑ c : N.ComplexIdx, ∑ T ∈ N.rootedInArborescences c, N.treeWeight κ T := rfl
    _ = ∑ c : N.ComplexIdx, ∑ T ∈ N.spanningTrees,
          (if T ∈ N.rootedInArborescences c then N.treeWeight κ T else 0) := by
        apply Finset.sum_congr rfl
        intro c _
        have hfilter : N.spanningTrees.filter (fun T => T ∈ N.rootedInArborescences c)
            = N.rootedInArborescences c := by
          ext T
          constructor
          · intro h
            exact (Finset.mem_filter.mp h).2
          · intro h
            exact Finset.mem_filter.mpr ⟨hsub c h, h⟩
        rw [← Finset.sum_filter, hfilter]
    _ = ∑ T ∈ N.spanningTrees, ∑ c : N.ComplexIdx,
          (if T ∈ N.rootedInArborescences c then N.treeWeight κ T else 0) := by
      rw [Finset.sum_comm]
    _ = ∑ T ∈ N.spanningTrees, N.treeWeight κ T := by
      apply Finset.sum_congr rfl
      intro T hT
      obtain ⟨c₀, hc₀⟩ := (N.mem_spanningTrees_iff T).1 hT
      have hc₀mem : T ∈ N.rootedInArborescences c₀ :=
        (N.mem_rootedInArborescences_iff c₀ T).2 hc₀
      have hsingle : (∑ c : N.ComplexIdx,
          (if T ∈ N.rootedInArborescences c then N.treeWeight κ T else 0))
          = N.treeWeight κ T := by
        have hsum := Finset.sum_eq_single_of_mem
          (f := fun c => if T ∈ N.rootedInArborescences c then N.treeWeight κ T else 0)
          c₀ (Finset.mem_univ _)
          (fun c _ hne => by
            by_cases hc : T ∈ N.rootedInArborescences c
            · exact (hne (root_unique N h1 ((N.mem_rootedInArborescences_iff c T).1 hc) hc₀)).elim
            · simp [hc])
        rw [hsum]
        simp [hc₀mem]
      exact hsingle

/-! ## Uniqueness of the positive steady state -/

/-- **The reaction graph of the network is strongly connected**: every complex reaches every
other complex.  For a weakly reversible network this is equivalent to having a single
linkage class. -/
def StronglyConnected (N : Network S) : Prop :=
  ∀ c d : N.ComplexIdx, N.Reaches c.1 d.1

/-- A weakly reversible network with a single linkage class has a strongly connected
reaction graph: within a linkage class, weak reversibility makes the reachability
symmetric. -/
theorem stronglyConnected_of_weaklyReversible_of_singleLinkageClass (N : Network S)
    (hwr : N.WeaklyReversible) (h1 : N.HasSingleLinkageClass) : N.StronglyConnected := by
  intro c d
  exact hwr.reaches_of_linked (h1 c d)

/-- **The maximum principle for the balance equations.**  If `w` is a nonpositive vector in
the kernel of the kinetic map and vanishes at `y`, then it vanishes at every source of a
reaction into `y`: the balance equation at `y` is a sum of nonpositive terms which
vanishes, so every term vanishes. -/
theorem eq_zero_of_le_zero_of_kineticKernel (N : Network S) (κ : N.RateConstants)
    {w : N.ComplexIdx → ℝ} (hwle : ∀ c, w c ≤ 0) (hker : N.kineticMap κ w = 0)
    {y : N.ComplexIdx} (hy : w y = 0) (r : N.R) (htarget : N.targetIdx r = y) :
    w (N.sourceIdx r) = 0 := by
  classical
  have hy' : (N.kineticMap κ w) y = 0 := by
    rw [hker]
    rfl
  rw [N.kineticMap_apply] at hy'
  -- split the balance equation into the inflow and the outflow
  have hsplit : (∑ r' : N.R, κ.k r' * w (N.sourceIdx r') *
        ((if N.targetIdx r' = y then 1 else 0) - (if N.sourceIdx r' = y then 1 else 0)))
      = (∑ r' : N.R, if N.targetIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0)
        - (∑ r' : N.R, if N.sourceIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r' _
    by_cases hP : N.targetIdx r' = y <;> by_cases hQ : N.sourceIdx r' = y <;>
      simp [hP, hQ]
  -- the outflow term vanishes because `w y = 0`
  have hS2 : (∑ r' : N.R, if N.sourceIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0) = 0 := by
    apply Finset.sum_eq_zero
    intro r' _
    by_cases hc : N.sourceIdx r' = y
    · rw [ite_eq_left hc, hc, hy]
      ring
    · rw [ite_eq_right hc]
  -- hence the inflow term vanishes
  have hS1 : (∑ r' : N.R, if N.targetIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0) = 0 := by
    have h1 : (∑ r' : N.R, if N.targetIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0)
        - (∑ r' : N.R, if N.sourceIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0) = 0 := by
      calc _ = (∑ r' : N.R, κ.k r' * w (N.sourceIdx r') *
            ((if N.targetIdx r' = y then 1 else 0) - (if N.sourceIdx r' = y then 1 else 0))) :=
          hsplit.symm
        _ = 0 := hy'
    linarith [h1, hS2]
  -- every term of the inflow sum is nonpositive
  have hle : ∀ r' : N.R, (if N.targetIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0) ≤ 0 := by
    intro r'
    by_cases hc : N.targetIdx r' = y
    · rw [ite_eq_left hc]
      exact mul_nonpos_of_nonneg_of_nonpos (κ.positive r').le (hwle (N.sourceIdx r'))
    · have h0 : (if N.targetIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0) = 0 := by
        rw [ite_eq_right hc]
      exact h0.le
  -- so each of them vanishes
  have hneg : (∑ r' : N.R, -(if N.targetIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0)) = 0 := by
    rw [Finset.sum_neg_distrib, hS1]
    simp
  have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset N.R))
    (f := fun r' => -(if N.targetIdx r' = y then κ.k r' * w (N.sourceIdx r') else 0))
    (fun r' _ => neg_nonneg.mpr (hle r'))
  have hterm := (hiff.mp hneg) r (Finset.mem_univ r)
  rw [htarget] at hterm
  rw [ite_eq_left rfl] at hterm
  have hmul : κ.k r * w (N.sourceIdx r) = 0 := by
    linarith
  rcases mul_eq_zero.mp hmul with h1 | h2
  · exact absurd h1 (ne_of_gt (κ.positive r))
  · exact h2

/-- **Uniqueness of a positive vector in the kernel of the kinetic map.**  If two strictly
positive vectors annihilate the kinetic map of a network whose reaction graph is strongly
connected, then they are positive scalar multiples of one another.  This is the maximum
principle for the balance equations of the reaction graph. -/
theorem exists_smul_eq_of_positive_kineticKernel (N : Network S) (κ : N.RateConstants)
    (hsc : N.StronglyConnected) {v v' : N.ComplexIdx → ℝ}
    (hv : ∀ c, 0 < v c) (hv' : ∀ c, 0 < v' c)
    (hker : N.kineticMap κ v = 0) (hker' : N.kineticMap κ v' = 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ c, v c = t * v' c := by
  classical
  by_cases hne : (Finset.univ : Finset N.ComplexIdx).Nonempty
  · obtain ⟨c₀, _, hmax⟩ :=
      Finset.exists_max_image (Finset.univ : Finset N.ComplexIdx) (fun c => v c / v' c) hne
    set t : ℝ := v c₀ / v' c₀ with ht
    have htpos : 0 < t := div_pos (hv c₀) (hv' c₀)
    set w : N.ComplexIdx → ℝ := fun c => v c - t * v' c with hw
    have hwle : ∀ c, w c ≤ 0 := by
      intro c
      have hle : v c / v' c ≤ t := hmax c (Finset.mem_univ c)
      have hle' : v c ≤ t * v' c := (div_le_iff₀ (hv' c)).mp hle
      simp only [hw]
      linarith
    have hwzero : w c₀ = 0 := by
      have hne' : v' c₀ ≠ 0 := ne_of_gt (hv' c₀)
      simp only [hw, ht]
      field_simp
      ring
    have hkerw : N.kineticMap κ w = 0 := by
      have hweq : w = v - t • v' := by
        funext c
        simp [hw, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hweq, map_sub, map_smul, hker, hker']
      simp
    -- the vanishing propagates backwards along the reaction graph
    have hprop : ∀ z : Complex S, N.Reaches z c₀.1 →
        ∀ z' : N.ComplexIdx, z'.val = z → w z' = 0 := by
      intro z hz
      induction hz using Relation.ReflTransGen.head_induction_on with
      | refl =>
        intro z' hz'
        have hz'' : z' = c₀ := by
          apply Subtype.ext
          exact hz'
        rw [hz'']
        exact hwzero
      | @head z zmid e _ ih =>
        intro z' hz'
        rcases e with ⟨r, hsrc, htgt⟩
        have hsrc' : N.sourceIdx r = z' := by
          apply Subtype.ext
          calc (N.sourceIdx r).val = (N.reaction r).source := rfl
            _ = z := hsrc
            _ = z'.val := hz'.symm
        have htgtmem : zmid ∈ N.complexes := by
          rw [← htgt]
          exact N.target_mem_complexes r
        have hmid : w ⟨zmid, htgtmem⟩ = 0 := by
          apply ih ⟨zmid, htgtmem⟩
          rfl
        have hz'' := N.eq_zero_of_le_zero_of_kineticKernel κ hwle hkerw hmid r
          (by
            apply Subtype.ext
            exact htgt)
        rw [hsrc'] at hz''
        exact hz''
    refine ⟨t, htpos, ?_⟩
    intro c
    have hz := hprop c.1 (hsc c c₀) c rfl
    simp only [hw] at hz
    linarith
  · refine ⟨1, zero_lt_one, ?_⟩
    intro c
    have hempty : (Finset.univ : Finset N.ComplexIdx) = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    exact absurd (Finset.mem_univ c) (by rw [hempty]; simp)

/-- **The positive steady state of a unimolecular network is unique up to scaling.**  For a
unimolecular network with a strongly connected reaction graph and positive rate constants
the positive steady states are exactly the positive multiples of the King--Altman steady
state. -/
theorem exists_pos_mul_eq_kingAltmanSteadyState (N : Network S) (κ : N.RateConstants)
    (h : N.Unimolecular) (hwr : N.WeaklyReversible) (h1 : N.HasSingleLinkageClass)
    (hne : Nonempty N.R)
    (hocc : ∀ s : S, singletonComplex s ∈ N.complexes)
    {y : Concentration S} (hy : y.Positive) (hys : N.IsMassActionSteadyState κ y) :
    ∃ c : ℝ, 0 < c ∧ ∀ s : S, y s = c * N.kingAltmanSteadyState κ h s := by
  classical
  have hsc : N.StronglyConnected :=
    N.stronglyConnected_of_weaklyReversible_of_singleLinkageClass hwr h1
  -- the monomial vector of `y` and the tree-constant vector are positive kernel vectors
  have hvpos : ∀ c : N.ComplexIdx, 0 < N.complexMonomialVector y c := by
    intro c
    obtain ⟨j, hj⟩ := N.complex_eq_singleton_of_unimolecular h c
    rw [N.complexMonomialVector_apply, hj]
    exact Complex.massActionMonomial_pos hy (singletonComplex j)
  have hv'pos : ∀ c : N.ComplexIdx, 0 < N.treeConstantVector κ c :=
    fun c => N.treeConstant_pos_of_weaklyReversible κ hwr c
  have hker : N.kineticMap κ (N.complexMonomialVector y) = 0 :=
    N.kineticMap_eq_zero_of_isSteadyState κ h hys
  have hker' : N.kineticMap κ (N.treeConstantVector κ) = 0 :=
    N.treeConstant_kineticKernel κ
  obtain ⟨t, htpos, ht⟩ :=
    N.exists_smul_eq_of_positive_kineticKernel κ hsc hvpos hv'pos hker hker'
  have hTpos : 0 < N.totalTreeWeight κ := by
    show 0 < ∑ c : N.ComplexIdx, N.treeConstant κ c
    exact Finset.sum_pos' (fun c _ => (N.treeConstant_pos_of_weaklyReversible κ hwr c).le)
      ⟨N.sourceIdx (Classical.choice hne), Finset.mem_univ _,
        N.treeConstant_pos_of_weaklyReversible κ hwr _⟩
  refine ⟨t * N.totalTreeWeight κ, mul_pos htpos hTpos, ?_⟩
  intro s
  have hs : singletonComplex s ∈ N.complexes := hocc s
  have hmono : N.complexMonomialVector y ⟨singletonComplex s, hs⟩ = y s := by
    rw [N.complexMonomialVector_apply]
    exact massActionMonomial_of_isSingleton y (isSingleton_singletonComplex s)
  have hmono' : N.treeConstantVector κ ⟨singletonComplex s, hs⟩
      = N.treeConcentration κ h s := by
    show N.treeConstant κ ⟨singletonComplex s, hs⟩ = N.treeConcentration κ h s
    exact (N.treeConcentration_of_occurs κ h hs).symm
  have hkey : y s = t * N.treeConcentration κ h s := by
    rw [← hmono, ← hmono']
    exact ht ⟨singletonComplex s, hs⟩
  rw [hkey]
  show t * N.treeConcentration κ h s
      = t * N.totalTreeWeight κ * (N.treeConcentration κ h s / N.totalTreeWeight κ)
  field_simp


end Network

/-! ## An instance: the reversible pair `X ⇌ Y` -/

namespace Examples.KingAltman

open CRNT
open scoped BigOperators

/-- The two species `X` and `Y`. -/
abbrev Species : Type := Fin 2

/-- The species `X`. -/
abbrev X : Species := 0

/-- The species `Y`. -/
abbrev Y : Species := 1

/-- The two reaction channels of the reversible pair. -/
abbrev Rxn : Type := Fin 2

/-- The reaction map of the reversible pair `X ⇌ Y`. -/
def rxn : Rxn → Reaction Species :=
  ![{ source := Network.singletonComplex X, target := Network.singletonComplex Y },
    { source := Network.singletonComplex Y, target := Network.singletonComplex X }]

/-- The network `X ⇌ Y`. -/
abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The channel `X → Y`. -/
def fwd : N.R := (0 : Rxn)

/-- The channel `Y → X`. -/
def bwd : N.R := (1 : Rxn)

/-- The source complex of a reaction of the example network. -/
def srcOf (r : N.R) : Complex Species := (N.reaction r).source

/-- The target complex of a reaction of the example network. -/
def tgtOf (r : N.R) : Complex Species := (N.reaction r).target

/-- The rate constants of the reversible pair: `k₁` for `X → Y` and `k₂` for `Y → X`. -/
def rates (k₁ k₂ : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) : Network.RateConstants N where
  k := ![k₁, k₂]
  positive := by
    intro r
    have hpos : ∀ r' : Rxn, 0 < (![k₁, k₂] : Rxn → ℝ) r' := by
      intro r'
      fin_cases r'
      · simpa using h₁
      · simpa using h₂
    show 0 < (![k₁, k₂] : Rxn → ℝ) r
    exact hpos r

/-- The source of the forward channel is `X`. -/
theorem source_fwd : srcOf fwd = Network.singletonComplex X := by
  show srcOf (0 : Rxn) = Network.singletonComplex X
  rfl

/-- The target of the forward channel is `Y`. -/
theorem target_fwd : tgtOf fwd = Network.singletonComplex Y := by
  show tgtOf (0 : Rxn) = Network.singletonComplex Y
  rfl

/-- The source of the backward channel is `Y`. -/
theorem source_bwd : srcOf bwd = Network.singletonComplex Y := by
  show srcOf (1 : Rxn) = Network.singletonComplex Y
  rfl

/-- The target of the backward channel is `X`. -/
theorem target_bwd : tgtOf bwd = Network.singletonComplex X := by
  show tgtOf (1 : Rxn) = Network.singletonComplex X
  rfl

/-- **The reversible pair `X ⇌ Y` is unimolecular.** -/
theorem N_unimolecular : N.Unimolecular := by
  intro r
  have h : ∀ r' : Rxn, Network.IsUnimolecular (N.reaction r') := by
    intro r'
    fin_cases r'
    · refine ⟨⟨X, ?_⟩, ⟨Y, ?_⟩⟩
      · show srcOf (0 : Rxn) = Network.singletonComplex X
        rfl
      · show tgtOf (0 : Rxn) = Network.singletonComplex Y
        rfl
    · refine ⟨⟨Y, ?_⟩, ⟨X, ?_⟩⟩
      · show srcOf (1 : Rxn) = Network.singletonComplex Y
        rfl
      · show tgtOf (1 : Rxn) = Network.singletonComplex X
        rfl
  show Network.IsUnimolecular (N.reaction r)
  exact h r

/-- The complex `X` is a complex of the network. -/
theorem cX_mem : Network.singletonComplex X ∈ N.complexes := by
  apply Finset.mem_union_left
  have h : srcOf (0 : Rxn) ∈ Finset.univ.image (fun r : N.R => (N.reaction r).source) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ (0 : Rxn))
  rw [show srcOf (0 : Rxn) = Network.singletonComplex X from rfl] at h
  exact h

/-- The complex `Y` is a complex of the network. -/
theorem cY_mem : Network.singletonComplex Y ∈ N.complexes := by
  apply Finset.mem_union_right
  have h : tgtOf (0 : Rxn) ∈ Finset.univ.image (fun r : N.R => (N.reaction r).target) :=
    Finset.mem_image_of_mem _ (Finset.mem_univ (0 : Rxn))
  rw [show tgtOf (0 : Rxn) = Network.singletonComplex Y from rfl] at h
  exact h

/-- The complex index of `X`. -/
def rootX : N.ComplexIdx := ⟨Network.singletonComplex X, cX_mem⟩

/-- The complex index of `Y`. -/
def rootY : N.ComplexIdx := ⟨Network.singletonComplex Y, cY_mem⟩

/-- The source index of the forward channel is `X`. -/
theorem sourceIdx_fwd : N.sourceIdx fwd = rootX := by
  apply Subtype.ext
  exact source_fwd

/-- The target index of the forward channel is `Y`. -/
theorem targetIdx_fwd : N.targetIdx fwd = rootY := by
  apply Subtype.ext
  exact target_fwd

/-- The source index of the backward channel is `Y`. -/
theorem sourceIdx_bwd : N.sourceIdx bwd = rootY := by
  apply Subtype.ext
  exact source_bwd

/-- The target index of the backward channel is `X`. -/
theorem targetIdx_bwd : N.targetIdx bwd = rootX := by
  apply Subtype.ext
  exact target_bwd

/-- The two roots are different. -/
theorem rootX_ne_rootY : rootX ≠ rootY := by
  intro h
  have hxy : Network.singletonComplex X = Network.singletonComplex Y :=
    congrArg Subtype.val h
  exact absurd hxy (Network.singletonComplex_ne (by decide))

/-- **The complexes of the network are exactly `X` and `Y`.** -/
theorem complexes_eq :
    N.complexes = ({Network.singletonComplex X, Network.singletonComplex Y} :
      Finset (Complex Species)) := by
  decide

/-- Every complex of the network is `X` or `Y`. -/
theorem complexIdx_eq_rootX_or_rootY (c : N.ComplexIdx) : c = rootX ∨ c = rootY := by
  have hc' : c.val ∈ ({Network.singletonComplex X, Network.singletonComplex Y} :
      Finset (Complex Species)) := by
    simpa only [complexes_eq] using c.property
  rcases Finset.mem_insert.mp hc' with h | h
  · left; apply Subtype.ext; exact h
  · right; apply Subtype.ext; exact Finset.mem_singleton.mp h

/-- The two complexes are linked. -/
theorem linked_cX_cY :
    N.Linked (Network.singletonComplex X) (Network.singletonComplex Y) := by
  have h := N.linked_of_reaction (0 : Rxn)
  rw [show (N.reaction (0 : Rxn)).source = Network.singletonComplex X from rfl,
    show (N.reaction (0 : Rxn)).target = Network.singletonComplex Y from rfl] at h
  exact h

/-- The two roots are in the same linkage class. -/
theorem sameLinkage_rootX_rootY : N.SameLinkage rootX rootY := by
  show N.Linked rootX.1 rootY.1
  exact linked_cX_cY

/-- **The only reaction of the network whose source is `Y` is the backward channel.** -/
theorem eq_bwd_of_source : ∀ r : N.R, srcOf r = Network.singletonComplex Y → r = bwd := by
  decide

/-- **The only reaction of the network whose source is `X` is the forward channel.** -/
theorem eq_fwd_of_source : ∀ r : N.R, srcOf r = Network.singletonComplex X → r = fwd := by
  decide

/-- **The reaction `Y → X` is a spanning tree of the reaction graph rooted at `X`.** -/
theorem arborescence_bwd_rootX : N.IsRootedInArborescence rootX {bwd} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc hne
    rcases complexIdx_eq_rootX_or_rootY c with h | h
    · exact absurd h hne
    · subst h
      refine ⟨bwd, ⟨Finset.mem_singleton_self bwd, sourceIdx_bwd⟩, ?_⟩
      intro r hr
      rcases hr with ⟨hr, _⟩
      simp only [Finset.mem_singleton] at hr
      subst hr
      rfl
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst hr
    rw [sourceIdx_bwd]
    exact fun h => rootX_ne_rootY h.symm
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst hr
    rw [sourceIdx_bwd]
    exact sameLinkage_rootX_rootY
  · intro c hc
    rcases complexIdx_eq_rootX_or_rootY c with h | h
    · subst h
      exact Relation.ReflTransGen.refl
    · subst h
      exact Relation.ReflTransGen.single ⟨bwd, Finset.mem_singleton_self bwd,
        sourceIdx_bwd, targetIdx_bwd⟩

/-- **The reaction `X → Y` is a spanning tree of the reaction graph rooted at `Y`.** -/
theorem arborescence_fwd_rootY : N.IsRootedInArborescence rootY {fwd} := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc hne
    rcases complexIdx_eq_rootX_or_rootY c with h | h
    · subst h
      refine ⟨fwd, ⟨Finset.mem_singleton_self fwd, sourceIdx_fwd⟩, ?_⟩
      intro r hr
      rcases hr with ⟨hr, _⟩
      simp only [Finset.mem_singleton] at hr
      subst hr
      rfl
    · exact absurd h hne
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst hr
    rw [sourceIdx_fwd]
    exact fun h => rootX_ne_rootY h
  · intro r hr
    simp only [Finset.mem_singleton] at hr
    subst hr
    rw [sourceIdx_fwd]
    show N.Linked rootY.1 (N.sourceIdx fwd).1
    exact Network.Linked.symm linked_cX_cY
  · intro c hc
    rcases complexIdx_eq_rootX_or_rootY c with h | h
    · subst h
      exact Relation.ReflTransGen.single ⟨fwd, Finset.mem_singleton_self fwd,
        sourceIdx_fwd, targetIdx_fwd⟩
    · subst h
      exact Relation.ReflTransGen.refl

/-- **The unique spanning tree rooted at `X` is the reaction `Y → X`.**  This is the hand
count of the spanning trees of the reaction graph of `X ⇌ Y`. -/
theorem unique_arborescence_rootX (T : Finset N.R) (hT : N.IsRootedInArborescence rootX T) :
    T = {bwd} := by
  -- the tree contains the reaction out of `Y`, and it is the only one
  have hE := hT.1 rootY sameLinkage_rootX_rootY (fun h => rootX_ne_rootY h.symm)
  have hchoose : hE.choose = bwd := by
    have hspec := hE.choose_spec
    have hsrc : srcOf hE.choose = Network.singletonComplex Y := by
      exact congrArg Subtype.val hspec.1.2
    exact eq_bwd_of_source hE.choose hsrc
  -- every reaction of the tree has its source in the linkage class of `rootX`
  have hsrc' : ∀ r ∈ T, N.sourceIdx r = rootX ∨ N.sourceIdx r = rootY := by
    intro r hr
    have hlink : N.SameLinkage rootX (N.sourceIdx r) := hT.2.2.1 r hr
    rcases complexIdx_eq_rootX_or_rootY (N.sourceIdx r) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hbwdT : bwd ∈ T := by
    rw [← hchoose]
    exact hE.choose_spec.1.1
  ext r
  constructor
  · intro hr
    rcases hsrc' r hr with h | h
    · exact absurd h (hT.2.1 r hr)
    · have hsrc : srcOf r = Network.singletonComplex Y := by
        exact congrArg Subtype.val h
      exact Finset.mem_singleton.mpr (eq_bwd_of_source r hsrc)
  · intro h
    have hr' : r = bwd := Finset.mem_singleton.mp h
    rw [hr']
    exact hbwdT

/-- **The unique spanning tree rooted at `Y` is the reaction `X → Y`.** -/
theorem unique_arborescence_rootY (T : Finset N.R) (hT : N.IsRootedInArborescence rootY T) :
    T = {fwd} := by
  -- the tree contains the reaction out of `X`, and it is the only one
  have hE := hT.1 rootX (by
      show N.Linked rootY.1 rootX.1
      exact Network.Linked.symm linked_cX_cY) (fun h => rootX_ne_rootY h)
  have hchoose : hE.choose = fwd := by
    have hspec := hE.choose_spec
    have hsrc : srcOf hE.choose = Network.singletonComplex X := by
      exact congrArg Subtype.val hspec.1.2
    exact eq_fwd_of_source hE.choose hsrc
  -- every reaction of the tree has its source in the linkage class of `rootY`
  have hsrc' : ∀ r ∈ T, N.sourceIdx r = rootX ∨ N.sourceIdx r = rootY := by
    intro r hr
    have hlink : N.SameLinkage rootY (N.sourceIdx r) := hT.2.2.1 r hr
    rcases complexIdx_eq_rootX_or_rootY (N.sourceIdx r) with h | h
    · exact Or.inl h
    · exact Or.inr h
  have hfwdT : fwd ∈ T := by
    rw [← hchoose]
    exact hE.choose_spec.1.1
  ext r
  constructor
  · intro hr
    rcases hsrc' r hr with h | h
    · have hsrc : srcOf r = Network.singletonComplex X := by
        exact congrArg Subtype.val h
      exact Finset.mem_singleton.mpr (eq_fwd_of_source r hsrc)
    · exact absurd h (hT.2.1 r hr)
  · intro h
    have hr' : r = fwd := Finset.mem_singleton.mp h
    rw [hr']
    exact hfwdT

/-- **The tree constant of `X` is the rate of the reaction `Y → X`.**  The spanning trees
of the reaction graph of `X ⇌ Y` rooted at `X` are counted by hand: there is exactly one,
the reaction `Y → X`, of weight `κ₂`. -/
theorem treeConstant_rootX (κ : Network.RateConstants N) :
    N.treeConstant κ rootX = κ.k bwd := by
  rw [Network.treeConstant_eq_of_unique_arborescence N κ rootX {bwd} arborescence_bwd_rootX
    (fun T hT => unique_arborescence_rootX T hT)]
  simp [Network.treeWeight]

/-- **The tree constant of `Y` is the rate of the reaction `X → Y`.** -/
theorem treeConstant_rootY (κ : Network.RateConstants N) :
    N.treeConstant κ rootY = κ.k fwd := by
  rw [Network.treeConstant_eq_of_unique_arborescence N κ rootY {fwd} arborescence_fwd_rootY
    (fun T hT => unique_arborescence_rootY T hT)]
  simp [Network.treeWeight]

/-- **The cofactor of `X` is the rate of the reaction `Y → X`**: by the directed
Matrix--Tree theorem the cofactor is the sum of the weights of the spanning trees rooted
at the root, and there is exactly one of them. -/
theorem kineticCofactor_rootX (κ : Network.RateConstants N) :
    N.kineticCofactor κ rootX = κ.k bwd := by
  rw [N.kineticCofactor_eq_treeConstant κ]
  exact treeConstant_rootX κ

/-- **The cofactor of `Y` is the rate of the reaction `X → Y`.** -/
theorem kineticCofactor_rootY (κ : Network.RateConstants N) :
    N.kineticCofactor κ rootY = κ.k fwd := by
  rw [N.kineticCofactor_eq_treeConstant κ]
  exact treeConstant_rootY κ

/-- **The total tree weight of `X ⇌ Y` is the sum of the two rate constants**: the two
spanning trees of the reaction graph have the weights `κ₁` and `κ₂`. -/
theorem totalTreeWeight_eq (κ : Network.RateConstants N) :
    N.totalTreeWeight κ = κ.k bwd + κ.k fwd := by
  rw [← N.sum_treeConcentration_eq_totalTreeWeight κ N_unimolecular]
  simp only [Fin.sum_univ_two]
  have hX : N.treeConcentration κ N_unimolecular X = κ.k bwd := by
    rw [N.treeConcentration_of_occurs κ N_unimolecular cX_mem]
    have hroot : (⟨Network.singletonComplex X, cX_mem⟩ : N.ComplexIdx) = rootX := by
      apply Subtype.ext
      rfl
    rw [hroot]
    exact treeConstant_rootX κ
  have hY : N.treeConcentration κ N_unimolecular Y = κ.k fwd := by
    rw [N.treeConcentration_of_occurs κ N_unimolecular cY_mem]
    have hroot : (⟨Network.singletonComplex Y, cY_mem⟩ : N.ComplexIdx) = rootY := by
      apply Subtype.ext
      rfl
    rw [hroot]
    exact treeConstant_rootY κ
  rw [hX, hY]

/-- **The King--Altman steady state of `X ⇌ Y` at `X`.** -/
theorem kingAltmanSteadyState_X (κ : Network.RateConstants N) :
    N.kingAltmanSteadyState κ N_unimolecular X = κ.k bwd / (κ.k bwd + κ.k fwd) := by
  show N.treeConcentration κ N_unimolecular X / N.totalTreeWeight κ
      = κ.k bwd / (κ.k bwd + κ.k fwd)
  rw [show N.treeConcentration κ N_unimolecular X = κ.k bwd from by
    rw [N.treeConcentration_of_occurs κ N_unimolecular cX_mem]
    have hroot : (⟨Network.singletonComplex X, cX_mem⟩ : N.ComplexIdx) = rootX := by
      apply Subtype.ext
      rfl
    rw [hroot]
    exact treeConstant_rootX κ]
  rw [totalTreeWeight_eq κ]

/-- **The King--Altman steady state of `X ⇌ Y` at `Y`.** -/
theorem kingAltmanSteadyState_Y (κ : Network.RateConstants N) :
    N.kingAltmanSteadyState κ N_unimolecular Y = κ.k fwd / (κ.k bwd + κ.k fwd) := by
  show N.treeConcentration κ N_unimolecular Y / N.totalTreeWeight κ
      = κ.k fwd / (κ.k bwd + κ.k fwd)
  rw [show N.treeConcentration κ N_unimolecular Y = κ.k fwd from by
    rw [N.treeConcentration_of_occurs κ N_unimolecular cY_mem]
    have hroot : (⟨Network.singletonComplex Y, cY_mem⟩ : N.ComplexIdx) = rootY := by
      apply Subtype.ext
      rfl
    rw [hroot]
    exact treeConstant_rootY κ]
  rw [totalTreeWeight_eq κ]

/-- The mass-action monomial of the singleton complex at `X` is the concentration of `X`. -/
theorem monomial_X (x : Concentration Species) :
    (Network.singletonComplex X).massActionMonomial x = x X :=
  Network.massActionMonomial_of_isSingleton x (Network.isSingleton_singletonComplex X)

/-- The mass-action monomial of the singleton complex at `Y` is the concentration of `Y`. -/
theorem monomial_Y (x : Concentration Species) :
    (Network.singletonComplex Y).massActionMonomial x = x Y :=
  Network.massActionMonomial_of_isSingleton x (Network.isSingleton_singletonComplex Y)

/-- **The field of `X ⇌ Y` at the species `X`** is the transfer `Y → X` minus the transfer
`X → Y`: `ẋ_X = κ₂ x_Y − κ₁ x_X`. -/
theorem field_X (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x X = κ.k bwd * x Y - κ.k fwd * x X := by
  show (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r X) = _
  change (∑ r : Fin 2, N.massActionRate κ r x * N.reactionVector r X) = _
  simp only [Fin.sum_univ_two]
  have h0 : N.massActionRate κ 0 x * N.reactionVector 0 X = -(κ.k 0) * x X := by
    rw [Network.massActionRate_eq, N.complexMonomialVector_apply]
    have hsrc : (N.sourceIdx 0).val = Network.singletonComplex X := by
      show (N.reaction 0).source = Network.singletonComplex X
      rfl
    rw [hsrc, monomial_X, Network.reactionVector_apply]
    have hsrc' : (N.reaction 0).source X = 1 := by
      show (Network.singletonComplex X) X = 1
      simp [Network.singletonComplex]
    have htgt : (N.reaction 0).target X = 0 := by
      show (Network.singletonComplex Y) X = 0
      simp [Network.singletonComplex]
    rw [htgt, hsrc']
    norm_num
  have h1 : N.massActionRate κ 1 x * N.reactionVector 1 X = κ.k 1 * x Y := by
    rw [Network.massActionRate_eq, N.complexMonomialVector_apply]
    have hsrc : (N.sourceIdx 1).val = Network.singletonComplex Y := by
      show (N.reaction 1).source = Network.singletonComplex Y
      rfl
    rw [hsrc, monomial_Y, Network.reactionVector_apply]
    have hsrc' : (N.reaction 1).source X = 0 := by
      show (Network.singletonComplex Y) X = 0
      simp [Network.singletonComplex]
    have htgt : (N.reaction 1).target X = 1 := by
      show (Network.singletonComplex X) X = 1
      simp [Network.singletonComplex]
    rw [htgt, hsrc']
    norm_num
  rw [h0, h1]
  have hbwd : κ.k 1 = κ.k bwd := by rfl
  have hfwd : κ.k 0 = κ.k fwd := by rfl
  rw [hbwd, hfwd]
  ring

/-- **The field of `X ⇌ Y` at the species `Y`** is the transfer `X → Y` minus the transfer
`Y → X`: `ẋ_Y = κ₁ x_X − κ₂ x_Y`. -/
theorem field_Y (κ : Network.RateConstants N) (x : Concentration Species) :
    N.massActionVectorField κ x Y = κ.k fwd * x X - κ.k bwd * x Y := by
  show (∑ r : N.R, N.massActionRate κ r x * N.reactionVector r Y) = _
  change (∑ r : Fin 2, N.massActionRate κ r x * N.reactionVector r Y) = _
  simp only [Fin.sum_univ_two]
  have h0 : N.massActionRate κ 0 x * N.reactionVector 0 Y = κ.k 0 * x X := by
    rw [Network.massActionRate_eq, N.complexMonomialVector_apply]
    have hsrc : (N.sourceIdx 0).val = Network.singletonComplex X := by
      show (N.reaction 0).source = Network.singletonComplex X
      rfl
    rw [hsrc, monomial_X, Network.reactionVector_apply]
    have hsrc' : (N.reaction 0).source Y = 0 := by
      show (Network.singletonComplex X) Y = 0
      simp [Network.singletonComplex]
    have htgt : (N.reaction 0).target Y = 1 := by
      show (Network.singletonComplex Y) Y = 1
      simp [Network.singletonComplex]
    rw [htgt, hsrc']
    norm_num
  have h1 : N.massActionRate κ 1 x * N.reactionVector 1 Y = -(κ.k 1) * x Y := by
    rw [Network.massActionRate_eq, N.complexMonomialVector_apply]
    have hsrc : (N.sourceIdx 1).val = Network.singletonComplex Y := by
      show (N.reaction 1).source = Network.singletonComplex Y
      rfl
    rw [hsrc, monomial_Y, Network.reactionVector_apply]
    have hsrc' : (N.reaction 1).source Y = 1 := by
      show (Network.singletonComplex Y) Y = 1
      simp [Network.singletonComplex]
    have htgt : (N.reaction 1).target Y = 0 := by
      show (Network.singletonComplex X) Y = 0
      simp [Network.singletonComplex]
    rw [htgt, hsrc']
    norm_num
  rw [h0, h1]
  have hbwd : κ.k 1 = κ.k bwd := by rfl
  have hfwd : κ.k 0 = κ.k fwd := by rfl
  rw [hbwd, hfwd]
  ring

/-- **The steady states of `X ⇌ Y` are the points with `κ₁ x_X = κ₂ x_Y`.**  This is the
specialisation of the SingletonSource theorem: the steady-state variety of a unimolecular network is
a linear subspace, here the line through the origin of slope `κ₁/κ₂`. -/
theorem steadyState_iff (κ : Network.RateConstants N) (x : Concentration Species) :
    N.IsMassActionSteadyState κ x ↔ κ.k fwd * x X = κ.k bwd * x Y := by
  constructor
  · intro h
    have hX := h X
    have hY := h Y
    rw [field_X κ x] at hX
    rw [field_Y κ x] at hY
    linarith
  · intro h s
    fin_cases s
    · show N.massActionVectorField κ x X = 0
      rw [field_X κ x]
      linarith
    · show N.massActionVectorField κ x Y = 0
      rw [field_Y κ x]
      linarith

/-- **The King--Altman steady state of `X ⇌ Y` is a steady state, and its ratio is the
ratio of the tree constants.**  This checks the King--Altman formula against the directly
computed steady state: the steady states of `X ⇌ Y` are the points of the line
`κ₁ x_X = κ₂ x_Y`, and the King--Altman formula gives the point of that line with total
concentration one. -/
theorem kingAltman_checked (κ : Network.RateConstants N) (h₁ : 0 < κ.k fwd) (h₂ : 0 < κ.k bwd) :
    N.IsMassActionSteadyState κ (N.kingAltmanSteadyState κ N_unimolecular) ∧
      κ.k fwd * (N.kingAltmanSteadyState κ N_unimolecular) X
        = κ.k bwd * (N.kingAltmanSteadyState κ N_unimolecular) Y ∧
      (∑ s : Species, N.kingAltmanSteadyState κ N_unimolecular s) = 1 := by
  have hT : 0 < κ.k bwd + κ.k fwd := by linarith
  have hsteady : N.IsMassActionSteadyState κ (N.kingAltmanSteadyState κ N_unimolecular) :=
    N.kingAltmanSteadyState_isSteadyState κ N_unimolecular
  have hratio : κ.k fwd * (N.kingAltmanSteadyState κ N_unimolecular) X
      = κ.k bwd * (N.kingAltmanSteadyState κ N_unimolecular) Y := by
    rw [kingAltmanSteadyState_X κ, kingAltmanSteadyState_Y κ]
    have hT0 : κ.k bwd + κ.k fwd ≠ 0 := by linarith [h₁, h₂]
    field_simp [hT0]
  have hsum : (∑ s : Species, N.kingAltmanSteadyState κ N_unimolecular s) = 1 := by
    have hT' : 0 < N.totalTreeWeight κ := by
      rw [totalTreeWeight_eq κ]
      exact hT
    exact N.kingAltmanSteadyState_sum_eq_one κ N_unimolecular hT'
  exact ⟨hsteady, hratio, hsum⟩

/-- **The King--Altman ratio of `X ⇌ Y` is the ratio of the cofactors**, i.e. the ratio of
the tree constants: `κ₂/κ₁`. -/
theorem kingAltman_ratio_checked (κ : Network.RateConstants N) (h₁ : 0 < κ.k fwd)
    (h₂ : 0 < κ.k bwd) :
    N.kingAltmanSteadyState κ N_unimolecular X / N.kingAltmanSteadyState κ N_unimolecular Y
      = N.kineticCofactor κ rootX / N.kineticCofactor κ rootY := by
  rw [kingAltmanSteadyState_X κ, kingAltmanSteadyState_Y κ, kineticCofactor_rootX κ,
    kineticCofactor_rootY κ]
  have hT0 : κ.k bwd + κ.k fwd ≠ 0 := by linarith [h₁, h₂]
  field_simp [hT0]

end Examples.KingAltman

end CRNT
