import CRNT.Kinetics.GeneralizedConditions

/-!
# Representation-independent oriented-matroid map conditions

The generalized mass-action literature states several existence/bijectivity criteria in
terms of *pairs of oriented matroids*.  A matrix implementation can obscure which object
is a row space and which is a kernel, so this file records the combinatorics first, for two
arbitrary realizable subspaces `A` and `B`.

No CRNT-specific identification of `A` and `B` is made here.  This prevents accidentally
reversing a face/closure condition when passing between a matrix and its kernel matrix.
-/

namespace CRNT

variable {ι : Type*} [Fintype ι]

/-- `σ` is a realizable nonzero covector of `A`. -/
def IsRealizableNonzeroCovector (A : Submodule ℝ (ι → ℝ))
    (σ : ι → SignType) : Prop :=
  σ ∈ RealizableSignVector A ∧ σ ≠ 0

/-- Every tope of `A` is covered by a tope of `B`.

For full-support sign vectors, coverage is necessarily equality; retaining the coverage
form makes the statement line up with the standard oriented-matroid partial order. -/
def TopeClosureCondition (A B : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ σ, IsRealizableTope A σ →
    ∃ τ, IsRealizableTope B τ ∧ SignVector.Covers τ σ

/-- Uniqueness condition for a pair of realizable sign systems: zero is their only common
sign vector. -/
def OrientedMatroidUniquenessCondition
    (A B : Submodule ℝ (ι → ℝ)) : Prop :=
  RealizableSignVector A ∩ RealizableSignVector B = {(fun _ => 0)}

/-- Face condition in the direction used by the kernel-matrix formulation: every
nonnegative cocircuit of `B` covers a nonnegative cocircuit of `A`. -/
def CocircuitFaceCondition (A B : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ τ, IsNonnegativeCocircuit B τ →
    ∃ σ, IsNonnegativeCocircuit A σ ∧ SignVector.Covers τ σ

/-- Package of the three representation-independent sign conditions. -/
structure OrientedMatroidMapConditions
    (A B : Submodule ℝ (ι → ℝ)) : Prop where
  closure : TopeClosureCondition A B
  uniqueness : OrientedMatroidUniquenessCondition A B
  face : CocircuitFaceCondition A B

/-- A tope covering another tope is the same sign vector. -/
theorem tope_eq_of_covers {σ τ : ι → SignType}
    (hσ : SignVector.IsTope σ) (h : SignVector.Covers τ σ) : τ = σ := by
  funext i
  exact h i (hσ i)

/-- Hence the tope closure condition is simply inclusion of realizable tope sets. -/
theorem topeClosureCondition_iff
    (A B : Submodule ℝ (ι → ℝ)) :
    TopeClosureCondition A B ↔
      ∀ σ, IsRealizableTope A σ → IsRealizableTope B σ := by
  constructor
  · intro h σ hσ
    rcases h σ hσ with ⟨τ, hτ, hcover⟩
    have hEq : τ = σ := tope_eq_of_covers hσ.2 hcover
    simpa [hEq] using hτ
  · intro h σ hσ
    exact ⟨σ, h σ hσ, SignVector.covers_refl σ⟩

/-- Closure conditions compose. -/
theorem TopeClosureCondition.trans
    {A B C : Submodule ℝ (ι → ℝ)}
    (hAB : TopeClosureCondition A B)
    (hBC : TopeClosureCondition B C) :
    TopeClosureCondition A C := by
  rw [topeClosureCondition_iff] at hAB hBC ⊢
  intro σ hσ
  exact hBC σ (hAB σ hσ)

/-- Closure is reflexive. -/
theorem topeClosureCondition_refl (A : Submodule ℝ (ι → ℝ)) :
    TopeClosureCondition A A := by
  rw [topeClosureCondition_iff]
  exact fun _ h => h

/-- Mutual tope closure means equality of the realizable tope predicates. -/
theorem mutual_topeClosure_iff
    (A B : Submodule ℝ (ι → ℝ)) :
    TopeClosureCondition A B ∧ TopeClosureCondition B A ↔
      ∀ σ, IsRealizableTope A σ ↔ IsRealizableTope B σ := by
  rw [topeClosureCondition_iff, topeClosureCondition_iff]
  constructor
  · rintro ⟨hAB, hBA⟩ σ
    exact ⟨hAB σ, hBA σ⟩
  · intro h
    exact ⟨fun σ => (h σ).mp, fun σ => (h σ).mpr⟩

/-- The uniqueness condition is symmetric. -/
theorem orientedMatroidUniquenessCondition_comm
    (A B : Submodule ℝ (ι → ℝ)) :
    OrientedMatroidUniquenessCondition A B ↔
      OrientedMatroidUniquenessCondition B A := by
  unfold OrientedMatroidUniquenessCondition
  rw [Set.inter_comm]

/-- Existing `SignCompatible` is exactly the representation-independent uniqueness
condition. -/
theorem orientedMatroidUniquenessCondition_iff_signCompatible
    (A B : Submodule ℝ (ι → ℝ)) :
    OrientedMatroidUniquenessCondition A B ↔ SignCompatible A B := by
  rw [OrientedMatroidUniquenessCondition, signCompatible_iff_realizable_inter]

/-- The face condition is reflexive. -/
theorem cocircuitFaceCondition_refl (A : Submodule ℝ (ι → ℝ)) :
    CocircuitFaceCondition A A := by
  intro τ hτ
  exact ⟨τ, hτ, SignVector.covers_refl τ⟩

/-- Face conditions compose by transitivity of covector coverage. -/
theorem CocircuitFaceCondition.trans
    {A B C : Submodule ℝ (ι → ℝ)}
    (hAB : CocircuitFaceCondition A B)
    (hBC : CocircuitFaceCondition B C) :
    CocircuitFaceCondition A C := by
  intro τ hτ
  rcases hBC τ hτ with ⟨σ, hσ, hτσ⟩
  rcases hAB σ hσ with ⟨ρ, hρ, hσρ⟩
  exact ⟨ρ, hρ, SignVector.covers_trans hτσ hσρ⟩

/-- Zero is always a realizable sign vector. -/
theorem zero_mem_realizableSignVector (A : Submodule ℝ (ι → ℝ)) :
    (fun _ => 0) ∈ RealizableSignVector A := by
  refine ⟨0, A.zero_mem, ?_⟩
  funext i
  simp [signVector]

/-- Uniqueness can equivalently be stated pointwise: any common realizable sign vector is
zero. -/
theorem orientedMatroidUniquenessCondition_iff_pointwise
    (A B : Submodule ℝ (ι → ℝ)) :
    OrientedMatroidUniquenessCondition A B ↔
      ∀ σ, σ ∈ RealizableSignVector A → σ ∈ RealizableSignVector B → σ = 0 := by
  constructor
  · intro h σ hA hB
    have hm : σ ∈ RealizableSignVector A ∩ RealizableSignVector B := ⟨hA, hB⟩
    rw [show RealizableSignVector A ∩ RealizableSignVector B = {(fun _ => 0)} from h] at hm
    have : σ = fun _ => 0 := hm
    funext i
    simpa using congrFun this i
  · intro h
    apply Set.Subset.antisymm
    · intro σ hm
      have hz := h σ hm.1 hm.2
      simp only [Set.mem_singleton_iff]
      exact hz
    · intro σ hσ
      simp only [Set.mem_singleton_iff] at hσ
      subst σ
      exact ⟨zero_mem_realizableSignVector A, zero_mem_realizableSignVector B⟩

end CRNT
