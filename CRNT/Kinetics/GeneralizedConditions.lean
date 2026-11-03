import CRNT.Kinetics.Generalized
import CRNT.LinearAlgebra.OrientedMatroid
import Mathlib.Data.Finset.Card
import CRNT.Multistationarity.Toric

/-!
# Sign-vector conditions for generalized mass-action systems

This file packages oriented-matroid conditions used in generalized mass-action CRNT.
For the generic two-subspace Birch problem we must record the equal-rank hypothesis that
is implicit in the square exponential-map formulation, together with the robust sign
closure `sign(S) ⊆ sign(T)` of Müller--Hofbauer--Regensburger.  Separate orthogonal/face
coverage predicates are retained as auxiliary combinatorial data; they are not, by
themselves, a replacement for the global properness hypotheses of the generalized Birch
theorem.
-/

namespace CRNT

variable {ι : Type*} [Fintype ι]

/-- Support of a sign vector. -/
def SignVector.support (σ : ι → SignType) : Finset ι :=
  Finset.univ.filter fun i => σ i ≠ 0

/-- Covector order: `σ ≤ τ` when every nonzero sign of `σ` agrees with `τ`. -/
def SignVector.Covers (τ σ : ι → SignType) : Prop :=
  ∀ i, σ i ≠ 0 → τ i = σ i

@[refl] theorem SignVector.covers_refl (σ : ι → SignType) : SignVector.Covers σ σ :=
  fun _ _ => rfl

@[trans] theorem SignVector.covers_trans {ρ σ τ : ι → SignType}
    (hτσ : SignVector.Covers τ σ) (hσρ : SignVector.Covers σ ρ) :
    SignVector.Covers τ ρ := by
  intro i hρ
  have hσi : σ i = ρ i := hσρ i hρ
  have hσ0 : σ i ≠ 0 := by simpa [hσi] using hρ
  exact (hτσ i hσ0).trans hσi

/-- Coverage can only enlarge support. -/
theorem SignVector.support_subset_of_covers {σ τ : ι → SignType}
    (h : SignVector.Covers τ σ) : σ.support ⊆ τ.support := by
  intro i hi
  simp only [Function.mem_support] at hi ⊢
  intro hτ0
  have := h i hi
  exact hi (by simpa [hτ0] using this.symm)

/-- A tope is a sign vector with no zero coordinate. -/
def SignVector.IsTope (σ : ι → SignType) : Prop :=
  ∀ i, σ i ≠ 0

/-- A realizable tope of a subspace. -/
def IsRealizableTope (S : Submodule ℝ (ι → ℝ)) (σ : ι → SignType) : Prop :=
  σ ∈ RealizableSignVector S ∧ SignVector.IsTope σ

/-- A nonzero realizable covector whose support is inclusion-minimal among nonzero
realizable covectors.  This is the cocircuit notion sufficient for CRNT face tests. -/
def IsRealizableCocircuit (S : Submodule ℝ (ι → ℝ)) (σ : ι → SignType) : Prop :=
  σ ∈ RealizableSignVector S ∧ σ ≠ 0 ∧
    ∀ τ ∈ RealizableSignVector S, τ ≠ 0 → τ.support ⊆ σ.support →
      σ.support ⊆ τ.support

/-- Coordinatewise nonnegative sign vector. -/
def SignVector.Nonnegative (σ : ι → SignType) : Prop :=
  ∀ i, σ i = 0 ∨ σ i = 1

/-- Nonnegative realizable cocircuit. -/
def IsNonnegativeCocircuit (S : Submodule ℝ (ι → ℝ)) (σ : ι → SignType) : Prop :=
  IsRealizableCocircuit S σ ∧ SignVector.Nonnegative σ

/-- **Generalized Birch sign-closure condition.**

In the square exponential-map setting of Müller--Hofbauer--Regensburger the two kernel
subspaces have equal dimension, and the robust closure condition is
`sign(S) ⊆ sign(T)`.  Our generic submodule API does not obtain equal dimension from a
matrix shape, so it is recorded explicitly here.  This condition is sufficient for the
associated exponential map to be a global diffeomorphism for all positive parameters. -/
def GeneralizedClosureCondition (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  Module.finrank ℝ S = Module.finrank ℝ T ∧
    RealizableSignVector S ⊆ RealizableSignVector T

/-- **Uniqueness condition.** No nonzero stoichiometric covector shares a sign with a
kinetic-orthogonal covector. -/
def GeneralizedUniquenessCondition (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  SignCompatible S (orthSum T)

/-- **Face condition.** Every nonnegative cocircuit of the stoichiometric orthogonal
complement is covered by a nonnegative covector of the kinetic orthogonal complement.
This encodes the boundary/face compatibility condition appearing in generalized
mass-action existence and bijectivity theorems. -/
def GeneralizedFaceCondition (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ σ, IsNonnegativeCocircuit (orthSum S) σ →
    ∃ τ ∈ RealizableSignVector (orthSum T), τ ≠ 0 ∧
      SignVector.Nonnegative τ ∧ SignVector.Covers τ σ

/-- Structural package commonly used for generalized CBE existence-and-uniqueness. -/
structure GeneralizedCBEConditions (S T : Submodule ℝ (ι → ℝ)) : Prop where
  closure : GeneralizedClosureCondition S T
  uniqueness : GeneralizedUniquenessCondition S T
  face : GeneralizedFaceCondition S T

/-- The uniqueness condition is exactly the existing Müller--Regensburger sign criterion. -/
theorem generalizedUniquenessCondition_iff (S T : Submodule ℝ (ι → ℝ)) :
    GeneralizedUniquenessCondition S T ↔ SignCompatible S (orthSum T) :=
  Iff.rfl

/-- Equivalent set-theoretic formulation of generalized uniqueness. -/
theorem generalizedUniquenessCondition_iff_sign_inter (S T : Submodule ℝ (ι → ℝ)) :
    GeneralizedUniquenessCondition S T ↔
      RealizableSignVector S ∩ RealizableSignVector (orthSum T) = {(fun _ => 0)} := by
  exact signCompatible_iff_realizable_inter S (orthSum T)

/-- Classical mass action automatically satisfies the generalized uniqueness condition. -/
theorem generalizedUniquenessCondition_self (S : Submodule ℝ (ι → ℝ)) :
    GeneralizedUniquenessCondition S S :=
  signCompatible_self S

/-- Equal-rank projection of the generalized Birch closure condition. -/
theorem GeneralizedClosureCondition.finrank_eq {S T : Submodule ℝ (ι → ℝ)}
    (h : GeneralizedClosureCondition S T) :
    Module.finrank ℝ S = Module.finrank ℝ T := h.1

/-- Sign-vector inclusion projection of the generalized Birch closure condition. -/
theorem GeneralizedClosureCondition.sign_subset {S T : Submodule ℝ (ι → ℝ)}
    (h : GeneralizedClosureCondition S T) :
    RealizableSignVector S ⊆ RealizableSignVector T := h.2

/-- The generalized Birch closure condition entails uniqueness-sign compatibility. -/
theorem GeneralizedClosureCondition.signCompatible {S T : Submodule ℝ (ι → ℝ)}
    (h : GeneralizedClosureCondition S T) : SignCompatible S (orthSum T) := by
  intro u hu v hv huv
  have hsu : signVector u ∈ RealizableSignVector S :=
    mem_realizableSignVector.mpr ⟨u, hu, rfl⟩
  have hsuT : signVector u ∈ RealizableSignVector T := h.sign_subset hsu
  obtain ⟨t, ht, htu⟩ := mem_realizableSignVector.mp hsuT
  have htv : SameSign t v := by
    rw [sameSign_iff_signVector_eq]
    exact htu.trans (sameSign_iff_signVector_eq.mp huv)
  have ht0 : t = 0 := signCompatible_self T t ht v hv htv
  have hsignu0 : signVector u = (fun _ => 0) := by
    rw [← htu, ht0]
    funext i
    simp [signVector]
  exact (signVector_eq_zero_iff u).mp hsignu0

/-- A bundled condition exposes the uniqueness theorem immediately. -/
theorem GeneralizedCBEConditions.toric_subsingleton
    {S T : Submodule ℝ (ι → ℝ)} (h : GeneralizedCBEConditions S T)
    {xstar c x y : ι → ℝ}
    (hx : x ∈ ToricSteadyStates S T xstar c)
    (hy : y ∈ ToricSteadyStates S T xstar c) : x = y :=
  toric_subsingleton_of_signCompatible h.uniqueness hx hy

end CRNT
