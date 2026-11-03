import Scaffold.CRNTExpansion.AdvancedDeficiencyFullClasses
import Scaffold.CRNTExpansion.AdvancedDeficiencyCoplanarity

/-!
# Faithful class signs for the linear-triplet Advanced Deficiency Algorithm

This file formalizes the sign layer of Steps 4--8 of the published ADA using the basis-free kernel
rows.  Signs are attached to full reaction classes, but represented as a reaction-indexed function
that is constant on `FullKernelCoordinateColinear` classes.

The `triplet_rule` below targets the regime in which the Triplet Linearity Condition holds.  It does
not claim to cover the nonlinear higher-cardinality coplanar-set cases.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The three signs assigned to ADA colinearity classes. -/
inductive ADAClassSign where
  | negative
  | zero
  | positive
  deriving DecidableEq

namespace ADAClassSign

/-- A real coefficient agrees with a class sign in the strict sense used by the ADA. -/
def Agrees (σ : ADAClassSign) (c : ℝ) : Prop :=
  match σ with
  | negative => c < 0
  | zero => c = 0
  | positive => 0 < c

@[simp] theorem agrees_positive {c : ℝ} : ADAClassSign.positive.Agrees c ↔ 0 < c := Iff.rfl
@[simp] theorem agrees_negative {c : ℝ} : ADAClassSign.negative.Agrees c ↔ c < 0 := Iff.rfl
@[simp] theorem agrees_zero {c : ℝ} : ADAClassSign.zero.Agrees c ↔ c = 0 := Iff.rfl

/-- Nonzero class signs. -/
def Nonzero (σ : ADAClassSign) : Prop := σ ≠ ADAClassSign.zero

end ADAClassSign

/-- A basis-free linear relation among three full-reaction ADA rows. -/
def FullKernelTripleRelation (N : Network S) (O : N.ADAOrientation)
    (i j k : N.R) (ci cj ck : ℝ) : Prop :=
  N.KernelRowRelation O.selected (fun r =>
    (if r = O.selectedRepresentative i then ci else 0) +
      (if r = O.selectedRepresentative j then cj else 0) +
      (if r = O.selectedRepresentative k then ck else 0))

/-- Three reactions represent three distinct nonzero ADA classes. -/
def DistinctNonzeroKernelClasses (N : Network S) (O : N.ADAOrientation)
    (i j k : N.R) : Prop :=
  ¬ N.FullKernelCoordinateZero O i ∧
  ¬ N.FullKernelCoordinateZero O j ∧
  ¬ N.FullKernelCoordinateZero O k ∧
  ¬ N.FullKernelCoordinateColinear O i j ∧
  ¬ N.FullKernelCoordinateColinear O i k ∧
  ¬ N.FullKernelCoordinateColinear O j k

/-- Triplet coplanarity in basis-free form: three distinct nonzero classes admit a relation with all
three coefficients nonzero.  Under the Triplet Linearity Condition these are precisely the
three-class coplanar sets relevant to Steps 8 and 13. -/
def FullKernelCoplanarTriple (N : Network S) (O : N.ADAOrientation)
    (i j k : N.R) : Prop :=
  N.DistinctNonzeroKernelClasses O i j k ∧
    ∃ ci cj ck : ℝ, ci ≠ 0 ∧ cj ≠ 0 ∧ ck ≠ 0 ∧
      N.FullKernelTripleRelation O i j k ci cj ck

/-- Step-8 sign compatibility for one coplanar triplet.

* two zero signs force the third sign to be zero;
* for three nonzero signs, no zero relation may use coefficients agreeing with all three signs;
* with exactly one zero sign, no signed combination of the other two rows may be a multiple of the
  zero-signed row.
-/
def ADATripletSignCompatible
    (N : Network S) (O : N.ADAOrientation) (sign : N.R → ADAClassSign)
    (i j k : N.R) : Prop :=
  ((sign i = ADAClassSign.zero ∧ sign j = ADAClassSign.zero) →
      sign k = ADAClassSign.zero) ∧
  ((sign i = ADAClassSign.zero ∧ sign k = ADAClassSign.zero) →
      sign j = ADAClassSign.zero) ∧
  ((sign j = ADAClassSign.zero ∧ sign k = ADAClassSign.zero) →
      sign i = ADAClassSign.zero) ∧
  ((sign i).Nonzero ∧ (sign j).Nonzero ∧ (sign k).Nonzero →
    ¬ ∃ ci cj ck : ℝ,
      (sign i).Agrees ci ∧ (sign j).Agrees cj ∧ (sign k).Agrees ck ∧
        N.FullKernelTripleRelation O i j k ci cj ck) ∧
  (sign i = ADAClassSign.zero ∧ (sign j).Nonzero ∧ (sign k).Nonzero →
    ¬ ∃ cj ck : ℝ, (sign j).Agrees cj ∧ (sign k).Agrees ck ∧
      ∃ ci : ℝ, N.FullKernelTripleRelation O i j k ci cj ck) ∧
  (sign j = ADAClassSign.zero ∧ (sign i).Nonzero ∧ (sign k).Nonzero →
    ¬ ∃ ci ck : ℝ, (sign i).Agrees ci ∧ (sign k).Agrees ck ∧
      ∃ cj : ℝ, N.FullKernelTripleRelation O i j k ci cj ck) ∧
  (sign k = ADAClassSign.zero ∧ (sign i).Nonzero ∧ (sign j).Nonzero →
    ¬ ∃ ci cj : ℝ, (sign i).Agrees ci ∧ (sign j).Agrees cj ∧
      ∃ ck : ℝ, N.FullKernelTripleRelation O i j k ci cj ck)

/-- Sign assignment for the linear-triplet ADA regime.  The first three fields are the unconditional
Step-8 class rules; `triplet_rule` records the coplanar constraints when every coplanar set is a
triplet. -/
structure ADATripletClassSigning (N : Network S) (O : N.ADAOrientation) where
  sign : N.R → ADAClassSign
  class_constant : ∀ r q : N.R, N.FullKernelCoordinateColinear O r q → sign r = sign q
  zeroClass_zero : ∀ r : N.R, N.FullKernelCoordinateZero O r → sign r = ADAClassSign.zero
  irreversible_positive : ∀ r : N.R, N.IrreversibleChannel r →
    sign r = ADAClassSign.positive
  triplet_rule : ∀ i j k : N.R, N.FullKernelCoplanarTriple O i j k →
    N.ADATripletSignCompatible O sign i j k

namespace ADATripletClassSigning

variable {N : Network S} {O : N.ADAOrientation}

/-- The assigned sign depends only on the full ADA colinearity class. -/
theorem sign_eq_of_colinear (σ : N.ADATripletClassSigning O) {r q : N.R}
    (h : N.FullKernelCoordinateColinear O r q) : σ.sign r = σ.sign q :=
  σ.class_constant r q h

/-- Every member of an irreversible colinearity class is positive once one irreversible member is
exhibited. -/
theorem sign_positive_of_colinear_irreversible
    (σ : N.ADATripletClassSigning O) {r q : N.R}
    (hr : N.IrreversibleChannel r) (hrq : N.FullKernelCoordinateColinear O r q) :
    σ.sign q = ADAClassSign.positive := by
  rw [← σ.sign_eq_of_colinear hrq]
  exact σ.irreversible_positive r hr

end ADATripletClassSigning

end Network
end CRNT
