import Scaffold.CRNTExpansion.AdvancedDeficiencyShelving
import CRNT.Multistationarity.Capacity

/-!
# Linear-triplet ADA pre-signatures (Steps 10--14)

This module assembles the basis-free orientation, full kernel-row classes, Step-8 signs, Step-9
shelves, and the linear inequalities/equalities of Steps 10--13 into a typed pre-signature.

The object is intentionally called a **pre-signature**.  In the published ADA, a pre-signature is a
full signature only when the linearity hypotheses (including the Independence and Triplet Linearity
Conditions, or a justified replacement) guarantee that no additional nonlinear equations are
missing.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Step-10 comparison of the reactant pairing `y · μ` with the class value `M_i`. -/
def ADAShelfMConstraint (shelf : Shelf) (M sourcePairing : ℝ) : Prop :=
  match shelf with
  | Shelf.upper => M < sourcePairing
  | Shelf.middle => sourcePairing = M
  | Shelf.lower => sourcePairing < M

/-- Step-11 oriented source/target comparison for a nonzero class sign. -/
def ADAOrientedSlopeConstraint
    (sign : ADAClassSign) (shelf : Shelf) (sourcePairing targetPairing : ℝ) : Prop :=
  match sign, shelf with
  | ADAClassSign.positive, Shelf.upper => sourcePairing < targetPairing
  | ADAClassSign.positive, Shelf.lower => targetPairing < sourcePairing
  | ADAClassSign.negative, Shelf.upper => targetPairing < sourcePairing
  | ADAClassSign.negative, Shelf.lower => sourcePairing < targetPairing
  | _, _ => True

/-- The Step-13 linear relation `c_k w_k = c_i w_i + c_j w_j`. -/
def FullKernelSplitRelation (N : Network S) (O : N.ADAOrientation)
    (i j k : N.R) (ci cj ck : ℝ) : Prop :=
  N.FullKernelTripleRelation O i j k ci cj (-ck)

/-- The three allowed Step-13 order patterns for `M_i, M_k, M_j`. -/
def ADAMTripletOrder (N : Network S) (M : N.R → ℝ) (i j k : N.R) : Prop :=
  (M i > M k ∧ M k > M j) ∨
    (M i = M k ∧ M k = M j) ∨
    (M i < M k ∧ M k < M j)

/-- Step-13 constraints for one coplanar triplet in the linear-triplet regime. -/
def ADAStep13Compatible (N : Network S) (O : N.ADAOrientation)
    (σ : N.ADATripletClassSigning O) (M : N.R → ℝ) (i j k : N.R) : Prop :=
  ((σ.sign i = ADAClassSign.zero ∧ (σ.sign j).Nonzero ∧ (σ.sign k).Nonzero) →
      M j = M k) ∧
  ((σ.sign j = ADAClassSign.zero ∧ (σ.sign i).Nonzero ∧ (σ.sign k).Nonzero) →
      M i = M k) ∧
  ((σ.sign k = ADAClassSign.zero ∧ (σ.sign i).Nonzero ∧ (σ.sign j).Nonzero) →
      M i = M j) ∧
  ((σ.sign i).Nonzero ∧ (σ.sign j).Nonzero ∧ (σ.sign k).Nonzero →
    ∀ ci cj ck : ℝ,
      (σ.sign i).Agrees ci → (σ.sign j).Agrees cj → (σ.sign k).Agrees ck →
      N.FullKernelSplitRelation O i j k ci cj ck →
      N.ADAMTripletOrder M i j k)

/-- A complete solution of the **linear** ADA inequality/equality system in the triplet regime.

No correctness theorem is asserted here.  The missing mathematical bridge is exactly the published
statement that, under the appropriate linearity hypotheses, such a pre-signature is a genuine
signature and hence realizes multistationarity capacity. -/
structure ADALinearPreSignature (N : Network S) where
  orientation : N.ADAOrientation
  signing : N.ADATripletClassSigning orientation
  shelving : N.ADAShelving orientation signing
  M : N.R → ℝ
  /-- `M_i` is constant on kernel-row colinearity classes. -/
  M_class_constant : ∀ r q : N.R,
    N.FullKernelCoordinateColinear orientation r q → M r = M q
  μ : S → ℝ
  μ_ne_zero : μ ≠ 0
  signCompatible : N.SignCompatibleWithStoich μ
  /-- Step 10: shelves compare source pairings with the class value. -/
  step10 : ∀ r : N.R, (signing.sign r).Nonzero →
    ADAShelfMConstraint (shelving.shelf r) (M r)
      (complexPairing (N.reaction r).source μ)
  /-- Step 11: upper/lower shelves add an oriented source-target inequality for reactions in `O`. -/
  step11 : ∀ r : N.R, (hr : r ∈ orientation.selected) →
    ADAOrientedSlopeConstraint (signing.sign r) (shelving.shelf r)
      (complexPairing (N.reaction r).source μ)
      (complexPairing (N.reaction r).target μ)
  /-- Step 12: zero-signed classes impose source/target pairing equality. -/
  step12 : ∀ r : N.R, signing.sign r = ADAClassSign.zero →
    complexPairing (N.reaction r).source μ = complexPairing (N.reaction r).target μ
  /-- Step 13 in the Triplet Linearity regime. -/
  step13 : ∀ i j k : N.R, N.FullKernelCoplanarTriple orientation i j k →
    N.ADAStep13Compatible orientation signing M i j k

/-- Existence of a linear-triplet ADA pre-signature. -/
def ADAHasLinearPreSignature (N : Network S) : Prop :=
  Nonempty N.ADALinearPreSignature

end Network
end CRNT
