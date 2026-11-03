import CRNT.Oscillation.VassenaContinuation
import CRNT.Oscillation.ChildSelectionSearch

/-!
# D-Hopf witnesses and oscillatory-core matrix routes

The 2025--2026 structural results are most naturally organized around positive diagonal scaling.
For a square matrix `A`, the relevant finite certificate is not merely "A is unstable": one needs
an invertible principal block whose inertia changes under two positive right-diagonal scalings.

For the formal CRN pipeline we use a slightly stronger, directly checkable witness:

* the selected block is nonsingular;
* one positive diagonal scaling is Hurwitz;
* another positive diagonal scaling has a strict right-half-plane eigenvalue.

This is enough for the analytic continuation/Fiedler route already formalized in the mass-action
layer, and avoids introducing an eigenvalue-counting API solely to state inertia.
-/

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Strong finite certificate for a diagonal Hopf route.  It records an invertible matrix and two
positive right-diagonal scalings with different strict stability behavior. -/
structure StrongDHopfWitness (M : Matrix n n ℝ) : Type u where
  nonsingular : M.det ≠ 0
  stableDiagonal : n → ℝ
  stablePositive : ∀ i, 0 < stableDiagonal i
  unstableDiagonal : n → ℝ
  unstablePositive : ∀ i, 0 < unstableDiagonal i
  stable : IsHurwitzReal (M * Matrix.diagonal stableDiagonal)
  unstable : (M * Matrix.diagonal unstableDiagonal).HasUnstableEigenvalue

namespace StrongDHopfWitness

/-- Forgetting nonsingularity gives the diagonal stability-transition object consumed by the
Vassena continuation. -/
def toStabilityTransition {M : Matrix n n ℝ} (h : StrongDHopfWitness M) :
    PositiveDiagonalStabilityTransition M where
  stableDiagonal := h.stableDiagonal
  stablePositive := h.stablePositive
  unstableDiagonal := h.unstableDiagonal
  unstablePositive := h.unstablePositive
  stable := h.stable
  unstable := h.unstable

/-- The determinant remains nonzero under every positive diagonal scaling. -/
theorem scaled_det_ne_zero {M : Matrix n n ℝ} (h : StrongDHopfWitness M)
    (d : n → ℝ) (hd : ∀ i, 0 < d i) :
    (M * Matrix.diagonal d).det ≠ 0 := by
  rw [Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero h.nonsingular
    (Finset.prod_ne_zero_iff.mpr (fun i _ => ne_of_gt (hd i)))

end StrongDHopfWitness

/-- A matrix contains a strong D-Hopf principal block.  This is the principal-submatrix form used
by oscillatory-core recipes when the ambient symbolic Jacobian has conservation-law zero modes. -/
def ContainsStrongDHopfBlock (M : Matrix n n ℝ) : Prop :=
  ∃ I : Finset n, Nonempty (StrongDHopfWitness (M.principalSubmatrix I))

/-- Negating a principal submatrix commutes with selecting the block. -/
theorem neg_principalSubmatrix (M : Matrix n n ℝ) (I : Finset n) :
    (-M).principalSubmatrix I = -(M.principalSubmatrix I) := by
  ext i j
  rfl

/-- Principal minors of `-M` have the expected `(-1)^k` determinant sign. -/
theorem principalDet_neg (M : Matrix n n ℝ) (I : Finset n) :
    principalDet (-M) I =
      (-1 : ℝ) ^ I.card * principalDet M I := by
  unfold principalDet
  have hneg :
      (-M).submatrix (fun i : I => (i : n)) (fun i : I => (i : n)) =
        -(M.submatrix (fun i : I => (i : n)) (fun i : I => (i : n))) := by
    ext i j
    rfl
  rw [hneg, Matrix.det_neg]
  simp only [Fintype.card_coe]

/-- Opposite determinant sign on one principal block is enough to violate `P^-_0`. -/
theorem not_isPMinusZeroMatrix_of_principal_sign_violation
    {M : Matrix n n ℝ} {I : Finset n}
    (hneg : (-1 : ℝ) ^ I.card * principalDet M I < 0) :
    ¬ M.IsPMinusZeroMatrix := by
  intro hP0
  have hnonneg := hP0 I
  rw [principalDet_neg] at hnonneg
  linarith

/-- An unstable-positive-feedback principal block forces failure of `P^-_0` in the ambient matrix.
This is the finite sign step behind the class-I recipe. -/
theorem not_isPMinusZeroMatrix_of_containsUnstablePositiveFeedback
    {M : Matrix n n ℝ} (h : M.ContainsUnstablePositiveFeedback) :
    ¬ M.IsPMinusZeroMatrix := by
  obtain ⟨I, _, hI⟩ := h
  apply not_isPMinusZeroMatrix_of_principal_sign_violation (M := M) (I := I)
  simpa [HasPositiveFeedbackSign, principalDet, principalSubmatrix, Fintype.card_coe] using hI.2

/-- Hence every exact class-I oscillatory core satisfies Vassena Criterion I. -/
theorem IsOscillatoryCoreClassI.criterionI {M : Matrix n n ℝ}
    (h : M.IsOscillatoryCoreClassI) : CriterionI M where
  stable := h.stable
  notPMinusZero :=
    not_isPMinusZeroMatrix_of_containsUnstablePositiveFeedback
      h.containsUnstablePositiveFeedback

/-- Fisher--Fuller branch of an exact class-II core satisfies Vassena Criterion II directly. -/
theorem IsOscillatoryCoreClassII.criterionII_of_fisherFuller
    {M : Matrix n n ℝ} (h : M.IsOscillatoryCoreClassII)
    (hFF : M.IsFisherFullerPMinusMatrix) : CriterionII M where
  unstable := h.unstable
  fisherFuller := hFF

/-- Class I produces a strong D-Hopf witness once the two purely finite matrix facts are supplied:
not-`P^-_0` gives an unstable scaling, and Hurwitz stability gives nonsingularity.  The latter is
kept explicit here so the D-Hopf layer does not duplicate spectral determinant infrastructure. -/
noncomputable def IsOscillatoryCoreClassI.strongDHopf
    (hP0 : NotPMinusZeroImpliesUnstableScalingTarget.{u})
    {M : Matrix n n ℝ} (h : M.IsOscillatoryCoreClassI)
    (hdet : M.det ≠ 0) : StrongDHopfWitness M := by
  let cI : CriterionI M := h.criterionI
  let T := cI.stabilityTransition hP0
  exact
    { nonsingular := hdet
      stableDiagonal := T.stableDiagonal
      stablePositive := T.stablePositive
      unstableDiagonal := T.unstableDiagonal
      unstablePositive := T.unstablePositive
      stable := T.stable
      unstable := T.unstable }

/-- Fisher--Fuller class-II cores likewise give a strong D-Hopf witness after diagonal
stabilization, with nonsingularity recorded explicitly. -/
noncomputable def IsOscillatoryCoreClassII.strongDHopf_of_fisherFuller
    (hFFscale : FisherFullerStabilizingScalingTarget.{u})
    {M : Matrix n n ℝ} (h : M.IsOscillatoryCoreClassII)
    (hFF : M.IsFisherFullerPMinusMatrix) (hdet : M.det ≠ 0) :
    StrongDHopfWitness M := by
  let cII : CriterionII M := h.criterionII_of_fisherFuller hFF
  let T := cII.stabilityTransition hFFscale
  exact
    { nonsingular := hdet
      stableDiagonal := T.stableDiagonal
      stablePositive := T.stablePositive
      unstableDiagonal := T.unstableDiagonal
      unstablePositive := T.unstablePositive
      stable := T.stable
      unstable := T.unstable }

/-- Exact remaining finite-matrix statement for the alternative class-II recipe: an unstable
negative-feedback core with a stable codimension-one principal block contains an invertible
principal block with a diagonal stability transition.  This is the only class-II branch not already
reduced to Fisher--Fuller diagonal stabilization above. -/
def StableCodimOneClassIIImpliesStrongDHopfBlockTarget : Prop :=
  ∀ {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℝ),
    M.IsUnstableNegativeFeedback → M.HasStableCodimOnePrincipalSubmatrix →
      M.ContainsStrongDHopfBlock

end Matrix

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A child selection carries a strong D-Hopf matrix certificate. -/
def ChildSelection.HasStrongDHopfWitness {N : Network S} (C : N.ChildSelection) : Prop :=
  Nonempty (Matrix.StrongDHopfWitness C.matrix)

/-- Search-friendly indexed version. -/
def IndexedChildSelection.HasStrongDHopfWitness
    {N : Network S} {I : Type} [DecidableEq I] [Fintype I]
    (C : N.IndexedChildSelection I) : Prop :=
  Nonempty (Matrix.StrongDHopfWitness C.matrix)

/-- A class-I child selection becomes a D-Hopf witness through the exact matrix theorem above. -/
theorem ChildSelection.strongDHopf_of_classI
    {N : Network S} {C : N.ChildSelection}
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hC : C.IsOscillatoryCoreClassI) (hdet : C.matrix.det ≠ 0) :
    C.HasStrongDHopfWitness := by
  change Matrix.IsOscillatoryCoreClassI C.matrix at hC
  exact ⟨Matrix.IsOscillatoryCoreClassI.strongDHopf hP0 hC hdet⟩

/-- Fisher--Fuller class-II child selections become D-Hopf witnesses analogously. -/
theorem ChildSelection.strongDHopf_of_classII_fisherFuller
    {N : Network S} {C : N.ChildSelection}
    (hFFscale : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hC : C.IsOscillatoryCoreClassII)
    (hFF : C.matrix.IsFisherFullerPMinusMatrix) (hdet : C.matrix.det ≠ 0) :
    C.HasStrongDHopfWitness := by
  change Matrix.IsOscillatoryCoreClassII C.matrix at hC
  exact ⟨Matrix.IsOscillatoryCoreClassII.strongDHopf_of_fisherFuller
    hFFscale hC hFF hdet⟩

end Network
end CRNT

namespace Matrix

universe u

variable {n : Type u} [Fintype n] [DecidableEq n]

/-- Class-I oscillatory cores need no separate determinant hypothesis: Hurwitz stability supplies it. -/
noncomputable def IsOscillatoryCoreClassI.strongDHopf_closed
    (hP0 : NotPMinusZeroImpliesUnstableScalingTarget.{u})
    {M : Matrix n n ℝ} (h : M.IsOscillatoryCoreClassI) :
    StrongDHopfWitness M :=
  h.strongDHopf hP0 h.stable.det_ne_zero

/-- Class-II negative feedback also carries its nonsingularity proof in its determinant sign. -/
noncomputable def IsOscillatoryCoreClassII.strongDHopf_of_fisherFuller_closed
    (hFFscale : FisherFullerStabilizingScalingTarget.{u})
    {M : Matrix n n ℝ} (h : M.IsOscillatoryCoreClassII)
    (hFF : M.IsFisherFullerPMinusMatrix) :
    StrongDHopfWitness M :=
  h.strongDHopf_of_fisherFuller hFFscale hFF h.unstableNegativeFeedback.2.det_ne_zero

end Matrix

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Closed class-I child-selection conversion with no manually supplied determinant fact. -/
theorem ChildSelection.strongDHopf_of_classI_closed
    {N : Network S} {C : N.ChildSelection}
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hC : C.IsOscillatoryCoreClassI) : C.HasStrongDHopfWitness := by
  change Matrix.IsOscillatoryCoreClassI C.matrix at hC
  exact ⟨Matrix.IsOscillatoryCoreClassI.strongDHopf_closed hP0 hC⟩

/-- Closed Fisher--Fuller class-II conversion. -/
theorem ChildSelection.strongDHopf_of_classII_fisherFuller_closed
    {N : Network S} {C : N.ChildSelection}
    (hFFscale : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hC : C.IsOscillatoryCoreClassII)
    (hFF : C.matrix.IsFisherFullerPMinusMatrix) : C.HasStrongDHopfWitness := by
  change Matrix.IsOscillatoryCoreClassII C.matrix at hC
  exact ⟨Matrix.IsOscillatoryCoreClassII.strongDHopf_of_fisherFuller_closed
    hFFscale hC hFF⟩

end CRNT.Network
