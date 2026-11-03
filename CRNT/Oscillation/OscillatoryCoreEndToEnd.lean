import CRNT.Oscillation.ParameterRichDHopfContinuation
import CRNT.Oscillation.DHopf

/-!
# End-to-end indexed oscillatory-core pipeline

Finite child-selection search should not have to know which later theorem will realize the selected
core.  The useful boundary is a **resolved** indexed core: an indexed child selection together with
an actual `StrongDHopfWitness` for its child-selection matrix.

Class-I cores resolve through Vassena Criterion I.  Fisher--Fuller class-II cores resolve through
Criterion II.  The alternative stable-codimension-one class-II branch can be added by proving the
finite matrix resolver already isolated in `DHopf`.

Once resolved, the rest of the parameter-rich pipeline is completely uniform:

`resolved core -> epsilon admissible reactivity -> lifted D-Hopf endpoints -> smooth kinetic path
 -> parameter-rich D-Hopf theorem -> periodic orbit`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Search result after the finite matrix side has been completely resolved to a strong D-Hopf
certificate. -/
structure ResolvedIndexedOscillatoryCoreCertificate (N : Network S) : Type 1 where
  I : Type
  decI : DecidableEq I
  finI : Fintype I
  selection : @IndexedChildSelection S _ _ N I decI finI
  dhopf : Nonempty (Matrix.StrongDHopfWitness selection.matrix)

attribute [instance] ResolvedIndexedOscillatoryCoreCertificate.decI
attribute [instance] ResolvedIndexedOscillatoryCoreCertificate.finI

namespace ResolvedIndexedOscillatoryCoreCertificate

variable {N : Network S}

/-- A resolved finite core feeds the already-closed CRN/reactivity path directly. -/
theorem parameterRichOscillatoryCapacity
    (hopen : ChildSelectionDHopfPerturbationTarget)
    (hDHopf : ParameterRichDHopfContinuationTarget)
    (F : N.SteadyStateParameterRichFamily)
    (hpaths : N.SupportsSmoothReactivityPaths F)
    (hnd : N.IsSymbolicallyNondegenerate)
    (C : N.ResolvedIndexedOscillatoryCoreCertificate)
    (x : Concentration S) (hx : x.Positive) :
    N.ParameterRichOscillatoryCapacity F := by
  exact parameterRichOscillatoryCapacity_of_indexed_strongDHopfCore
    hopen hDHopf N F hpaths hnd C.selection C.dhopf x hx

end ResolvedIndexedOscillatoryCoreCertificate

/-- Class-I indexed selections resolve without any user-supplied determinant fact. -/
noncomputable def resolvedIndexedCoreOfClassI
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    {I : Type} [DecidableEq I] [Fintype I]
    {N : Network S} (C : N.IndexedChildSelection I)
    (hC : C.IsOscillatoryCoreClassI) :
    N.ResolvedIndexedOscillatoryCoreCertificate where
  I := I
  decI := inferInstance
  finI := inferInstance
  selection := C
  dhopf := ⟨Matrix.IsOscillatoryCoreClassI.strongDHopf_closed hP0 hC⟩

/-- Fisher--Fuller class-II indexed selections resolve analogously. -/
noncomputable def resolvedIndexedCoreOfClassIIFF
    (hFFscale : Matrix.FisherFullerStabilizingScalingTarget.{0})
    {I : Type} [DecidableEq I] [Fintype I]
    {N : Network S} (C : N.IndexedChildSelection I)
    (hC : C.IsOscillatoryCoreClassII)
    (hFF : C.matrix.IsFisherFullerPMinusMatrix) :
    N.ResolvedIndexedOscillatoryCoreCertificate where
  I := I
  decI := inferInstance
  finI := inferInstance
  selection := C
  dhopf := ⟨Matrix.IsOscillatoryCoreClassII.strongDHopf_of_fisherFuller_closed
    hFFscale hC hFF⟩

/-- End-to-end class-I child-selection recipe. -/
theorem parameterRichOscillatoryCapacity_of_indexed_classI
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hopen : ChildSelectionDHopfPerturbationTarget)
    (hDHopf : ParameterRichDHopfContinuationTarget)
    {I : Type} [DecidableEq I] [Fintype I]
    (N : Network S) (F : N.SteadyStateParameterRichFamily)
    (hpaths : N.SupportsSmoothReactivityPaths F)
    (hnd : N.IsSymbolicallyNondegenerate)
    (C : N.IndexedChildSelection I) (hC : C.IsOscillatoryCoreClassI)
    (x : Concentration S) (hx : x.Positive) :
    N.ParameterRichOscillatoryCapacity F := by
  let R := resolvedIndexedCoreOfClassI hP0 C hC
  exact R.parameterRichOscillatoryCapacity hopen hDHopf F hpaths hnd x hx

/-- End-to-end Fisher--Fuller class-II child-selection recipe. -/
theorem parameterRichOscillatoryCapacity_of_indexed_classIIFF
    (hFFscale : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hopen : ChildSelectionDHopfPerturbationTarget)
    (hDHopf : ParameterRichDHopfContinuationTarget)
    {I : Type} [DecidableEq I] [Fintype I]
    (N : Network S) (F : N.SteadyStateParameterRichFamily)
    (hpaths : N.SupportsSmoothReactivityPaths F)
    (hnd : N.IsSymbolicallyNondegenerate)
    (C : N.IndexedChildSelection I) (hC : C.IsOscillatoryCoreClassII)
    (hFF : C.matrix.IsFisherFullerPMinusMatrix)
    (x : Concentration S) (hx : x.Positive) :
    N.ParameterRichOscillatoryCapacity F := by
  let R := resolvedIndexedCoreOfClassIIFF hFFscale C hC hFF
  exact R.parameterRichOscillatoryCapacity hopen hDHopf F hpaths hnd x hx

/-- A strong D-Hopf principal block of an indexed child selection is itself a resolved smaller
indexed child selection.  This is the bridge needed by the stable-codimension-one class-II branch. -/
noncomputable def resolvedIndexedCoreOfContainedBlock
    {I : Type} [DecidableEq I] [Fintype I]
    {N : Network S} (C : N.IndexedChildSelection I)
    (hblock : C.matrix.ContainsStrongDHopfBlock) :
    N.ResolvedIndexedOscillatoryCoreCertificate := by
  let J := Classical.choose hblock
  have hJ := Classical.choose_spec hblock
  exact
    { I := {i : I // i ∈ J}
      decI := inferInstance
      finI := inferInstance
      selection := C.restrict J
      dhopf := by
        rw [C.matrix_restrict J]
        exact hJ }

/-- Every exact class-II indexed core resolves after the two finite class-II matrix branches have
been supplied: Fisher--Fuller diagonal stabilization or the stable-codimension-one principal-block
theorem. -/
noncomputable def resolvedIndexedCoreOfClassII
    (hFFscale : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hStable : Matrix.StableCodimOneClassIIImpliesStrongDHopfBlockTarget)
    {I : Type} [DecidableEq I] [Fintype I]
    {N : Network S} (C : N.IndexedChildSelection I)
    (hC : C.IsOscillatoryCoreClassII) :
    N.ResolvedIndexedOscillatoryCoreCertificate := by
  apply Classical.choice
  rcases hC.fisherFuller_or_stableCodimOne with hFF | hcodim
  · exact ⟨resolvedIndexedCoreOfClassIIFF hFFscale C hC hFF⟩
  · exact ⟨resolvedIndexedCoreOfContainedBlock C
      (hStable C.matrix hC.unstableNegativeFeedback hcodim)⟩

/-- Exact finite-resolution theorem needed to make all search-facing class-I/class-II witnesses
uniform. -/
def IndexedCoreDHopfResolutionTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T),
    N.HasIndexedOscillatoryCore →
      Nonempty (N.ResolvedIndexedOscillatoryCoreCertificate)

/-- The three finite matrix theorems resolve every exact indexed oscillatory core. -/
theorem indexedCoreDHopfResolution_of_matrixTheorems
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hFFscale : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hStable : Matrix.StableCodimOneClassIIImpliesStrongDHopfBlockTarget) :
    IndexedCoreDHopfResolutionTarget := by
  intro T _ _ N hcore
  rcases hcore with hI | hII
  · obtain ⟨C⟩ := hI
    exact ⟨resolvedIndexedCoreOfClassI hP0 C.selection C.isClassI⟩
  · obtain ⟨C⟩ := hII
    exact ⟨resolvedIndexedCoreOfClassII hFFscale hStable C.selection C.isClassII⟩

/-- Once finite core resolution and the nonlinear D-Hopf theorem are available, the older generic
search-facing realization target follows automatically. -/
theorem indexedParameterRichOscillatoryCoreRealization
    (hresolve : IndexedCoreDHopfResolutionTarget)
    (hopen : ChildSelectionDHopfPerturbationTarget)
    (hDHopf : ParameterRichDHopfContinuationTarget) :
    IndexedParameterRichOscillatoryCoreRealizationTarget := by
  intro T _ _ N F hpaths _hcons hnd hcore
  obtain ⟨C⟩ := hresolve N hcore
  let x : Concentration T := fun _ => 1
  have hx : x.Positive := by intro i; exact zero_lt_one
  exact C.parameterRichOscillatoryCapacity hopen hDHopf F hpaths hnd x hx

end Network
end CRNT

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The original theorem-facing 2026 oscillatory-core target is derivable from the resolved indexed
pipeline.  `IsConsistent` remains in the historical public signature but is not needed by this
construction because `SupportsSmoothReactivityPaths` already supplies a coherent steady kinetic
realization at the chosen positive state. -/
theorem parameterRichOscillatoryCoreRealization_of_kernels
    (hP0 : Matrix.NotPMinusZeroImpliesUnstableScalingTarget.{0})
    (hFFscale : Matrix.FisherFullerStabilizingScalingTarget.{0})
    (hStable : Matrix.StableCodimOneClassIIImpliesStrongDHopfBlockTarget)
    (hopen : ChildSelectionDHopfPerturbationTarget)
    (hDHopf : ParameterRichDHopfContinuationTarget) :
    ParameterRichOscillatoryCoreRealizationTarget := by
  intro T _ _ N F hpaths _hcons hnd hcore
  let x : Concentration T := fun _ => 1
  have hx : x.Positive := by intro i; exact zero_lt_one
  rcases hcore with hI | hII
  · obtain ⟨C⟩ := hI
    let I := C.selection.toIndexed
    have hclass : I.IsOscillatoryCoreClassI := by
      change Matrix.IsOscillatoryCoreClassI I.matrix
      have hc : Matrix.IsOscillatoryCoreClassI C.selection.matrix := C.isClassI
      simpa [I] using hc
    let R := resolvedIndexedCoreOfClassI hP0 I hclass
    exact R.parameterRichOscillatoryCapacity hopen hDHopf F hpaths hnd x hx
  · obtain ⟨C⟩ := hII
    let I := C.selection.toIndexed
    have hclass : I.IsOscillatoryCoreClassII := by
      change Matrix.IsOscillatoryCoreClassII I.matrix
      have hc : Matrix.IsOscillatoryCoreClassII C.selection.matrix := C.isClassII
      simpa [I] using hc
    let R := resolvedIndexedCoreOfClassII hFFscale hStable I hclass
    exact R.parameterRichOscillatoryCapacity hopen hDHopf F hpaths hnd x hx

end Network
end CRNT
