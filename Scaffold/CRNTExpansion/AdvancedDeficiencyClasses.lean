import Scaffold.CRNTExpansion.AdvancedDeficiencyLinearMap

/-!
# Zero and nonzero ADA kernel-row classes

The published ADA separates the distinguished zero class from the nonzero colinearity classes of
the kernel rows `w_r`.  `AdvancedDeficiencyKernel` proves that basis-free kernel-coordinate
colinearity is an equivalence relation; this file packages the two class layers explicitly.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The distinguished zero class: coordinates whose restriction to `ker L_O` is identically zero. -/
def zeroKernelCoordinates (N : Network S) (O : Finset N.R) : Set (↥O) :=
  {r | N.KernelCoordinateZero O r}

@[simp] theorem mem_zeroKernelCoordinates_iff (N : Network S) (O : Finset N.R) (r : ↥O) :
    r ∈ N.zeroKernelCoordinates O ↔ N.KernelCoordinateZero O r :=
  Iff.rfl

/-- Nonzero oriented reactions, i.e. rows not belonging to the distinguished zero class. -/
abbrev NonzeroKernelCoordinate (N : Network S) (O : Finset N.R) :=
  {r : ↥O // ¬ N.KernelCoordinateZero O r}

/-- Colinearity restricted to nonzero kernel coordinates is again an equivalence relation. -/
theorem nonzeroKernelCoordinateColinear_equivalence (N : Network S) (O : Finset N.R) :
    Equivalence (fun r q : N.NonzeroKernelCoordinate O =>
      N.KernelCoordinateColinear O r.1 q.1) := by
  constructor
  · intro r
    exact N.kernelCoordinateColinear_refl O r.1
  · intro r q h
    exact N.kernelCoordinateColinear_symm O h
  · intro r q t hrq hqt
    exact N.kernelCoordinateColinear_trans O hrq hqt

/-- Setoid of the nonzero published ADA colinearity classes. -/
noncomputable def nonzeroKernelCoordinateSetoid (N : Network S) (O : Finset N.R) :
    Setoid (N.NonzeroKernelCoordinate O) where
  r := fun a b => N.KernelCoordinateColinear O a.1 b.1
  iseqv := N.nonzeroKernelCoordinateColinear_equivalence O

/-- Nonzero ADA colinearity classes. -/
abbrev NonzeroKernelColinearityClass (N : Network S) (O : Finset N.R) :=
  Quotient (N.nonzeroKernelCoordinateSetoid O)

/-- A nonzero class can never contain a zero coordinate.  This is the formal disjointness of the
distinguished zero class from the quotient of nonzero classes. -/
theorem nonzeroKernelCoordinate_not_mem_zeroClass
    (N : Network S) (O : Finset N.R) (r : N.NonzeroKernelCoordinate O) :
    r.1 ∉ N.zeroKernelCoordinates O :=
  r.2

end Network
end CRNT
