import CRNT.Stoich.Subspace

/-!
# Basis-free kernel coordinates for the Advanced Deficiency Algorithm

This file corrects an important representational issue in the current ADA scaffold.

In the published Advanced Deficiency Algorithm, after choosing an orientation `O`, one forms

  L_O alpha = sum_{r in O} alpha_r * reactionVector(r)

and chooses a basis of `ker L_O`.  The vector `w_r` attached to an oriented reaction is the row of
that kernel basis at coordinate `r`.  Colinearity classes are classes of these `w_r` vectors --
**not classes of stoichiometric reaction vectors**.

A basis choice is unnecessary in Lean.  The row `w_r` is canonically the coordinate functional
`alpha |-> alpha_r` restricted to `ker L_O`.  Two rows are colinear exactly when those restricted
coordinate functionals are nonzero scalar multiples.  The definitions below capture that invariant
content without choosing a basis.

The remaining scaffold still needs a parallel-reaction-aware formalization of a valid orientation
(one direction of each reversible channel pair, every irreversible channel retained), colinkage
sets, coplanar sets, class signs, and Steps 9--13 of the ADA inequalities.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Kernel equation for a chosen finite set `O` of oriented reaction channels.  This is the
basis-free form of `ker L_O`. -/
def OrientedStoichKernel (N : Network S) (O : Finset N.R) (alpha : (↥O) -> ℝ) : Prop :=
  (∑ r : ↥O, alpha r • N.reactionVector r.1) = (0 : S -> ℝ)

/-- An oriented reaction belongs to the ADA zero colinearity class when its coordinate functional
vanishes on the whole oriented stoichiometric kernel. -/
def KernelCoordinateZero (N : Network S) (O : Finset N.R) (r : ↥O) : Prop :=
  ∀ alpha : (↥O) -> ℝ, N.OrientedStoichKernel O alpha -> alpha r = 0

/-- Basis-free colinearity of two ADA kernel rows.  The scalar is required to be nonzero, matching
published colinearity classes; the zero class is represented separately by `KernelCoordinateZero`. -/
def KernelCoordinateColinear (N : Network S) (O : Finset N.R) (r q : ↥O) : Prop :=
  ∃ c : ℝ, c ≠ 0 ∧
    ∀ alpha : (↥O) -> ℝ, N.OrientedStoichKernel O alpha -> alpha r = c * alpha q

@[refl] theorem kernelCoordinateColinear_refl (N : Network S) (O : Finset N.R) (r : ↥O) :
    N.KernelCoordinateColinear O r r := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro alpha _
  simp

/-- A nonzero scalar multiple of a zero kernel coordinate is again zero.  This is the elementary
fact that makes the zero class disjoint from every nonzero colinearity class. -/
theorem kernelCoordinateZero_of_colinear_left (N : Network S) (O : Finset N.R)
    {r q : ↥O} (hr : N.KernelCoordinateZero O r)
    (hcol : N.KernelCoordinateColinear O r q) : N.KernelCoordinateZero O q := by
  rcases hcol with ⟨c, hc, hrel⟩
  intro alpha hker
  have h := hrel alpha hker
  rw [hr alpha hker] at h
  have hzero : c * alpha q = 0 := h.symm
  exact (mul_eq_zero.mp hzero).resolve_left hc

/-- Colinearity is symmetric.  Algebraically this is just multiplication by the inverse nonzero
scalar; mathematically it is the basis-free counterpart of row-vector colinearity. -/
@[symm] theorem kernelCoordinateColinear_symm (N : Network S) (O : Finset N.R)
    {r q : ↥O} (hcol : N.KernelCoordinateColinear O r q) :
    N.KernelCoordinateColinear O q r := by
  rcases hcol with ⟨c, hc, hrel⟩
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  intro alpha hker
  have h := hrel alpha hker
  calc
    alpha q = c⁻¹ * (c * alpha q) := by
      rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
    _ = c⁻¹ * alpha r := by rw [← h]

/-- Colinearity is transitive, with the witnessing scalars multiplying. -/
@[trans] theorem kernelCoordinateColinear_trans (N : Network S) (O : Finset N.R)
    {r q t : ↥O} (hrq : N.KernelCoordinateColinear O r q)
    (hqt : N.KernelCoordinateColinear O q t) : N.KernelCoordinateColinear O r t := by
  rcases hrq with ⟨c, hc, hrelc⟩
  rcases hqt with ⟨d, hd, hreld⟩
  refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
  intro alpha hker
  rw [hrelc alpha hker, hreld alpha hker, mul_assoc]

/-- If the right coordinate functional is identically zero, every colinear left coordinate is
identically zero as well. -/
theorem kernelCoordinateZero_of_colinear_right (N : Network S) (O : Finset N.R)
    {r q : ↥O} (hq : N.KernelCoordinateZero O q)
    (hcol : N.KernelCoordinateColinear O r q) : N.KernelCoordinateZero O r := by
  rcases hcol with ⟨c, _hc, hrel⟩
  intro alpha hker
  rw [hrel alpha hker, hq alpha hker, mul_zero]

/-- Colinear kernel coordinates belong to the zero class simultaneously. -/
theorem kernelCoordinateZero_iff_of_colinear (N : Network S) (O : Finset N.R)
    {r q : ↥O} (hcol : N.KernelCoordinateColinear O r q) :
    N.KernelCoordinateZero O r ↔ N.KernelCoordinateZero O q := by
  constructor
  · intro hr
    exact N.kernelCoordinateZero_of_colinear_left O hr hcol
  · intro hq
    exact N.kernelCoordinateZero_of_colinear_right O hq hcol

/-- Any two coordinates that vanish on `ker L_O` are colinear; together they form the distinguished
zero class of the Advanced Deficiency Algorithm. -/
theorem kernelCoordinateColinear_of_zero (N : Network S) (O : Finset N.R)
    {r q : ↥O} (hr : N.KernelCoordinateZero O r) (hq : N.KernelCoordinateZero O q) :
    N.KernelCoordinateColinear O r q := by
  refine ⟨1, one_ne_zero, ?_⟩
  intro alpha hker
  rw [hr alpha hker, hq alpha hker]
  simp

/-- Basis-free kernel-row colinearity is an equivalence relation on the oriented reaction set.
Its quotient is the correct starting point for the zero/nonzero colinearity classes in the ADA. -/
theorem kernelCoordinateColinear_equivalence (N : Network S) (O : Finset N.R) :
    Equivalence (N.KernelCoordinateColinear O) :=
  ⟨fun r => N.kernelCoordinateColinear_refl O r,
    fun h => N.kernelCoordinateColinear_symm O h,
    fun h₁ h₂ => N.kernelCoordinateColinear_trans O h₁ h₂⟩

/-- The setoid of published ADA kernel-row colinearity classes. -/
noncomputable def kernelCoordinateSetoid (N : Network S) (O : Finset N.R) : Setoid (↥O) where
  r := N.KernelCoordinateColinear O
  iseqv := N.kernelCoordinateColinear_equivalence O

/-- Basis-free ADA colinearity classes for a fixed orientation. -/
abbrev KernelColinearityClass (N : Network S) (O : Finset N.R) :=
  Quotient (N.kernelCoordinateSetoid O)

end Network
end CRNT
