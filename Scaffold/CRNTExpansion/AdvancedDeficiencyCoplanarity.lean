import Scaffold.CRNTExpansion.AdvancedDeficiencyClasses

/-!
# Basis-free linear relations among ADA kernel rows

The later Advanced Deficiency Algorithm uses coplanar sets of the row vectors `w_r`.  A basis of
`ker L_O` is unnecessary: a linear relation among rows is exactly a coefficient vector `c` whose
coordinate pairing `sum_r c_r alpha_r` vanishes for every `alpha` in `ker L_O`.

This file records that invariant relation and a three-row coplanarity predicate suitable for the
`M_i` ordering constraints in the later ADA steps.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A basis-free linear relation among the kernel rows `w_r`. -/
def KernelRowRelation (N : Network S) (O : Finset N.R) (c : (↥O) → ℝ) : Prop :=
  ∀ alpha : (↥O) → ℝ,
    alpha ∈ LinearMap.ker (N.orientedStoichLinearMap O) →
      (∑ r : ↥O, c r * alpha r) = 0

/-- The zero coefficient vector is always a row relation. -/
theorem kernelRowRelation_zero (N : Network S) (O : Finset N.R) :
    N.KernelRowRelation O 0 := by
  intro alpha hker
  simp

/-- Row relations are closed under addition. -/
theorem KernelRowRelation.add {N : Network S} {O : Finset N.R}
    {c d : (↥O) → ℝ} (hc : N.KernelRowRelation O c) (hd : N.KernelRowRelation O d) :
    N.KernelRowRelation O (c + d) := by
  intro alpha hker
  have hc0 := hc alpha hker
  have hd0 := hd alpha hker
  change (∑ r : ↥O, (c r + d r) * alpha r) = 0
  calc
    (∑ r : ↥O, (c r + d r) * alpha r) =
        (∑ r : ↥O, c r * alpha r) + (∑ r : ↥O, d r * alpha r) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = 0 := by rw [hc0, hd0, add_zero]

/-- Row relations are closed under scalar multiplication. -/
theorem KernelRowRelation.smul {N : Network S} {O : Finset N.R}
    (a : ℝ) {c : (↥O) → ℝ} (hc : N.KernelRowRelation O c) :
    N.KernelRowRelation O (a • c) := by
  intro alpha hker
  have hc0 := hc alpha hker
  simp only [Pi.smul_apply, smul_eq_mul]
  calc
    (∑ r : ↥O, (a * c r) * alpha r) = a * (∑ r : ↥O, c r * alpha r) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    _ = 0 := by rw [hc0, mul_zero]

/-- Three selected oriented reactions are coplanarly related when a nontrivial coefficient triple
supported on them annihilates every vector in `ker L_O`.  This is the basis-free content needed for
ADA coplanar-set ordering constraints; later files may add the exact sign/order hypotheses from the
published algorithm. -/
def KernelRowCoplanarTriple (N : Network S) (O : Finset N.R)
    (i j k : ↥O) : Prop :=
  ∃ ci cj ck : ℝ, ci ≠ 0 ∧ cj ≠ 0 ∧ ck ≠ 0 ∧
    N.KernelRowRelation O (fun r =>
      (if r = i then ci else 0) + (if r = j then cj else 0) +
        (if r = k then ck else 0))

end Network
end CRNT
