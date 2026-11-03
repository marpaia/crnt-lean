import CRNT.Equilibria.TreeConstants
import CRNT.Equilibria.ComplexBalanced
import CRNT.Dynamics.MassActionAlgebra
import CRNT.Deficiency.PerClassKernelUnique

/-!
# Tree-constant binomials for complex-balanced equilibria

On each weakly reversible linkage class, the kinetic kernel is one-dimensional.
Consequently a positive complex-balanced monomial vector is proportional to the
vector of tree constants.  This yields the classical tree-constant binomials

`K_j x^{y_i} = K_i x^{y_j}`

for linked complexes `i,j`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Source monomial attached to a complex index. -/
def complexMonomial (N : Network S) (x : Concentration S) (c : N.ComplexIdx) : ℝ :=
  c.1.massActionMonomial x

/-- The monomial vector of a complex-balanced state lies in the kinetic kernel. -/
theorem complexMonomial_kineticKernel_of_complexBalanced (N : Network S)
    (κ : N.RateConstants) {x : Concentration S} (hcb : N.IsComplexBalanced κ x) :
    N.kineticMap κ (N.complexMonomial x) = 0 := by
  -- `complexMonomial` is the same vector as `complexMonomialVector`.
  change N.kineticMap κ (N.complexMonomialVector x) = 0
  exact (N.isComplexBalanced_iff_kineticMap κ x).1 hcb

/-- **Linkage-class kernel proportionality.** On a weakly reversible linkage class,
any two positive kinetic-kernel vectors have the same coordinate ratios.

This is the one-dimensional-kernel statement underlying the tree-constant formulas. -/
theorem positive_kineticKernel_ratio_eq (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {a b : N.ComplexIdx → ℝ}
    (ha : ∀ c, 0 < a c) (_hb : ∀ c, 0 < b c)
    (hka : N.kineticMap κ a = 0) (hkb : N.kineticMap κ b = 0)
    {i j : N.ComplexIdx} (hij : N.Linked i.1 j.1) :
    a i * b j = a j * b i := by
  classical
  let θ : Quotient N.linkedSetoid := N.classOf i
  have hjθ : N.classOf j = θ := by
    exact Quotient.sound hij.symm
  have hsc : ∀ c c' : N.ComplexIdx,
      N.classOf c = θ → N.classOf c' = θ → N.Reaches c.val c'.val := by
    intro c c' hc hc'
    apply hwr.reaches_of_linked
    exact Quotient.exact (hc.trans hc'.symm)
  have hapos : ∀ c, N.classOf c = θ → 0 < N.restrictToClass θ a c := by
    intro c hc
    rw [N.restrictToClass_apply_of_eq a hc]
    exact ha c
  have haoff : ∀ c, N.classOf c ≠ θ → N.restrictToClass θ a c = 0 := by
    intro c hc
    exact N.restrictToClass_apply_of_ne a hc
  have hak : N.kineticMap κ (N.restrictToClass θ a) = 0 := by
    rw [N.kineticMap_restrictToClass κ, hka]
    funext c
    simp [restrictToClass]
  have hboff : ∀ c, N.classOf c ≠ θ → N.restrictToClass θ b c = 0 := by
    intro c hc
    exact N.restrictToClass_apply_of_ne b hc
  have hbk : N.kineticMap κ (N.restrictToClass θ b) = 0 := by
    rw [N.kineticMap_restrictToClass κ, hkb]
    funext c
    simp [restrictToClass]
  obtain ⟨t, ht⟩ := N.perClass_kernel_unique κ θ hsc hapos haoff hak hboff hbk
  have hi := congrFun ht i
  have hj := congrFun ht j
  have hiθ : N.classOf i = θ := rfl
  simp only [Pi.smul_apply, smul_eq_mul] at hi hj
  rw [N.restrictToClass_apply_of_eq b hiθ, N.restrictToClass_apply_of_eq a hiθ] at hi
  rw [N.restrictToClass_apply_of_eq b hjθ, N.restrictToClass_apply_of_eq a hjθ] at hj
  rw [hi, hj]
  ring

/-- **Tree-constant binomial.** Positive complex-balanced states satisfy the classical
binomial relations on every linkage class. -/
theorem treeConstant_binomial_of_complexBalanced (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive)
    (hcb : N.IsComplexBalanced κ x) {i j : N.ComplexIdx}
    (hij : N.Linked i.1 j.1) :
    N.treeConstant κ j * N.complexMonomial x i =
      N.treeConstant κ i * N.complexMonomial x j := by
  have hTpos : ∀ c, 0 < N.treeConstantVector κ c :=
    (N.treeConstantVector_positive_kernel κ hwr).1
  have hMpos : ∀ c, 0 < N.complexMonomial x c := by
    intro c
    exact Complex.massActionMonomial_pos hx c.1
  have hratio := N.positive_kineticKernel_ratio_eq κ hwr hTpos hMpos
    (N.treeConstant_kineticKernel κ)
    (N.complexMonomial_kineticKernel_of_complexBalanced κ hcb) hij
  simpa [treeConstantVector, complexMonomial, mul_comm] using hratio.symm

/-- Tree-constant ratios determine monomial ratios at a positive complex-balanced state. -/
theorem complexMonomial_ratio_eq_treeConstant_ratio (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive)
    (hcb : N.IsComplexBalanced κ x) {i j : N.ComplexIdx}
    (hij : N.Linked i.1 j.1) :
    N.complexMonomial x i / N.complexMonomial x j =
      N.treeConstant κ i / N.treeConstant κ j := by
  have hbin := N.treeConstant_binomial_of_complexBalanced κ hwr hx hcb hij
  have hmj : N.complexMonomial x j ≠ 0 := (Complex.massActionMonomial_pos hx j.1).ne'
  have hTj : N.treeConstant κ j ≠ 0 :=
    (N.treeConstant_pos_of_weaklyReversible κ hwr j).ne'
  field_simp
  nlinarith

end Network

end CRNT
