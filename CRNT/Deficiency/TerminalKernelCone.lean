import CRNT.Deficiency.TerminalKernelDimension
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The nonnegative kinetic-kernel cone of an arbitrary reaction graph

For a general finite directed reaction graph, the kernel of the kinetic Laplacian has
one extremal ray for each terminal strong-linkage class.  Nonnegative kernel vectors
are therefore precisely the nonnegative linear combinations of the terminal Perron
modes.  Strict positivity on every complex is possible exactly when every SCC is
terminal, i.e. exactly under weak reversibility.

This is the arbitrary-graph analogue of the linkage-class tree-constant cone theorem.
-/

namespace CRNT
namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Coordinate map from terminal-SLC coefficients into the kinetic kernel. -/
noncomputable def terminalKernelCoordinates (N : Network S) (κ : N.RateConstants) :
    (N.TerminalSLC → ℝ) →ₗ[ℝ] (N.ComplexIdx → ℝ) where
  toFun a := ∑ σ, a σ • N.terminalKernelMode κ σ
  map_add' a b := by
    classical
    simp [add_smul, Finset.sum_add_distrib]
  map_smul' c a := by
    classical
    simp [smul_smul, Finset.smul_sum]

/-- Terminal coordinates always produce kinetic-kernel vectors. -/
theorem terminalKernelCoordinates_mem_kernel (N : Network S) (κ : N.RateConstants)
    (a : N.TerminalSLC → ℝ) :
    N.kineticMap κ (N.terminalKernelCoordinates κ a) = 0 := by
  classical
  simp [terminalKernelCoordinates, map_sum, N.terminalKernelMode_mem_kernel κ]

/-- Terminal-coordinate map is injective because terminal modes have disjoint support. -/
theorem terminalKernelCoordinates_injective (N : Network S) (κ : N.RateConstants) :
    Function.Injective (N.terminalKernelCoordinates κ) := by
  intro a b hab
  have hlin := N.terminalKernelModes_linearIndependent κ
  rw [Fintype.linearIndependent_iff] at hlin
  have hzero : ∑ σ : N.TerminalSLC,
      (a σ - b σ) • N.terminalKernelMode κ σ = 0 := by
    calc
      (∑ σ : N.TerminalSLC, (a σ - b σ) • N.terminalKernelMode κ σ) =
          N.terminalKernelCoordinates κ a - N.terminalKernelCoordinates κ b := by
            simp [terminalKernelCoordinates, sub_smul, Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr hab
  funext σ
  have hz := hlin (fun τ => a τ - b τ) hzero σ
  exact sub_eq_zero.mp hz

/-- Every kinetic-kernel vector has unique terminal-SLC coordinates. -/
theorem existsUnique_terminalKernelCoordinates (N : Network S) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} (hv : N.kineticMap κ v = 0) :
    ∃! a : N.TerminalSLC → ℝ, v = N.terminalKernelCoordinates κ a := by
  have hvspan : v ∈ Submodule.span ℝ (Set.range (N.terminalKernelMode κ)) :=
    N.kineticKernel_le_span_terminalModes κ (by simpa [LinearMap.mem_ker] using hv)
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hvspan
  refine ⟨a, ?_, ?_⟩
  · simpa [terminalKernelCoordinates] using ha.symm
  · intro b hb
    apply N.terminalKernelCoordinates_injective κ
    have haa : N.terminalKernelCoordinates κ a = v := by
      simpa [terminalKernelCoordinates] using ha
    rw [haa]
    exact hb.symm

/-- A nonnegative kernel vector has nonnegative terminal coordinates. -/
theorem terminalCoefficients_nonneg_of_kernel_nonneg
    (N : Network S) (κ : N.RateConstants)
    (a : N.TerminalSLC → ℝ)
    (h : ∀ c, 0 ≤ N.terminalKernelCoordinates κ a c) :
    ∀ σ, 0 ≤ a σ := by
  intro σ
  have hp := N.terminalKernelMode_pos κ σ (StronglyLinked.refl N σ.val.out.val)
  have hc := h σ.val.out
  -- At a representative of `σ`, every other terminal mode vanishes.
  classical
  have hcoord : N.terminalKernelCoordinates κ a σ.val.out =
      a σ * N.terminalKernelMode κ σ σ.val.out := by
    unfold terminalKernelCoordinates
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_eq_single σ (fun τ _ hne => by
      have hoff : ¬ N.StronglyLinked τ.val.out.val σ.val.out.val := by
        intro hsl
        apply hne
        apply Subtype.ext
        calc
          τ.val = Quotient.mk N.stronglyLinkedSetoid τ.val.out := (Quotient.out_eq τ.val).symm
          _ = Quotient.mk N.stronglyLinkedSetoid σ.val.out :=
            Quotient.sound (show N.stronglyLinkedSetoid.r τ.val.out σ.val.out from hsl)
          _ = σ.val := Quotient.out_eq _
      rw [N.terminalKernelMode_zero_off κ τ hoff, mul_zero]) (by simp)
  rw [hcoord] at hc
  nlinarith

/-- Nonnegative terminal coordinates produce a nonnegative kernel vector. -/
theorem terminalKernelCoordinates_nonneg
    (N : Network S) (κ : N.RateConstants)
    {a : N.TerminalSLC → ℝ} (ha : ∀ σ, 0 ≤ a σ) :
    ∀ c, 0 ≤ N.terminalKernelCoordinates κ a c := by
  intro c
  classical
  unfold terminalKernelCoordinates
  simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply Finset.sum_nonneg
  intro σ _
  exact mul_nonneg (ha σ) (by
    by_cases hs : N.StronglyLinked σ.val.out.val c.val
    · exact (N.terminalKernelMode_pos κ σ hs).le
    · rw [N.terminalKernelMode_zero_off κ σ hs])

/-- **Nonnegative kinetic-kernel cone theorem.** -/
theorem nonnegative_kineticKernel_iff_terminalCoefficients
    (N : Network S) (κ : N.RateConstants) (v : N.ComplexIdx → ℝ) :
    (N.kineticMap κ v = 0 ∧ ∀ c, 0 ≤ v c) ↔
      ∃ a : N.TerminalSLC → ℝ,
        (∀ σ, 0 ≤ a σ) ∧ v = N.terminalKernelCoordinates κ a := by
  constructor
  · rintro ⟨hvker, hvnn⟩
    obtain ⟨a, ha, -⟩ := N.existsUnique_terminalKernelCoordinates κ hvker
    refine ⟨a, ?_, ha⟩
    apply N.terminalCoefficients_nonneg_of_kernel_nonneg κ a
    simpa [← ha] using hvnn
  · rintro ⟨a, ha, rfl⟩
    exact ⟨N.terminalKernelCoordinates_mem_kernel κ a,
      N.terminalKernelCoordinates_nonneg κ ha⟩

/-- The terminal modes are the support-minimal nonzero rays of the nonnegative
kinetic-kernel cone. -/
def IsTerminalKernelExtremeRay (N : Network S) (κ : N.RateConstants)
    (v : N.ComplexIdx → ℝ) : Prop :=
  N.kineticMap κ v = 0 ∧
  (∀ c, 0 ≤ v c) ∧ v ≠ 0 ∧
  ∀ w, N.kineticMap κ w = 0 → (∀ c, 0 ≤ w c) →
    (∀ c, w c ≠ 0 → v c ≠ 0) → ∃ t : ℝ, 0 ≤ t ∧ w = t • v

/-- Every canonical terminal mode spans an extreme ray. -/
theorem terminalKernelMode_extreme (N : Network S) (κ : N.RateConstants)
    (σ : N.TerminalSLC) :
    N.IsTerminalKernelExtremeRay κ (N.terminalKernelMode κ σ) := by
  refine ⟨N.terminalKernelMode_mem_kernel κ σ, ?_, ?_, ?_⟩
  · intro c
    by_cases h : N.StronglyLinked σ.val.out.val c.val
    · exact (N.terminalKernelMode_pos κ σ h).le
    · rw [N.terminalKernelMode_zero_off κ σ h]
  · intro hzero
    have hp := N.terminalKernelMode_pos κ σ (StronglyLinked.refl N σ.val.out.val)
    rw [hzero] at hp
    simp at hp
  · intro w hwker hwnn hsupp
    have hwoff : ∀ c, ¬ N.StronglyLinked σ.val.out.val c.val → w c = 0 := by
      intro c hc
      by_contra hwne
      have hmne := hsupp c hwne
      exact hmne (N.terminalKernelMode_zero_off κ σ hc)
    obtain ⟨t, ht⟩ := N.terminalSLC_kernel_unique κ
      (fun c hc => N.terminalKernelMode_pos κ σ hc)
      (fun c hc => N.terminalKernelMode_zero_off κ σ hc)
      (N.terminalKernelMode_mem_kernel κ σ) hwoff hwker
    refine ⟨t, ?_, ht⟩
    have hp := N.terminalKernelMode_pos κ σ (StronglyLinked.refl N σ.val.out.val)
    have hw := hwnn σ.val.out
    have hcoord := congrFun ht σ.val.out
    simp only [Pi.smul_apply, smul_eq_mul] at hcoord
    rw [hcoord] at hw
    nlinarith

end Network
end CRNT
