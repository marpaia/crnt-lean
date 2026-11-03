import CRNT.Deficiency.TerminalKernelCone
import CRNT.Graph.WeakReversibility

/-!
# Faces of the nonnegative kinetic-kernel cone

The nonnegative kernel cone of the kinetic Laplacian is simplicial: its extremal rays are
exactly the canonical modes of the terminal strong-linkage classes.  Faces correspond to
subsets of terminal classes.  Strict positivity on every complex occurs exactly when every
strong-linkage class is terminal, i.e. when the network is weakly reversible.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Support of a terminal kernel coordinate vector at the level of terminal SLCs. -/
noncomputable def terminalCoefficientSupport (N : Network S) (a : N.TerminalSLC → ℝ) :
    Finset N.TerminalSLC := Finset.univ.filter fun σ => a σ ≠ 0

/-- Every nonzero extreme ray of the nonnegative kinetic kernel is a positive multiple of
one terminal mode. -/
theorem extremeKernelRay_eq_terminalMode
    (N : Network S) (κ : N.RateConstants) {v : N.ComplexIdx → ℝ}
    (hv : N.IsTerminalKernelExtremeRay κ v) :
    ∃ σ : N.TerminalSLC, ∃ a : ℝ, 0 < a ∧ v = a • N.terminalKernelMode κ σ := by
  classical
  obtain ⟨coeff, hnonneg, hrepr⟩ :=
    (N.nonnegative_kineticKernel_iff_terminalCoefficients κ v).mp ⟨hv.1, hv.2.1⟩
  have hcoeff_ne : coeff ≠ 0 := by
    intro hzero
    rw [hzero, map_zero] at hrepr
    exact hv.2.2.1 hrepr
  have hex : ∃ σ : N.TerminalSLC, coeff σ ≠ 0 := by
    by_contra h
    push Not at h
    apply hcoeff_ne
    funext σ
    exact h σ
  obtain ⟨σ, hσne⟩ := hex
  have hσpos : 0 < coeff σ := lt_of_le_of_ne (hnonneg σ) (Ne.symm hσne)
  let w : N.ComplexIdx → ℝ := coeff σ • N.terminalKernelMode κ σ
  have hwker : N.kineticMap κ w = 0 := by
    dsimp [w]
    rw [map_smul, N.terminalKernelMode_mem_kernel κ σ, smul_zero]
  have hwnn : ∀ c, 0 ≤ w c := by
    intro c
    dsimp [w]
    exact mul_nonneg hσpos.le (by
      by_cases hs : N.StronglyLinked σ.val.out.val c.val
      · exact (N.terminalKernelMode_pos κ σ hs).le
      · rw [N.terminalKernelMode_zero_off κ σ hs])
  have hsupp : ∀ c, w c ≠ 0 → v c ≠ 0 := by
    intro c hwc
    have hsl : N.StronglyLinked σ.val.out.val c.val := by
      by_contra hnot
      have hz := N.terminalKernelMode_zero_off κ σ hnot
      apply hwc
      dsimp [w]
      simp [hz]
    have hmodepos := N.terminalKernelMode_pos κ σ hsl
    have hsum : (∑ τ : N.TerminalSLC, coeff τ * N.terminalKernelMode κ τ c) =
        coeff σ * N.terminalKernelMode κ σ c := by
      apply Finset.sum_eq_single σ
      · intro τ _ hτσ
        have hoff : ¬ N.StronglyLinked τ.val.out.val c.val := by
          intro hτc
          apply hτσ
          apply Subtype.ext
          calc
            τ.val = Quotient.mk N.stronglyLinkedSetoid τ.val.out := (Quotient.out_eq τ.val).symm
            _ = Quotient.mk N.stronglyLinkedSetoid c := Quotient.sound hτc
            _ = Quotient.mk N.stronglyLinkedSetoid σ.val.out := Quotient.sound hsl.symm
            _ = σ.val := Quotient.out_eq _
        rw [N.terminalKernelMode_zero_off κ τ hoff, mul_zero]
      · simp
    have hvc : v c = coeff σ * N.terminalKernelMode κ σ c := by
      rw [hrepr]
      unfold terminalKernelCoordinates
      simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact hsum
    rw [hvc]
    exact mul_ne_zero hσne hmodepos.ne'
  obtain ⟨t, ht_nonneg, hwt⟩ := hv.2.2.2 w hwker hwnn hsupp
  have ht_ne : t ≠ 0 := by
    intro ht0
    have hw0 : w = 0 := by rw [hwt, ht0, zero_smul]
    have hp := N.terminalKernelMode_pos κ σ (StronglyLinked.refl N σ.val.out.val)
    have h := congrFun hw0 σ.val.out
    dsimp [w] at h
    nlinarith [hp, hσpos]
  have hcoord_w : w = N.terminalKernelCoordinates κ
      (fun τ => if τ = σ then coeff σ else 0) := by
    funext c
    dsimp [w]
    unfold terminalKernelCoordinates
    simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp [ite_mul]
  let b : N.TerminalSLC → ℝ := fun τ => if τ = σ then coeff σ else 0
  have hcoord_w' : w = N.terminalKernelCoordinates κ b := by
    simpa [b] using hcoord_w
  have hcoeff_eq : b = t • coeff := by
    apply N.terminalKernelCoordinates_injective κ
    calc
      N.terminalKernelCoordinates κ b = w := hcoord_w'.symm
      _ = t • v := hwt
      _ = t • N.terminalKernelCoordinates κ coeff := by rw [hrepr]
      _ = N.terminalKernelCoordinates κ (t • coeff) := by rw [map_smul]
  have ht_one : t = 1 := by
    have hs := congrFun hcoeff_eq σ
    simp [b, Pi.smul_apply, smul_eq_mul] at hs
    nlinarith [hσpos]
  refine ⟨σ, coeff σ, hσpos, ?_⟩
  rw [ht_one, one_smul] at hwt
  exact hwt.symm

/-- Complete extreme-ray characterization. -/
theorem terminalKernelExtremeRay_iff
    (N : Network S) (κ : N.RateConstants) (v : N.ComplexIdx → ℝ) :
    N.IsTerminalKernelExtremeRay κ v ↔
      ∃ σ : N.TerminalSLC, ∃ a : ℝ, 0 < a ∧ v = a • N.terminalKernelMode κ σ := by
  constructor
  · exact N.extremeKernelRay_eq_terminalMode κ
  · rintro ⟨σ, a, ha, rfl⟩
    have hbase := N.terminalKernelMode_extreme κ σ
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [map_smul, hbase.1, smul_zero]
    · intro c
      simp only [Pi.smul_apply, smul_eq_mul]
      exact mul_nonneg ha.le (hbase.2.1 c)
    · intro hz
      have hp := N.terminalKernelMode_pos κ σ (StronglyLinked.refl N σ.val.out.val)
      have hcoord := congrFun hz σ.val.out
      simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
      nlinarith
    · intro w hwker hwnn hsupp
      have hsuppbase : ∀ c, w c ≠ 0 → N.terminalKernelMode κ σ c ≠ 0 := by
        intro c hwc
        have h := hsupp c hwc
        simp only [Pi.smul_apply, smul_eq_mul] at h
        exact (mul_ne_zero_iff.mp h).2
      obtain ⟨t, ht, hwt⟩ := hbase.2.2.2 w hwker hwnn hsuppbase
      refine ⟨t / a, div_nonneg ht ha.le, ?_⟩
      rw [hwt, smul_smul]
      congr 1
      exact (div_mul_cancel₀ t ha.ne').symm

/-- A nonnegative kinetic-kernel face selected by a set of terminal SLCs. -/
def TerminalKernelFace (N : Network S) (κ : N.RateConstants)
    (T : Finset N.TerminalSLC) : Set (N.ComplexIdx → ℝ) :=
  {v | ∃ a : N.TerminalSLC → ℝ,
      (∀ σ, 0 ≤ a σ) ∧
      (∀ σ, σ ∉ T → a σ = 0) ∧
      v = N.terminalKernelCoordinates κ a}

/-- Inclusion of terminal-class subsets gives inclusion of kernel-cone faces. -/
theorem terminalKernelFace_mono (N : Network S) (κ : N.RateConstants)
    {T U : Finset N.TerminalSLC} (hTU : T ⊆ U) :
    N.TerminalKernelFace κ T ⊆ N.TerminalKernelFace κ U := by
  rintro v ⟨a, ha, hsupp, rfl⟩
  exact ⟨a, ha, fun σ hσ => hsupp σ (fun h => hσ (hTU h)), rfl⟩

/-- Face dimension equals the number of selected terminal classes. -/
theorem finrank_terminalKernelFace_span (N : Network S) (κ : N.RateConstants)
    (T : Finset N.TerminalSLC) :
    Module.finrank ℝ (Submodule.span ℝ (N.TerminalKernelFace κ T)) = T.card := by
  classical
  let f : {σ : N.TerminalSLC // σ ∈ T} → (N.ComplexIdx → ℝ) :=
    fun σ => N.terminalKernelMode κ σ.1
  have hli : LinearIndependent ℝ f :=
    (N.terminalKernelModes_linearIndependent κ).comp Subtype.val Subtype.val_injective
  have hspan : Submodule.span ℝ (N.TerminalKernelFace κ T) =
      Submodule.span ℝ (Set.range f) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      rcases hv with ⟨a, ha, hsupp, rfl⟩
      unfold terminalKernelCoordinates
      apply Submodule.sum_mem
      intro σ _
      by_cases hσ : σ ∈ T
      · apply Submodule.smul_mem
        exact Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩
      · rw [hsupp σ hσ, zero_smul]
        exact Submodule.zero_mem _
    · rw [Submodule.span_le]
      rintro _ ⟨σ, rfl⟩
      apply Submodule.subset_span
      refine ⟨(fun τ : N.TerminalSLC => if τ = σ.1 then 1 else 0), ?_, ?_, ?_⟩
      · intro τ
        by_cases h : τ = σ.1 <;> simp [h]
      · intro τ hτ
        by_cases heq : τ = σ.1
        · subst τ
          exact False.elim (hτ σ.2)
        · simp [heq]
      · unfold terminalKernelCoordinates
        funext c
        simp only [LinearMap.coe_mk, AddHom.coe_mk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        simp [ite_mul]
        rfl
  rw [hspan, finrank_span_eq_card hli]
  exact Fintype.card_coe T

/-- Existence of a strictly positive kinetic-kernel vector forces weak reversibility. -/
theorem weaklyReversible_of_exists_strictlyPositive_kineticKernel
    (N : Network S) (κ : N.RateConstants)
    (h : ∃ v : N.ComplexIdx → ℝ,
      N.kineticMap κ v = 0 ∧ ∀ c, 0 < v c) :
    N.WeaklyReversible := by
  obtain ⟨v, hvker, hvpos⟩ := h
  exact N.weaklyReversible_of_exists_positive_kineticKernel κ ⟨v, hvpos, hvker⟩

/-- Weak reversibility is exactly existence of a strictly positive kinetic-kernel vector. -/
theorem weaklyReversible_iff_exists_strictlyPositive_kineticKernel
    (N : Network S) (κ : N.RateConstants) :
    N.WeaklyReversible ↔
      ∃ v : N.ComplexIdx → ℝ,
        N.kineticMap κ v = 0 ∧ ∀ c, 0 < v c := by
  constructor
  · intro hwr
    obtain ⟨v, hvpos, hvker⟩ :=
      (N.weaklyReversible_iff_exists_positive_kineticKernel κ).1 hwr
    exact ⟨v, hvker, hvpos⟩
  · exact N.weaklyReversible_of_exists_strictlyPositive_kineticKernel κ

end Network
end CRNT
