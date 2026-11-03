import CRNT.Deficiency.TerminalKernelBound
import CRNT.Deficiency.TerminalSLCKernel
import CRNT.Deficiency.SignedDrainage
import CRNT.Equilibria.TreeConstants

/-!
# Kinetic-kernel dimension equals the number of terminal strong linkage classes

For an arbitrary finite reaction graph with positive rate constants, the kernel of
the kinetic Laplacian has one independent mode for each terminal strongly connected
component and no others.  Thus

  dim ker A_k = t,

where `t` is the number of terminal strong linkage classes.  This is the general
finite directed-Laplacian theorem underlying both weak-reversibility criteria and the
deficiency-one algorithm.
-/

namespace CRNT
namespace Network

open scoped Classical BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Restriction of a complex vector to a strong linkage class. -/
noncomputable def restrictToStrongClass (N : Network S)
    (σ : Quotient N.stronglyLinkedSetoid) (v : N.ComplexIdx → ℝ) :
    N.ComplexIdx → ℝ :=
  fun c => if Quotient.mk N.stronglyLinkedSetoid c = σ then v c else 0

/-- Restricting a kinetic-kernel vector to a terminal strong linkage class preserves
the kinetic-kernel equation.  Signed drainage kills all transient incoming contributions,
while terminality prevents selected-class mass from leaving the class. -/
theorem restrictToStrongClass_kineticKernel (N : Network S) (κ : N.RateConstants)
    (σ : N.TerminalSLC) {v : N.ComplexIdx → ℝ}
    (hv : N.kineticMap κ v = 0) :
    N.kineticMap κ (N.restrictToStrongClass σ.val v) = 0 := by
  funext c
  change (∑ r : N.R, κ.k r * N.restrictToStrongClass σ.val v (N.sourceIdx r) *
    ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0))) = 0
  have hv_c : (∑ r : N.R, κ.k r * v (N.sourceIdx r) *
      ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0))) = 0 := by
    have h := congrFun hv c
    simpa only [N.kineticMap_apply, Pi.zero_apply] using h
  have htermRep : N.IsTerminalSLC σ.val.out.val := by
    have h := σ.property
    rw [← Quotient.out_eq σ.val, isTerminalSLClass_mk] at h
    exact h
  by_cases hcσ : Quotient.mk N.stronglyLinkedSetoid c = σ.val
  · calc
      (∑ r : N.R, κ.k r * N.restrictToStrongClass σ.val v (N.sourceIdx r) *
        ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0))) =
        ∑ r : N.R, κ.k r * v (N.sourceIdx r) *
        ((if N.targetIdx r = c then 1 else 0) - (if N.sourceIdx r = c then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro r _
          by_cases hsσ : Quotient.mk N.stronglyLinkedSetoid (N.sourceIdx r) = σ.val
          · simp [restrictToStrongClass, hsσ]
          · by_cases ht : N.targetIdx r = c
            · have hvsrc : v (N.sourceIdx r) = 0 := by
                apply N.kineticMap_eq_zero_of_not_terminal κ hv
                intro hsrcTerm
                have hst : N.StronglyLinked (N.sourceIdx r).1 (N.targetIdx r).1 :=
                  hsrcTerm r (StronglyLinked.refl N _)
                apply hsσ
                calc
                  Quotient.mk N.stronglyLinkedSetoid (N.sourceIdx r) =
                      Quotient.mk N.stronglyLinkedSetoid (N.targetIdx r) := Quotient.sound hst
                  _ = Quotient.mk N.stronglyLinkedSetoid c := by rw [ht]
                  _ = σ.val := hcσ
              simp [restrictToStrongClass, hsσ, hvsrc, ht]
            · by_cases hs : N.sourceIdx r = c
              · exfalso
                apply hsσ
                rw [hs, hcσ]
              · simp [restrictToStrongClass, hsσ, ht, hs]
      _ = 0 := hv_c
  · apply Finset.sum_eq_zero
    intro r _
    by_cases hsσ : Quotient.mk N.stronglyLinkedSetoid (N.sourceIdx r) = σ.val
    · have hsrcSL : N.StronglyLinked σ.val.out.val (N.sourceIdx r).1 := by
        have hq : Quotient.mk N.stronglyLinkedSetoid σ.val.out =
            Quotient.mk N.stronglyLinkedSetoid (N.sourceIdx r) :=
          (Quotient.out_eq σ.val).trans hsσ.symm
        exact Quotient.exact hq
      have htgtSL : N.StronglyLinked σ.val.out.val (N.targetIdx r).1 := htermRep r hsrcSL
      have htgtσ : Quotient.mk N.stronglyLinkedSetoid (N.targetIdx r) = σ.val := by
        calc
          Quotient.mk N.stronglyLinkedSetoid (N.targetIdx r) =
              Quotient.mk N.stronglyLinkedSetoid σ.val.out := Quotient.sound htgtSL.symm
          _ = σ.val := Quotient.out_eq _
      have htc : N.targetIdx r ≠ c := by
        intro heq
        apply hcσ
        rw [← heq, htgtσ]
      have hsc : N.sourceIdx r ≠ c := by
        intro heq
        apply hcσ
        rw [← heq, hsσ]
      simp [restrictToStrongClass, hsσ, htc, hsc]
    · simp [restrictToStrongClass, hsσ]

/-- A terminal-SLC kernel mode chosen canonically only up to existence. -/
noncomputable def terminalKernelMode (N : Network S) (κ : N.RateConstants)
    (σ : N.TerminalSLC) : N.ComplexIdx → ℝ :=
  Classical.choose
    (N.exists_pos_kernelVector_on_terminalSLC κ
      (by
        have h := σ.property
        rw [← Quotient.out_eq σ.val, isTerminalSLClass_mk] at h
        exact h))

/-- The chosen terminal mode is positive on its terminal strong linkage class. -/
theorem terminalKernelMode_pos (N : Network S) (κ : N.RateConstants)
    (σ : N.TerminalSLC) {c : N.ComplexIdx}
    (hc : N.StronglyLinked σ.val.out.val c.val) :
    0 < N.terminalKernelMode κ σ c := by
  exact (Classical.choose_spec
    (N.exists_pos_kernelVector_on_terminalSLC κ
      (by
        have h := σ.property
        rw [← Quotient.out_eq σ.val, isTerminalSLClass_mk] at h
        exact h))).1 c hc

/-- The chosen terminal mode vanishes off its terminal strong linkage class. -/
theorem terminalKernelMode_zero_off (N : Network S) (κ : N.RateConstants)
    (σ : N.TerminalSLC) {c : N.ComplexIdx}
    (hc : ¬ N.StronglyLinked σ.val.out.val c.val) :
    N.terminalKernelMode κ σ c = 0 := by
  exact (Classical.choose_spec
    (N.exists_pos_kernelVector_on_terminalSLC κ
      (by
        have h := σ.property
        rw [← Quotient.out_eq σ.val, isTerminalSLClass_mk] at h
        exact h))).2.1 c hc

/-- The chosen terminal mode lies in `ker A_k`. -/
theorem terminalKernelMode_mem_kernel (N : Network S) (κ : N.RateConstants)
    (σ : N.TerminalSLC) :
    N.kineticMap κ (N.terminalKernelMode κ σ) = 0 := by
  exact (Classical.choose_spec
    (N.exists_pos_kernelVector_on_terminalSLC κ
      (by
        have h := σ.property
        rw [← Quotient.out_eq σ.val, isTerminalSLClass_mk] at h
        exact h))).2.2

/-- Terminal modes are linearly independent because their supports are disjoint. -/
theorem terminalKernelModes_linearIndependent (N : Network S) (κ : N.RateConstants) :
    LinearIndependent ℝ (N.terminalKernelMode κ) := by
  rw [Fintype.linearIndependent_iff]
  intro a ha σ₀
  have hcoord := congrFun ha σ₀.val.out
  rw [Finset.sum_apply] at hcoord
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcoord
  rw [Finset.sum_eq_single σ₀] at hcoord
  · exact (mul_eq_zero.mp hcoord).resolve_right
      (N.terminalKernelMode_pos κ σ₀ (StronglyLinked.refl N _)).ne'
  · intro σ _ hσ
    have hoff : ¬ N.StronglyLinked σ.val.out.val σ₀.val.out.val := by
      intro hsl
      apply hσ
      apply Subtype.ext
      calc
        σ.val = Quotient.mk N.stronglyLinkedSetoid σ.val.out := (Quotient.out_eq σ.val).symm
        _ = Quotient.mk N.stronglyLinkedSetoid σ₀.val.out :=
          Quotient.sound (show N.stronglyLinkedSetoid.r σ.val.out σ₀.val.out from hsl)
        _ = σ₀.val := Quotient.out_eq _
    rw [N.terminalKernelMode_zero_off κ σ hoff, mul_zero]
  · simp

/-- A kinetic-kernel vector is the sum of its restrictions to terminal strong linkage
classes. Signed drainage makes all nonterminal coordinates vanish. -/
theorem sum_restrictToStrongClass_eq (N : Network S) (κ : N.RateConstants)
    {v : N.ComplexIdx → ℝ} (hv : N.kineticMap κ v = 0) :
    v = ∑ σ : N.TerminalSLC, N.restrictToStrongClass σ.val v := by
  funext c
  rw [Finset.sum_apply]
  by_cases hterm : N.IsTerminalSLC c.val
  · let σc : N.TerminalSLC :=
      ⟨Quotient.mk N.stronglyLinkedSetoid c, by simpa using hterm⟩
    rw [Finset.sum_eq_single σc]
    · simp [restrictToStrongClass, σc]
    · intro σ _ hne
      have hneq : Quotient.mk N.stronglyLinkedSetoid c ≠ σ.val := by
        intro heq
        apply hne
        apply Subtype.ext
        exact heq.symm
      simp [restrictToStrongClass, hneq]
    · simp
  · have hvc : v c = 0 := N.kineticMap_eq_zero_of_not_terminal κ hv hterm
    rw [hvc]
    symm
    apply Finset.sum_eq_zero
    intro σ _
    have hneq : Quotient.mk N.stronglyLinkedSetoid c ≠ σ.val := by
      intro heq
      apply hterm
      have hσterm : N.IsTerminalSLC σ.val.out.val := by
        have h := σ.property
        rw [← Quotient.out_eq σ.val, isTerminalSLClass_mk] at h
        exact h
      have hsl : N.StronglyLinked c.val σ.val.out.val := by
        have hq : Quotient.mk N.stronglyLinkedSetoid c =
            Quotient.mk N.stronglyLinkedSetoid σ.val.out :=
          heq.trans (Quotient.out_eq σ.val).symm
        exact Quotient.exact hq
      exact (N.isTerminalSLC_congr hsl).mpr hσterm
    simp [restrictToStrongClass, hneq]

/-- **Terminal-mode spanning theorem.** Every kinetic-kernel vector is a linear
combination of terminal strong-linkage-class modes.  The proof is the standard
condensation-DAG elimination: nonterminal SCC coordinates are uniquely determined to
vanish by solving blocks backward from sinks. -/
theorem kineticKernel_le_span_terminalModes (N : Network S) (κ : N.RateConstants) :
    LinearMap.ker (N.kineticMap κ) ≤
      Submodule.span ℝ (Set.range (N.terminalKernelMode κ)) := by
  intro v hvker
  have hv : N.kineticMap κ v = 0 := (LinearMap.mem_ker).1 hvker
  have huniq : ∀ σ : N.TerminalSLC, ∃ t : ℝ,
      N.restrictToStrongClass σ.val v = t • N.terminalKernelMode κ σ := by
    intro σ
    apply N.terminalSLC_kernel_unique κ
      (fun c hc => N.terminalKernelMode_pos κ σ hc)
      (fun c hc => N.terminalKernelMode_zero_off κ σ hc)
      (N.terminalKernelMode_mem_kernel κ σ)
    · intro c hc
      have hneq : Quotient.mk N.stronglyLinkedSetoid c ≠ σ.val := by
        intro heq
        apply hc
        have hq : Quotient.mk N.stronglyLinkedSetoid σ.val.out =
            Quotient.mk N.stronglyLinkedSetoid c :=
          (Quotient.out_eq σ.val).trans heq.symm
        exact Quotient.exact hq
      simp [restrictToStrongClass, hneq]
    · exact N.restrictToStrongClass_kineticKernel κ σ hv
  choose t ht using huniq
  have heq : v = ∑ σ : N.TerminalSLC, t σ • N.terminalKernelMode κ σ := by
    calc
      v = ∑ σ : N.TerminalSLC, N.restrictToStrongClass σ.val v :=
        N.sum_restrictToStrongClass_eq κ hv
      _ = ∑ σ : N.TerminalSLC, t σ • N.terminalKernelMode κ σ := by
        apply Finset.sum_congr rfl
        intro σ _
        exact ht σ
  rw [heq]
  apply Submodule.sum_mem
  intro σ _
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨σ, rfl⟩

/-- Terminal modes span exactly the kinetic kernel. -/
theorem span_terminalModes_eq_kineticKernel (N : Network S) (κ : N.RateConstants) :
    Submodule.span ℝ (Set.range (N.terminalKernelMode κ)) =
      LinearMap.ker (N.kineticMap κ) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨σ, rfl⟩
    exact (LinearMap.mem_ker).2 (N.terminalKernelMode_mem_kernel κ σ)
  · exact N.kineticKernel_le_span_terminalModes κ

/-- **Feinberg directed-Laplacian kernel formula:** `dim ker A_k = t`. -/
theorem finrank_ker_kineticMap_eq_numTerminalSLC (N : Network S)
    (κ : N.RateConstants) :
    Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) = N.numTerminalSLC := by
  rw [← N.span_terminalModes_eq_kineticKernel κ]
  rw [finrank_span_eq_card (N.terminalKernelModes_linearIndependent κ)]
  rfl

/-- The earlier lower bound is therefore always sharp. -/
theorem numTerminalSLC_eq_finrank_ker_kineticMap (N : Network S)
    (κ : N.RateConstants) :
    N.numTerminalSLC = Module.finrank ℝ (LinearMap.ker (N.kineticMap κ)) :=
  (N.finrank_ker_kineticMap_eq_numTerminalSLC κ).symm

/-- A strictly positive kinetic-kernel vector can exist only if every strong linkage
class is terminal, equivalently if the network is weakly reversible. -/
theorem weaklyReversible_of_exists_positive_kineticKernel
    (N : Network S) (κ : N.RateConstants)
    (hposker : ∃ v : N.ComplexIdx → ℝ,
      (∀ c, 0 < v c) ∧ N.kineticMap κ v = 0) :
    N.WeaklyReversible := by
  obtain ⟨v, hpos, hv⟩ := hposker
  intro r
  have hterm : N.IsTerminalSLC (N.sourceIdx r).val := by
    by_contra hnot
    have hz := N.kineticMap_eq_zero_of_not_terminal κ hv hnot
    exact (hpos (N.sourceIdx r)).ne' hz
  have hsl : N.StronglyLinked (N.sourceIdx r).val (N.targetIdx r).val :=
    hterm r (StronglyLinked.refl N _)
  exact hsl.2

/-- Weak reversibility is equivalent to existence of a strictly positive kinetic-kernel
vector for any fixed positive rate vector. -/
theorem weaklyReversible_iff_exists_positive_kineticKernel
    (N : Network S) (κ : N.RateConstants) :
    N.WeaklyReversible ↔
      ∃ v : N.ComplexIdx → ℝ,
        (∀ c, 0 < v c) ∧ N.kineticMap κ v = 0 := by
  constructor
  · intro hwr
    exact ⟨N.treeConstantVector κ,
      (N.treeConstantVector_positive_kernel κ hwr).1,
      (N.treeConstantVector_positive_kernel κ hwr).2⟩
  · exact N.weaklyReversible_of_exists_positive_kineticKernel κ

end Network
end CRNT
