import CRNT.Deficiency.ConsistentWR
import CRNT.Deficiency.TerminalKernelDimension
import CRNT.Deficiency.CycleExactSequence
import CRNT.Combinatorics.DigraphExcess

/-!
# Positive graph circulations and weak reversibility

For a finite reaction graph, weak reversibility is equivalent to the existence of a
strictly positive circulation on *every reaction channel*:

`α_r > 0`,  `∂α = 0`.

This is stronger than ordinary CRNT consistency (`Sα=0`).  Deficiency measures exactly
the gap between those notions; at deficiency zero a positive stoichiometric steady flux
must already be a graph circulation.  Hence a deficiency-zero network is weakly
reversible exactly when it is consistent.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Strictly positive circulation on the directed reaction graph. -/
def IsPositiveGraphCirculation (N : Network S) (α : N.R → ℝ) : Prop :=
  (∀ r, 0 < α r) ∧ N.incidenceMap α = 0

/-- Weak reversibility produces a positive graph circulation. -/
theorem exists_positiveGraphCirculation_of_weaklyReversible
    (N : Network S) (hwr : N.WeaklyReversible) :
    ∃ α : N.R → ℝ, N.IsPositiveGraphCirculation α := by
  let κ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩
  obtain ⟨b, hbpos, hbker⟩ :=
    PositiveKernel.weaklyReversible_exists_positive_kernelVector N hwr κ
  let α : N.R → ℝ := fun r => κ.k r * b (N.sourceIdx r)
  refine ⟨α, ?_, ?_⟩
  · intro r
    exact mul_pos (κ.positive r) (hbpos _)
  · have hkin : N.kineticMap κ b = N.incidenceMap α := by
      funext c
      rfl
    rw [← hkin, hbker]

/-- A strictly positive circulation forces every reaction edge to lie on a directed
cycle, hence the network is weakly reversible. -/
theorem weaklyReversible_of_positiveGraphCirculation
    (N : Network S) {α : N.R → ℝ}
    (hα : N.IsPositiveGraphCirculation α) :
    N.WeaklyReversible := by
  classical
  intro r₀
  by_contra hret
  let U : Finset N.ComplexIdx :=
    Finset.univ.filter (fun c => N.Reaches (N.targetIdx r₀).val c.val)
  have hmem : ∀ c : N.ComplexIdx,
      c ∈ U ↔ N.Reaches (N.targetIdx r₀).val c.val := by
    intro c
    simp [U]
  have htgt : N.targetIdx r₀ ∈ U :=
    (hmem _).2 (Reaches.refl N _)
  have hsrc : N.sourceIdx r₀ ∉ U := by
    intro hs
    apply hret
    have hs' := (hmem _).1 hs
    simpa [targetIdx, sourceIdx] using hs'
  have hclosed : ∀ r : N.R, N.sourceIdx r ∈ U → N.targetIdx r ∈ U := by
    intro r hs
    rw [hmem] at hs ⊢
    exact hs.trans (by simpa [sourceIdx, targetIdx] using N.reaches_of_reaction r)
  have hvertex : ∀ c : N.ComplexIdx,
      excessVertex N.sourceIdx N.targetIdx α c = 0 := by
    intro c
    have hc := congrFun hα.2 c
    rw [incidenceMap_apply] at hc
    have hedge : ∀ e : N.R,
        (if N.sourceIdx e = c then α e else 0) -
            (if N.targetIdx e = c then α e else 0) =
          - (α e * ((if N.targetIdx e = c then 1 else 0) -
            (if N.sourceIdx e = c then 1 else 0))) := by
      intro e
      by_cases hs : N.sourceIdx e = c <;>
        by_cases ht : N.targetIdx e = c <;> simp [hs, ht]
    rw [excessVertex, ← Finset.sum_sub_distrib]
    calc
      (∑ e : N.R,
          ((if N.sourceIdx e = c then α e else 0) -
            (if N.targetIdx e = c then α e else 0)))
          = ∑ e : N.R, - (α e * ((if N.targetIdx e = c then 1 else 0) -
              (if N.sourceIdx e = c then 1 else 0))) := by
                exact Finset.sum_congr rfl (fun e _ => hedge e)
      _ = - (∑ e : N.R, α e * ((if N.targetIdx e = c then 1 else 0) -
              (if N.sourceIdx e = c then 1 else 0))) := by
                rw [Finset.sum_neg_distrib]
      _ = 0 := by rw [hc]; simp
  have hset0 : excessSet N.sourceIdx N.targetIdx α U = 0 := by
    rw [excessSet_eq_sum_excessVertex]
    simp [hvertex]
  have hout :
      (∑ r, if N.sourceIdx r ∈ U ∧ N.targetIdx r ∉ U then α r else 0) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [if_neg]
    rintro ⟨hs, ht⟩
    exact ht (hclosed r hs)
  have hinpos :
      0 < ∑ r, if N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U then α r else 0 := by
    refine Finset.sum_pos' (fun r _ => ?_) ⟨r₀, Finset.mem_univ r₀, ?_⟩
    · by_cases h : N.sourceIdx r ∉ U ∧ N.targetIdx r ∈ U
      · rw [if_pos h]
        exact (hα.1 r).le
      · rw [if_neg h]
    · rw [if_pos ⟨hsrc, htgt⟩]
      exact hα.1 r₀
  have hneg : excessSet N.sourceIdx N.targetIdx α U < 0 := by
    rw [excessSet, hout, zero_sub]
    exact neg_neg_of_pos hinpos
  rw [hset0] at hneg
  exact (lt_irrefl 0) hneg

/-- **Finite directed-graph circulation criterion for weak reversibility.** -/
theorem weaklyReversible_iff_exists_positiveGraphCirculation (N : Network S) :
    N.WeaklyReversible ↔ ∃ α : N.R → ℝ, N.IsPositiveGraphCirculation α := by
  constructor
  · exact N.exists_positiveGraphCirculation_of_weaklyReversible
  · rintro ⟨α, hα⟩
    exact N.weaklyReversible_of_positiveGraphCirculation hα

/-- Positive graph circulation implies CRNT consistency by applying the complex map. -/
theorem isConsistent_of_positiveGraphCirculation
    (N : Network S) {α : N.R → ℝ}
    (hα : N.IsPositiveGraphCirculation α) :
    N.IsConsistent := by
  refine ⟨α, hα.1, ?_⟩
  have hS : N.stoichMap α = 0 := by
    have hfac := congrArg (fun f => f α) N.complexMap_comp_incidenceMap
    simpa [hα.2] using hfac.symm
  funext s
  have hs := congrFun hS s
  simpa [stoichMap_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hs

end Network
end CRNT
