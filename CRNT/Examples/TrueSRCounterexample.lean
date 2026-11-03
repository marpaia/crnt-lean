import CRNT.Multistationarity.TrueChemistrySRCriterion

namespace CRNT.Network

private abbrev flowN : Network (Fin 2) where
  R := Fin 2
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun r =>
    if r = 0 then
      { source := Complex.zero
        target := fun s => if s = 0 then 1 else 2 }
    else
      { source := Complex.zero
        target := fun s => if s = 0 then 2 else 1 }


@[simp] private theorem flowN_r0_t0 : (flowN.reaction (0 : Fin 2)).target 0 = 1 := by rfl
@[simp] private theorem flowN_r0_t1 : (flowN.reaction (0 : Fin 2)).target 1 = 2 := by rfl
@[simp] private theorem flowN_r1_t0 : (flowN.reaction (1 : Fin 2)).target 0 = 2 := by rfl
@[simp] private theorem flowN_r1_t1 : (flowN.reaction (1 : Fin 2)).target 1 = 1 := by rfl

@[simp] private theorem flowN_fo_r0_t0 :
    (flowN.fullyOpen.reaction (Sum.inl (0 : Fin 2))).target 0 = 1 := by rfl
@[simp] private theorem flowN_fo_r0_t1 :
    (flowN.fullyOpen.reaction (Sum.inl (0 : Fin 2))).target 1 = 2 := by rfl
@[simp] private theorem flowN_fo_r1_t0 :
    (flowN.fullyOpen.reaction (Sum.inl (1 : Fin 2))).target 0 = 2 := by rfl
@[simp] private theorem flowN_fo_r1_t1 :
    (flowN.fullyOpen.reaction (Sum.inl (1 : Fin 2))).target 1 = 1 := by rfl
@[simp] private theorem flowN_fo_out0_s0 :
    (flowN.fullyOpen.reaction (Sum.inr (Sum.inr (0 : Fin 2)))).source 0 = 1 := by rfl
@[simp] private theorem flowN_fo_out1_s1 :
    (flowN.fullyOpen.reaction (Sum.inr (Sum.inr (1 : Fin 2)))).source 1 = 1 := by rfl
@[simp] private theorem flowN_fo_original_source (r s : Fin 2) :
    (flowN.fullyOpen.reaction
      (Sum.inl r : Fin 2 ⊕ (Fin 2 ⊕ Fin 2))).source s = 0 := by
  fin_cases r <;> rfl
@[simp] private theorem flowN_fo_out_target (r s : Fin 2) :
    (flowN.fullyOpen.reaction
      (Sum.inr (Sum.inr r) : Fin 2 ⊕ (Fin 2 ⊕ Fin 2))).target s = 0 := by
  fin_cases r <;> fin_cases s <;> rfl
@[simp] private theorem flowN_fo_out0_s1 :
    (flowN.fullyOpen.reaction
      (Sum.inr (Sum.inr (0 : Fin 2)) : Fin 2 ⊕ (Fin 2 ⊕ Fin 2))).source 1 = 0 := by rfl
@[simp] private theorem flowN_fo_out1_s0 :
    (flowN.fullyOpen.reaction
      (Sum.inr (Sum.inr (1 : Fin 2)) : Fin 2 ⊕ (Fin 2 ⊕ Fin 2))).source 0 = 0 := by rfl

private def sig : Fin 2 → ℝ := fun s => if s = 0 then -1 else 1

private def a : flowN.fullyOpen.R → ℝ
  | Sum.inl r => if (flowN.reaction r).target 0 = 1 then 1 else -1
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr s) => if s = 0 then -1 else 1

private theorem flowN_all_flow (r : flowN.R) : flowN.IsFlowChannel r := by
  left
  fin_cases r <;> rfl

private theorem flowN_no_internal (ρ : flowN.TrueReaction) :
    ¬ TrueReaction.Internal flowN ρ := by
  induction ρ using Quotient.inductionOn with
  | _ r =>
      exact fun h => h (flowN_all_flow r)

private theorem flowN_no_edge (e : flowN.TrueSREdge) : False :=
  flowN_no_internal e.reaction e.internal

private theorem flowN_no_cycle {n : ℕ} (C : flowN.TrueSRCycle n) : False := by
  have hn : 0 < n := lt_of_lt_of_le (by omega) C.nontrivial
  exact flowN_no_edge (C.leftEdge ⟨0, hn⟩)

private theorem flowN_trueSR : flowN.TrueSRStrongCriterion := by
  constructor
  · intro n C _hEven
    exact (flowN_no_cycle C).elim
  · intro m n C D _hC _hD
    exact (flowN_no_cycle C).elim

private theorem flowN_witness : flowN.fullyOpen.StrongConcordanceWitness a sig := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply flowN.fullyOpen.inKerL_of_apply
    intro s
    change (∑ q : flowN.R ⊕ (Fin 2 ⊕ Fin 2),
      a q * flowN.fullyOpen.reactionVector q s) = 0
    rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
    simp only [Fin.sum_univ_two]
    fin_cases s
    · norm_num [a, Network.reactionVector, Network.fullyOpen, flowN,
        inflowReaction, outflowReaction, singletonComplex, Complex.zero]
      rw [flowN_fo_r0_t0, flowN_fo_r1_t0, flowN_fo_out0_s0]
      norm_num [flowN, Network.fullyOpen, inflowReaction, outflowReaction,
        singletonComplex, Complex.zero]
    · norm_num [a, Network.reactionVector, Network.fullyOpen, flowN,
        inflowReaction, outflowReaction, singletonComplex, Complex.zero]
      rw [flowN_fo_r0_t1, flowN_fo_r1_t1, flowN_fo_out1_s1]
      norm_num [flowN, Network.fullyOpen, inflowReaction, outflowReaction,
        singletonComplex, Complex.zero]
  · rw [flowN.stoichSubspace_fullyOpen_eq_top]
    exact Submodule.mem_top
  · intro h
    have h0 := congrFun h 0
    norm_num [sig] at h0
  · intro q hq
    rcases q with r | q
    · fin_cases r
      · refine ⟨0, ?_⟩
        norm_num [Promotes, reactionDirectionSign, sig, flowN, fullyOpen_reaction_inl]
      · norm_num [a] at hq
    · rcases q with s | s
      · norm_num [a] at hq
      · fin_cases s
        · norm_num [a] at hq
        · refine ⟨1, ?_⟩
          norm_num [Promotes, reactionDirectionSign, sig, flowN,
            fullyOpen_reaction_outflow, outflowReaction, singletonComplex_apply]
  · intro q hq
    rcases q with r | q
    · fin_cases r
      · norm_num [a] at hq
      · refine ⟨1, ?_⟩
        norm_num [Opposes, reactionDirectionSign, sig, flowN, fullyOpen_reaction_inl]
    · rcases q with s | s
      · norm_num [a] at hq
      · fin_cases s
        · refine ⟨0, ?_⟩
          norm_num [Opposes, reactionDirectionSign, sig, flowN,
            fullyOpen_reaction_outflow, outflowReaction, singletonComplex_apply]
        · norm_num [a] at hq
  · intro q hq
    rcases q with r | q
    · fin_cases r <;> norm_num [a] at hq
    · rcases q with s | s
      · left
        intro t hsrc
        fin_cases s <;> fin_cases t <;>
          norm_num [fullyOpen_reaction_inflow, inflowReaction, singletonComplex_apply] at hsrc
      · fin_cases s <;> norm_num [a] at hq


private theorem flowN_not_zeroComplexReactionsAreFlows :
    ¬ flowN.ZeroComplexReactionsAreFlows := by
  intro h
  have hr := h (0 : Fin 2) (Or.inl rfl)
  rcases hr with ⟨s, hs⟩ | ⟨s, hs⟩
  · fin_cases s
    · have ht := congrArg (fun R : Reaction (Fin 2) => R.target 1) hs
      norm_num [flowN, inflowReaction, singletonComplex_apply] at ht
    · have ht := congrArg (fun R : Reaction (Fin 2) => R.target 0) hs
      norm_num [flowN, inflowReaction, singletonComplex_apply] at ht
  · have ht := congrArg (fun R : Reaction (Fin 2) => R.target 0) hs
    norm_num [flowN, outflowReaction, singletonComplex_apply] at ht

private theorem flowN_fullyOpen_not_stronglyConcordant :
    ¬ flowN.fullyOpen.StronglyConcordant := by
  intro h
  exact h ⟨a, sig, flowN_witness⟩

/-- The current true-SR criterion theorem is false without excluding pre-existing flow channels. -/
theorem trueSRCriterion_counterexample :
    flowN.TrueSRStrongCriterion ∧ ¬ flowN.fullyOpen.StronglyConcordant ∧
      ¬ flowN.ZeroComplexReactionsAreFlows :=
  ⟨flowN_trueSR, flowN_fullyOpen_not_stronglyConcordant,
    flowN_not_zeroComplexReactionsAreFlows⟩

end CRNT.Network
