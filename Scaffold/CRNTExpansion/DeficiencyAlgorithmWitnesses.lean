import Scaffold.CRNTExpansion.DeficiencyAlgorithmCorrectness

/-!
# Typed witnesses and proof kernels for the Deficiency One Algorithm

`DOAAffirmsCapacity` is intentionally a compact nested existential.  For the remaining correctness
proof it is more convenient to expose that data as a structure and isolate the genuinely hard
rate-realization step.

The key new target is `DOARateRealizationKernel`: every affirmative signature must be realizable by
one positive rate vector for which two distinct positive, stoichiometrically compatible
concentrations are both steady states.  Once that kernel is proved, verdict -> capacity is formal
assembly.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Structured form of an affirmative Deficiency One Algorithm signature. -/
structure DOAAffirmationWitness (N : Network S) where
  g : N.ComplexIdx → ℝ
  confluence : N.IsConfluenceVector g
  g_ne_zero : g ≠ 0
  shelf : N.ShelfPartition
  mu : S → ℝ
  mu_ne_zero : mu ≠ 0
  signCompatible : N.SignCompatibleWithStoich mu
  imposes : shelf.imposes g mu

/-- A structured witness is exactly the existing algorithmic verdict. -/
theorem doaAffirmsCapacity_iff_nonempty_witness (N : Network S) :
    N.DOAAffirmsCapacity ↔ Nonempty (N.DOAAffirmationWitness) := by
  constructor
  · rintro ⟨g, hg, hg0, sp, μ, hμ0, hsign, himposes⟩
    exact ⟨⟨g, hg, hg0, sp, μ, hμ0, hsign, himposes⟩⟩
  · rintro ⟨W⟩
    exact ⟨W.g, W.confluence, W.g_ne_zero, W.shelf, W.mu,
      W.mu_ne_zero, W.signCompatible, W.imposes⟩

/-- The genuinely hard soundness kernel: realize every affirmative DOA signature by one rate vector
with two distinct positive compatible steady states. -/
def DOARateRealizationKernel (N : Network S) : Prop :=
  ∀ W : N.DOAAffirmationWitness,
    ∃ (κ : N.RateConstants) (x y : Concentration S),
      x.Positive ∧ y.Positive ∧ N.StoichCompatible x y ∧ x ≠ y ∧
        N.IsMassActionSteadyState κ x ∧ N.IsMassActionSteadyState κ y

/-- The rate-realization kernel immediately proves the soundness direction of the DOA. -/
theorem doaVerdictToCapacity_of_rateRealizationKernel
    (N : Network S) (K : N.DOARateRealizationKernel) : N.DOAVerdictToCapacity := by
  intro _hregular _hdef hverd
  obtain ⟨W⟩ := (N.doaAffirmsCapacity_iff_nonempty_witness).mp hverd
  obtain ⟨κ, x, y, hx, hy, hxy, hne, hssx, hssy⟩ := K W
  refine ⟨κ, x, x, y, ?_, ?_, hssx, hssy, hne⟩
  · exact ⟨Network.StoichCompatible.refl N x, hx⟩
  · exact ⟨hxy, hy⟩

/-- Completeness can likewise be isolated as construction of a structured affirmative witness from
an actual multistationarity-capacity witness. -/
def DOAWitnessExtractionKernel (N : Network S) : Prop :=
  N.HasMultistationarityCapacity → Nonempty N.DOAAffirmationWitness

/-- Witness extraction proves the capacity -> verdict direction. -/
theorem doaCapacityToVerdict_of_witnessExtractionKernel
    (N : Network S) (K : N.DOAWitnessExtractionKernel) : N.DOACapacityToVerdict := by
  intro _hregular _hdef hcap
  exact (N.doaAffirmsCapacity_iff_nonempty_witness).mpr (K hcap)

/-- With the two independent kernels established, the full headline DOA statement follows. -/
theorem deficiencyOneAlgorithmStatement_of_witnessKernels
    (N : Network S) (Kcomplete : N.DOAWitnessExtractionKernel)
    (Ksound : N.DOARateRealizationKernel) : N.DeficiencyOneAlgorithmStatement := by
  apply (N.deficiencyOneAlgorithmStatement_iff_directionalKernels).2
  exact ⟨N.doaCapacityToVerdict_of_witnessExtractionKernel Kcomplete,
    N.doaVerdictToCapacity_of_rateRealizationKernel Ksound⟩

end Network
end CRNT
