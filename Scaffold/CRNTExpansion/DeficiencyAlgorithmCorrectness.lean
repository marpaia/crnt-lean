import CRNT.Deficiency.DeficiencyOneAlgorithm
import CRNT.Deficiency.AdvancedDeficiencyAlgorithm
import CRNT.Deficiency.DOAForward
import CRNT.Deficiency.DOACapacityConstruction

/-!
# Correctness interfaces for the deficiency algorithms

The existing library records the headline Deficiency One Algorithm (DOA) and Advanced Deficiency
Algorithm (ADA) correctness statements as named propositions.  This scaffold splits each
biconditional into two independently provable mathematical kernels.  That is important for proof
engineering: the two directions use quite different mathematics and should not remain hidden behind
one monolithic target.

For the DOA, the existing source already contains the first substantial ingredients on both sides:

* `exists_signCompatible_of_hasMultistationarityCapacity` starts capacity -> verdict by extracting
  the logarithmic sign vector from two steady states;
* `exists_compatible_pair_sameSign_logRatio` starts verdict -> capacity by constructing a positive
  compatible pair from a nonzero stoichiometric sign direction.

What remains is the genuine Feinberg shelf/confluence analysis and the construction of rate
constants making the candidate pair stationary.

The ADA definitions currently in `AdvancedDeficiencyAlgorithm` are explicitly only a partial
surrogate for the published algorithm.  The separate `AdvancedDeficiencyKernel` scaffold records
its correct kernel-coordinate starting point before a correctness proof is attempted.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Completeness direction of the Deficiency One Algorithm: actual multistationarity capacity
produces an affirmative algorithmic signature. -/
def DOACapacityToVerdict (N : Network S) : Prop :=
  N.RegularNetwork -> N.DeficiencyOne ->
    N.HasMultistationarityCapacity -> N.DOAAffirmsCapacity

/-- Soundness direction of the Deficiency One Algorithm: an affirmative signature can be realized
by positive rate constants and two positive steady states in one compatibility class. -/
def DOAVerdictToCapacity (N : Network S) : Prop :=
  N.RegularNetwork -> N.DeficiencyOne ->
    N.DOAAffirmsCapacity -> N.HasMultistationarityCapacity

/-- The entry data forced by genuine multistationarity: a nonzero logarithmic sign direction
compatible with the stoichiometric subspace.  This is deliberately weaker than a full shelf
signature and isolates the already-formalized first half of the DOA completeness proof. -/
def DOALogSignatureCore (N : Network S) : Prop :=
  ∃ μ : S -> ℝ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ

/-- Genuine multistationarity capacity always produces the logarithmic sign core. -/
theorem doaLogSignatureCore_of_capacity (N : Network S)
    (hcap : N.HasMultistationarityCapacity) : N.DOALogSignatureCore :=
  N.exists_signCompatible_of_hasMultistationarityCapacity hcap

/-- An affirmative DOA signature already determines two distinct positive concentrations in one
stoichiometric compatibility class whose log-ratio has the signature's sign pattern.  The only
missing step toward actual capacity is therefore the rate-constant/steady-state realization of this
candidate pair. -/
theorem doaAffirmsCapacity_exists_candidatePair (N : Network S)
    (h : N.DOAAffirmsCapacity) :
    ∃ (μ : S -> ℝ) (x y : Concentration S),
      μ ≠ 0 ∧ N.SignCompatibleWithStoich μ ∧
      x.Positive ∧ y.Positive ∧ N.StoichCompatible x y ∧ x ≠ y ∧
      SameSign μ (fun s => Real.log (y s) - Real.log (x s)) := by
  obtain ⟨g, hg, hg0, sp, μ, hμ0, ⟨w, hwmem, hsame⟩, himposes⟩ := h
  have hw0 : w ≠ 0 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hμ0
    simp only [Pi.zero_apply] at hi
    have hwi : w i ≠ 0 := by
      rcases lt_or_gt_of_ne hi with hlt | hgt
      · exact ne_of_lt ((hsame i).2.mpr hlt)
      · exact ne_of_gt ((hsame i).1.mpr hgt)
    intro hw
    rw [hw] at hwi
    exact hwi rfl
  obtain ⟨x, y, hx, hy, hcompat, hxy, hlog⟩ :=
    N.exists_compatible_pair_sameSign_logRatio hwmem hw0
  have hμw : SameSign μ w := sameSign_symm hsame
  have hμlog : SameSign μ (fun s => Real.log (y s) - Real.log (x s)) := by
    intro s
    exact ⟨(hμw s).1.trans (hlog s).1, (hμw s).2.trans (hlog s).2⟩
  exact ⟨μ, x, y, hμ0, ⟨w, hwmem, hsame⟩, hx, hy, hcompat, hxy, hμlog⟩

/-- The existing headline DOA statement is exactly the conjunction of its two directional kernels. -/
theorem deficiencyOneAlgorithmStatement_iff_directionalKernels (N : Network S) :
    N.DeficiencyOneAlgorithmStatement <->
      (N.DOACapacityToVerdict /\ N.DOAVerdictToCapacity) := by
  unfold DeficiencyOneAlgorithmStatement DOACapacityToVerdict DOAVerdictToCapacity
  constructor
  · intro h
    constructor
    · intro hreg hdef hcap
      exact (h hreg hdef).mp hcap
    · intro hreg hdef hverdict
      exact (h hreg hdef).mpr hverdict
  · rintro ⟨hforward, hbackward⟩ hreg hdef
    exact ⟨hforward hreg hdef, hbackward hreg hdef⟩

/-- Capacity-to-verdict kernel for the Advanced Deficiency Algorithm.  This name is deliberately
independent of the current simplified `ADAData`: the final theorem should be retargeted to the
faithful ADA signature once the orientation/kernel/coplanarity layer is complete. -/
def ADACapacityToVerdict (N : Network S) : Prop :=
  N.RegularNetwork -> N.HasMultistationarityCapacity -> N.ADAAffirmsCapacity

/-- Verdict-to-capacity kernel for the Advanced Deficiency Algorithm. -/
def ADAVerdictToCapacity (N : Network S) : Prop :=
  N.RegularNetwork -> N.ADAAffirmsCapacity -> N.HasMultistationarityCapacity

/-- The existing headline ADA proposition decomposes into the two directional kernels. -/
theorem advancedDeficiencyAlgorithmStatement_iff_directionalKernels (N : Network S) :
    N.AdvancedDeficiencyAlgorithmStatement <->
      (N.ADACapacityToVerdict /\ N.ADAVerdictToCapacity) := by
  unfold AdvancedDeficiencyAlgorithmStatement ADACapacityToVerdict ADAVerdictToCapacity
  constructor
  · intro h
    constructor
    · intro hreg hcap
      exact (h hreg).mp hcap
    · intro hreg hverdict
      exact (h hreg).mpr hverdict
  · rintro ⟨hforward, hbackward⟩ hreg
    exact ⟨hforward hreg, hbackward hreg⟩

end Network
end CRNT
