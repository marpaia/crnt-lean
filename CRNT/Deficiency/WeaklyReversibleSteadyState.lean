import CRNT.Deficiency.BorosActiveInwardEstimate

/-!
# Positive steady states for weakly reversible systems

The Boros--Birch inward estimate gives a direct existence proof on a positive compatibility
class. The empty-linkage case is immediate because then there are no reaction channels.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every weakly reversible mass-action system has a positive steady state in each positive
stoichiometric compatibility class. -/
theorem exists_positiveSteadyState_of_weaklyReversible
    (N : Network S) (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  classical
  by_cases hclasses : Nonempty (Quotient N.linkedSetoid)
  · letI : DecidableEq (Quotient N.linkedSetoid) := Classical.decEq _
    letI : Nonempty (Quotient N.linkedSetoid) := hclasses
    obtain ⟨xsel, hxcont, hxpos, hxstoich, _, hgraph⟩ :=
      N.exists_continuous_borosBirchGraph x₀ hx₀
    have hxclass : ∀ z, xsel z ∈ N.positiveCompatibilityClass x₀ := by
      intro z
      exact ⟨hxstoich z, hxpos z⟩
    obtain ⟨kmin, kmax, ε, r, hkminpos, hkmin, hkmaxpos, hkmax,
        hε, hεone, hr0, hrmono, hrnonneg, hεres, hrstep⟩ :=
      N.exists_borosActiveRadiusSchedule hwr κ
    have hinward := N.borosBirchKineticProjectionField_strict_inward
      hwr κ xsel hxpos hgraph kmin kmax ε r hkminpos hkmin hkmaxpos hkmax
      hε hεone hr0 hrmono hrnonneg hεres hrstep
    obtain ⟨y, hyclass, hyss⟩ :=
      N.exists_borosBirchSteadyState_of_activeInward κ xsel hxcont hxpos hxclass
        r hinward
    exact ⟨y, hyclass, hyss⟩
  · have hqempty : IsEmpty (Quotient N.linkedSetoid) := not_nonempty_iff.mp hclasses
    letI : IsEmpty (Quotient N.linkedSetoid) := hqempty
    letI : IsEmpty N.ComplexIdx := ⟨fun c => hqempty.false (N.classOf c)⟩
    letI : IsEmpty N.R := ⟨fun r => ‹IsEmpty N.ComplexIdx›.false (N.sourceIdx r)⟩
    refine ⟨x₀, ?_, ?_⟩
    · exact ⟨StoichCompatible.refl N x₀, hx₀⟩
    · intro s
      simp [massActionVectorField_apply]

end Network
end CRNT
