import CRNT.Dynamics.StrictInflow
import CRNT.Dynamics.SiphonConservation
import CRNT.Equilibria.SteadyState
import CRNT.Equilibria.CompatibilityClass
import CRNT.Equilibria.GeneralizedComplexBalanceToric

/-!
# Boundary steady states and siphons

The zero set of any nonnegative mass-action steady state is a siphon.  If that boundary
steady state lies in the stoichiometric compatibility class of a positive point, its zero
set is in fact a critical siphon: any positive conservation law supported on the zero set
would have positive value at the interior point and zero value at the boundary point,
contradicting conservation along stoichiometric classes.

This is the equilibrium-level version of the more general boundary-omega-limit theorem and
requires no semiflow construction.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Zero-species set of a concentration. -/
noncomputable def zeroSpecies (x : Concentration S) : Finset S :=
  Finset.univ.filter fun s => x s = 0

@[simp] theorem mem_zeroSpecies (x : Concentration S) (s : S) :
    s ∈ zeroSpecies x ↔ x s = 0 := by
  simp [zeroSpecies]

/-- The zero set of a nonnegative steady state is a siphon. -/
theorem isSiphon_zeroSpecies_of_steadyState
    (N : Network S) (κ : N.RateConstants)
    {x : Concentration S} (hx : x.Nonnegative)
    (hss : N.IsMassActionSteadyState κ x) :
    N.IsSiphon (zeroSpecies x) := by
  by_contra hnot
  obtain ⟨s, hs, hpos⟩ :=
    N.massActionVectorField_pos_of_not_isSiphon κ hx
      (fun t => mem_zeroSpecies x t) hnot
  have hz := hss s
  rw [hz] at hpos
  exact lt_irrefl 0 hpos

/-- Conservation-law values agree on one stoichiometric compatibility class. -/
theorem conservation_pairing_eq_of_sameStoichClass
    (N : Network S) {x y : Concentration S} (hxy : N.SameStoichClass x y)
    {v : S → ℝ} (hv : v ∈ orthSum N.stoichSubspace) :
    (∑ s : S, v s * x s) = ∑ s : S, v s * y s := by
  have horth := (mem_orthSum.mp hv) (x - y) hxy
  have hzero : ∑ s : S, v s * (x s - y s) = 0 := by
    simpa [Pi.sub_apply] using horth
  simp only [mul_sub] at hzero
  rw [Finset.sum_sub_distrib] at hzero
  linarith

/-- A nonnegative conservation law supported on the zero set has zero value at the
boundary point. -/
theorem conservation_pairing_zero_on_zeroSpecies
    {x : Concentration S} {v : S → ℝ}
    (hsupp : ∀ s, 0 < v s ↔ s ∈ zeroSpecies x)
    (hnn : ∀ s, 0 ≤ v s) :
    (∑ s : S, v s * x s) = 0 := by
  apply Finset.sum_eq_zero
  intro s _
  by_cases hs : s ∈ zeroSpecies x
  · rw [(mem_zeroSpecies x s).mp hs, mul_zero]
  · have hv0 : v s = 0 := by
      have : ¬ 0 < v s := fun hp => hs ((hsupp s).mp hp)
      exact le_antisymm (le_of_not_gt this) (hnn s)
    rw [hv0, zero_mul]

/-- A positive concentration gives strictly positive value to every nonzero nonnegative
conservation law. -/
theorem conservation_pairing_pos_at_positive
    {x : Concentration S} (hx : x.Positive) {v : S → ℝ}
    (hnn : ∀ s, 0 ≤ v s) (hv0 : v ≠ 0) :
    0 < ∑ s : S, v s * x s := by
  obtain ⟨s, hs⟩ : ∃ s, v s ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv0 (funext h)
  have hvpos : 0 < v s := lt_of_le_of_ne (hnn s) (Ne.symm hs)
  apply Finset.sum_pos'
  · intro t _
    exact mul_nonneg (hnn t) (hx t).le
  · exact ⟨s, Finset.mem_univ s, mul_pos hvpos (hx s)⟩

/-- **Boundary steady state in a positive class ⇒ critical siphon.** -/
theorem isCriticalSiphon_zeroSpecies_of_boundarySteadyState
    (N : Network S) (κ : N.RateConstants)
    {x x₀ : Concentration S}
    (hx : x.Nonnegative) (hboundary : (zeroSpecies x).Nonempty)
    (hss : N.IsMassActionSteadyState κ x)
    (hx₀ : x₀.Positive) (hclass : N.SameStoichClass x x₀) :
    N.IsCriticalSiphon (zeroSpecies x) := by
  refine ⟨hboundary, N.isSiphon_zeroSpecies_of_steadyState κ hx hss, ?_⟩
  rintro ⟨v, hvnn, hvSupp, hvCons⟩
  have hvorth := (N.conservationLaw_iff_mem_orthSum v).1 hvCons
  have heq := N.conservation_pairing_eq_of_sameStoichClass hclass hvorth
  have hxzero := conservation_pairing_zero_on_zeroSpecies hvSupp hvnn
  have hv0 : v ≠ 0 := by
    intro hz
    obtain ⟨s, hs⟩ := hboundary
    have hp : 0 < v s := (hvSupp s).2 hs
    rw [hz] at hp
    simp at hp
  have hx₀pos := conservation_pairing_pos_at_positive hx₀ hvnn hv0
  rw [hxzero] at heq
  linarith

/-- No-critical-siphon networks have no boundary steady state in any positive class. -/
theorem no_boundarySteadyState_in_positiveClass_of_noCriticalSiphon
    (N : Network S) (κ : N.RateConstants)
    (hnc : N.HasNoCriticalSiphon)
    {x x₀ : Concentration S}
    (hx : x.Nonnegative) (hx₀ : x₀.Positive)
    (hss : N.IsMassActionSteadyState κ x)
    (hclass : N.SameStoichClass x x₀) :
    x.Positive := by
  intro s
  have hxnonneg := hx s
  by_contra hnot
  have hxzero : x s = 0 := le_antisymm (le_of_not_gt hnot) hxnonneg
  have hne : (zeroSpecies x).Nonempty := ⟨s, (mem_zeroSpecies x s).2 hxzero⟩
  exact hnc (zeroSpecies x)
    (N.isCriticalSiphon_zeroSpecies_of_boundarySteadyState κ hx hne hss hx₀ hclass)

/-- In particular, if a closed positive stoichiometric class has no critical siphon, every
nonnegative equilibrium in that class is interior. -/
theorem steadyState_nonnegative_iff_positive_in_class_of_noCriticalSiphon
    (N : Network S) (κ : N.RateConstants)
    (hnc : N.HasNoCriticalSiphon) {x₀ : Concentration S} (hx₀ : x₀.Positive)
    {x : Concentration S} (hclass : N.SameStoichClass x x₀)
    (hss : N.IsMassActionSteadyState κ x) :
    x.Nonnegative ↔ x.Positive := by
  constructor
  · intro hx
    exact N.no_boundarySteadyState_in_positiveClass_of_noCriticalSiphon
      κ hnc hx hx₀ hss hclass
  · intro hx s
    exact (hx s).le

end Network
end CRNT
