import CRNT.Dynamics.SiphonAutocatalysis

set_option backward.isDefEq.respectTransparency false

/-!
# The repository's minimal-critical-siphon dichotomy is false as stated

`IsCriticalSiphon P` (`CRNT/Dynamics/Siphon.lean`) forbids a nonnegative conservation law whose
support is *exactly* `P`.  Deshpande–Gopalkrishnan (2014, Definition 3.1) call `T` critical when
no positive conservation law has support *contained in* `T`.  With the exact-support definition,
their Theorem 5.3(2) fails:

`A → A + B`, `A + B → A`.

* `{A}` carries the conservation law `x_A`, so it is not critical; `{B}` is not a siphon.
* `{A, B}` is a siphon, and every conservation law vanishes on `B`, so no law has support exactly
  `{A, B}`: it is a minimal critical siphon in the repository's sense.
* `x_A` is conserved, so no flux changes `A`: `{A, B}` is neither flux-drainable nor
  flux-self-replicable.

Hence `¬ MinimalCriticalSiphonFluxDichotomy` and `¬ MinimalCriticalSiphonDichotomy` for this
network.  In the paper's sense `{A, B}` is not critical (the law `x_A` has support inside it).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.CriticalDichotomyCE

open CRNT CRNT.Network

/-- Species `A = 0`, `B = 1`. -/
abbrev Species := Fin 2

def cA : Complex Species := ![1, 0]
def cAB : Complex Species := ![1, 1]

/-- `r 0 : A → A + B`, `r 1 : A + B → A`. -/
def rxn : Fin 2 → Reaction Species
  | 0 => { source := cA, target := cAB }
  | 1 => { source := cAB, target := cA }

def N : Network Species :=
  { R := Fin 2, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- No reaction changes `A`. -/
theorem reactionVector_A (r : N.R) : N.reactionVector r 0 = 0 := by
  fin_cases r <;> simp [reactionVector_apply, N, rxn, cA, cAB]

theorem reactionVector_B0 : N.reactionVector (0 : Fin 2) 1 = 1 := by
  simp [reactionVector_apply, N, rxn, cA, cAB]

/-- `{A, B}` is a minimal critical siphon in the repository's sense. -/
theorem isMinimalCriticalSiphon_univ : N.IsMinimalCriticalSiphon Finset.univ := by
  refine ⟨⟨Finset.univ_nonempty, ?_, ?_⟩, ?_⟩
  · intro r _
    refine ⟨0, Finset.mem_univ _, ?_⟩
    fin_cases r <;> simp [IsReactant, N, rxn, cA, cAB]
  · rintro ⟨v, -, hsupp, hcons⟩
    have h1 : 0 < v 1 := (hsupp 1).mpr (Finset.mem_univ _)
    have h := hcons (0 : Fin 2)
    rw [Fin.sum_univ_two, reactionVector_A, reactionVector_B0] at h
    linarith
  · intro Q _ hQne hQnonempty hcrit
    by_cases h0 : (0 : Fin 2) ∈ Q <;> by_cases h1 : (1 : Fin 2) ∈ Q
    · apply hQne
      ext s; fin_cases s <;> simp [h0, h1]
    · -- `{A}` carries the conservation law `x_A`
      apply hcrit.2.2
      refine ⟨![1, 0], fun s => by fin_cases s <;> simp, fun s => ?_, fun r => ?_⟩
      · fin_cases s <;> simp [h0, h1]
      · rw [Fin.sum_univ_two, reactionVector_A]; simp
    · -- `{B}` is not a siphon: `A → A + B` makes `B` from `A`
      obtain ⟨s, hs, hreact⟩ := hcrit.2.1 (0 : Fin 2) ⟨1, h1, by
        simp [IsProduct, N, rxn, cAB]⟩
      fin_cases s
      · exact h0 hs
      · simp [IsReactant, N, rxn, cA] at hreact
    · obtain ⟨s, hs⟩ := hQnonempty
      fin_cases s
      · exact h0 hs
      · exact h1 hs

/-- `{A, B}` is neither flux-drainable nor flux-self-replicable. -/
theorem not_fluxDichotomy_univ :
    ¬ (N.IsFluxDrainable Finset.univ ∨ N.IsFluxSelfReplicable Finset.univ) := by
  have hz : ∀ v : N.R → ℝ, N.fluxNetChange v 0 = 0 := fun v => by
    unfold fluxNetChange
    exact Finset.sum_eq_zero fun r _ => by rw [reactionVector_A, mul_zero]
  rintro (⟨v, -, hv⟩ | ⟨v, -, hv⟩)
  · have := hv 0 (Finset.mem_univ _); rw [hz] at this; exact lt_irrefl _ this
  · have := hv 0 (Finset.mem_univ _); rw [hz] at this; exact lt_irrefl _ this

/-- The flux form of the dichotomy fails for this network. -/
theorem not_minimalCriticalSiphonFluxDichotomy : ¬ N.MinimalCriticalSiphonFluxDichotomy :=
  fun h => not_fluxDichotomy_univ (h _ isMinimalCriticalSiphon_univ)

end CRNT.Examples.CriticalDichotomyCE
