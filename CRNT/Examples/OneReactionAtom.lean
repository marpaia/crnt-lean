import CRNT.Multistationarity.OneSpeciesNecessity

set_option backward.isDefEq.respectTransparency false

/-!
# One-species one-reaction fully open networks (Joshi 2013)

The fully open network `0 ⇌ X` with the single non-flow reaction `a X → b X` admits rate
constants with two distinct positive steady states (and a not identically zero steady-state
polynomial) iff `1 < a < b`: the reaction must be autocatalytic and of order at least two
(Joshi 2013, the one-species case of the classification of one-reaction networks).  This follows
from the Joshi–Shiu arrow-pattern criterion `oneSpecies_nondegenerate_multistationary_iff`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.OneReactionAtom

open CRNT CRNT.Network

/-- The complex `n X`. -/
def cpx (n : ℕ) : Complex Unit := fun _ => n

/-- `r 0 : 0 → X`, `r 1 : X → 0`, `r 2 : a X → b X`. -/
def rxn (a b : ℕ) : Fin 3 → Reaction Unit
  | 0 => ⟨cpx 0, cpx 1⟩
  | 1 => ⟨cpx 1, cpx 0⟩
  | 2 => ⟨cpx a, cpx b⟩

/-- The fully open one-reaction network. -/
abbrev N (a b : ℕ) : Network Unit :=
  ⟨Fin 3, inferInstance, inferInstance, rxn a b⟩

theorem src_vals (a b : ℕ) :
    ((N a b).reaction 0).source () = 0 ∧ ((N a b).reaction 1).source () = 1 ∧
      ((N a b).reaction 2).source () = a := ⟨rfl, rfl, rfl⟩

theorem rv_vals (a b : ℕ) :
    (N a b).reactionVector 0 () = 1 ∧ (N a b).reactionVector 1 () = -1 ∧
      (N a b).reactionVector 2 () = (b : ℝ) - a := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [reactionVector_apply, N, rxn, cpx]

/-- **Classification.** `0 ⇌ X, aX → bX` has an alternating arrow pattern iff `1 < a < b`. -/
theorem hasAlternatingArrowPattern_iff (a b : ℕ) :
    (N a b).HasAlternatingArrowPattern ↔ 1 < a ∧ a < b := by
  obtain ⟨s0, s1, s2⟩ := src_vals a b
  obtain ⟨v0, v1, v2⟩ := rv_vals a b
  have hpos : (0 : ℝ) < (b : ℝ) - a ↔ a < b := by rw [sub_pos]; exact_mod_cast Iff.rfl
  have hneg : (b : ℝ) - a < 0 ↔ b < a := by rw [sub_neg]; exact_mod_cast Iff.rfl
  constructor
  · rintro ⟨r₁, r₂, r₃, h12, h23, h⟩
    have hd : (default : Unit) = () := rfl
    simp only [hd] at h12 h23 h
    fin_cases r₁ <;> fin_cases r₂ <;> fin_cases r₃ <;>
      (try simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at h12 h23 h) <;>
      (try simp only [s0, s1, s2, v0, v1, v2, hpos, hneg] at h12 h23 h) <;>
      (try simp only [rxn, cpx] at h12 h23) <;>
      (try norm_num at h12 h23 h) <;> (try omega)
  · rintro ⟨ha, hb⟩
    refine ⟨0, 1, 2, ?_, ?_, Or.inl ⟨?_, ?_, ?_⟩⟩
    · show ((N a b).reaction 0).source () < ((N a b).reaction 1).source (); rw [s0, s1]; omega
    · show ((N a b).reaction 1).source () < ((N a b).reaction 2).source (); rw [s1, s2]; exact ha
    · show (0 : ℝ) < (N a b).reactionVector 0 (); rw [v0]; norm_num
    · show (N a b).reactionVector 1 () < 0; rw [v1]; norm_num
    · show (0 : ℝ) < (N a b).reactionVector 2 (); rw [v2]; exact hpos.mpr hb

/-- **Joshi 2013 (one species).** `0 ⇌ X, aX → bX` is nondegenerately multistationary iff
`1 < a < b`. -/
theorem multistationary_iff (a b : ℕ) :
    (∃ (κ : RateConstants (N a b)) (x z : Concentration Unit), (N a b).oneSpeciesPoly κ ≠ 0 ∧
        x.Positive ∧ z.Positive ∧ x ≠ z ∧ (N a b).IsMassActionSteadyState κ x ∧
          (N a b).IsMassActionSteadyState κ z) ↔ 1 < a ∧ a < b := by
  rw [oneSpecies_nondegenerate_multistationary_iff, hasAlternatingArrowPattern_iff]

end CRNT.Examples.OneReactionAtom
