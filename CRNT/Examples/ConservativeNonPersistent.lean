import CRNT.Examples.Minimal
import CRNT.Persistence.ConservativePersistence

set_option backward.isDefEq.respectTransparency false

/-!
# Weak reversibility cannot be dropped from conservative persistence

The network `A → B` (`CRNT.Examples.Minimal.N`) is conservative (`A + B` is conserved) but not
weakly reversible, and it is not persistent: with unit rate the solution
`(exp (-t), 2 - exp (-t))` from `(1, 1)` leaves every compact set of positive states.  This is a
check on `weaklyReversible_conservative_persistentFrom`: its conclusion `PersistentFrom` is not
satisfied for free, and its weak-reversibility hypothesis is needed.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.Minimal

open CRNT CRNT.Network Real

theorem univ_species : (Finset.univ : Finset Species) = {.A, .B} := by decide

theorem univ_rxn : (Finset.univ : Finset Rxn) = {.r1} := by decide

/-- `A + B` is a strictly positive conservation law. -/
theorem isConservative : N.IsConservative := by
  refine ⟨fun _ => 1, ?_, fun _ => one_pos⟩
  unfold IsPInvariant stoichSubspace
  refine mem_orthSum_span ?_
  rintro g ⟨r, rfl⟩
  cases r
  rw [reactionVector_r1]
  simp [univ_species]

/-- Unit rate constant. -/
def κ₁ : N.RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

/-- The explicit solution from `(1, 1)`. -/
noncomputable def sol (t : ℝ) : Concentration Species := fun s =>
  match s with
  | .A => exp (-t)
  | .B => 2 - exp (-t)

theorem field_eq (x : Concentration Species) :
    N.massActionVectorField κ₁ x = fun s => match s with | .A => -x .A | .B => x .A := by
  funext s
  cases s <;> simp [massActionVectorField_apply, massActionRate, κ₁, univ_rxn,
    Complex.massActionMonomial, N, rxn, cA, cB, univ_species]

theorem sol_hasDerivAt (t : ℝ) : HasDerivAt sol (N.massActionVectorField κ₁ (sol t)) t := by
  rw [field_eq, hasDerivAt_pi]
  have he : HasDerivAt (fun t : ℝ => exp (-t)) (-exp (-t)) t := by
    simpa using (hasDerivAt_neg t).exp
  intro s
  cases s
  · simpa [sol] using he
  · simpa [sol] using he.const_sub 2

/-- `A → B` is not persistent from `(1, 1)` at unit rate. -/
theorem not_persistentFrom : ¬ N.PersistentFrom κ₁ (sol 0) := by
  rintro ⟨K, hK, hKpos, hstay⟩
  have hmem : ∀ t : ℝ, 0 ≤ t → sol t ∈ K := hstay sol rfl (fun t _ => sol_hasDerivAt t)
  obtain ⟨y, hyK, hymin⟩ := hK.exists_isMinOn ⟨sol 0, hmem 0 le_rfl⟩
    ((continuous_apply Species.A).continuousOn)
  have hy : 0 < y .A := hKpos y hyK .A
  set t := -log (y .A) + 1
  have ht : 0 ≤ t := by
    have h0 : y .A ≤ sol 0 .A := hymin (hmem 0 le_rfl)
    have h0' : sol 0 .A = 1 := by simp [sol]
    have := Real.log_nonpos hy.le (h0'.symm ▸ h0)
    simp only [t]; linarith
  have h1 : y .A ≤ sol t .A := hymin (hmem t ht)
  have h2 : sol t .A = y .A * exp (-1) := by
    simp only [sol, t, neg_add, neg_neg, exp_add, exp_log hy]
  have h3 : exp (-1 : ℝ) < 1 := by rw [Real.exp_lt_one_iff]; norm_num
  rw [h2] at h1
  nlinarith

/-- Conservative networks need not be persistent without weak reversibility. -/
theorem not_structurallyPersistent : ¬ N.StructurallyPersistent := fun h =>
  not_persistentFrom (h κ₁ (sol 0) (fun s => by cases s <;> simp [sol]))

end CRNT.Examples.Minimal
