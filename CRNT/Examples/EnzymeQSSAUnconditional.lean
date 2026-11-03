import CRNT.Examples.Enzyme
import CRNT.Dynamics.EnzymeQSSA
import CRNT.Dynamics.GenuineConfinement

set_option backward.isDefEq.respectTransparency false

/-!
# Unconditional QSSA bound for the mass-action enzyme network

For the network `E + S ⇌ ES → E + P` (`CRNT.Examples.Enzyme.N`), any rate constants, and any
forward mass-action solution from a positive state, the complex concentration stays within

`|ES(t) - c*(S(t))| ≤ |ES(0) - c*(S(0))| + (e₀ / K_M) · (k₁ e₀ S_tot + k₋₁ e₀) / (k₋₁ + k₂)`

of the Briggs–Haldane quasi-steady state, for all `t ≥ 0`, where `e₀ = E(0) + ES(0)` and
`S_tot = S(0) + ES(0) + P(0)` (`qssa_error_le_enzyme`).  The hypotheses of
`Enzyme.qssa_error_le` are discharged from the network: positivity of solutions, conservation of
total enzyme and of total substrate.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT.Examples.Enzyme

open CRNT CRNT.Network Species

theorem univ_species : (Finset.univ : Finset Species) = {E, S, ES, P} := by decide
theorem univ_rxn : (Finset.univ : Finset Rxn) = {.bind, .unbind, .catalyze} := by decide

theorem field_S (κ : N.RateConstants) (x : Concentration Species) :
    N.massActionVectorField κ x S =
      -κ.k .bind * x E * x S + κ.k .unbind * x ES := by
  simp [massActionVectorField_apply, massActionRate, univ_rxn, Complex.massActionMonomial,
    univ_species, Network.reactionVector, N, rxn, Reaction.vector, cES_sub, cESbound, cEP]
  ring

theorem field_ES (κ : N.RateConstants) (x : Concentration Species) :
    N.massActionVectorField κ x ES =
      κ.k .bind * x E * x S - (κ.k .unbind + κ.k .catalyze) * x ES := by
  simp [massActionVectorField_apply, massActionRate, univ_rxn, Complex.massActionMonomial,
    univ_species, Network.reactionVector, N, rxn, Reaction.vector, cES_sub, cESbound, cEP]
  ring

/-- Total substrate `S + ES + P` is conserved by every reaction. -/
theorem substrate_conserved (κ : N.RateConstants) (x : Concentration Species) :
    N.massActionVectorField κ x S + N.massActionVectorField κ x ES +
      N.massActionVectorField κ x P = 0 := by
  simp [massActionVectorField_apply, massActionRate, univ_rxn, Complex.massActionMonomial,
    univ_species, Network.reactionVector, N, rxn, Reaction.vector, cES_sub, cESbound, cEP]
  ring

/-- A linear combination of coordinates whose field combination vanishes is constant forward. -/
theorem const_of_field_zero (κ : N.RateConstants) {γ : ℝ → Concentration Species}
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (w : Species → ℝ) (hw : ∀ x, ∑ s, w s * N.massActionVectorField κ x s = 0) :
    ∀ t, 0 ≤ t → ∑ s, w s * γ t s = ∑ s, w s * γ 0 s := by
  intro t ht
  have hd : ∀ τ, 0 ≤ τ → HasDerivAt (fun τ => ∑ s, w s * γ τ s) 0 τ := by
    intro τ hτ
    have h := HasDerivAt.sum (u := Finset.univ) fun s _ =>
      ((hasDerivAt_pi.mp (hsol τ hτ)) s).const_mul (w s)
    rw [hw (γ τ)] at h
    convert h using 1
    funext τ'; simp
  have := constant_of_has_deriv_right_zero (f := fun τ => ∑ s, w s * γ τ s) (a := 0) (b := t)
    (fun τ hτ => (hd τ hτ.1).continuousAt.continuousWithinAt)
    (fun τ hτ => (hd τ hτ.1).hasDerivWithinAt) t ⟨ht, le_rfl⟩
  exact this

/-- **QSSA error bound for the mass-action enzyme network** (no hypotheses beyond positivity of
the initial state). -/
theorem qssa_error_le_enzyme (κ : N.RateConstants) {γ : ℝ → Concentration Species}
    (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    ∀ t, 0 ≤ t →
      |γ t ES - Enzyme.qss (κ.k .bind) (κ.k .unbind) (κ.k .catalyze) (γ 0 E + γ 0 ES) (γ t S)| ≤
        |γ 0 ES - Enzyme.qss (κ.k .bind) (κ.k .unbind) (κ.k .catalyze) (γ 0 E + γ 0 ES) (γ 0 S)|
        + ((γ 0 E + γ 0 ES) / ((κ.k .unbind + κ.k .catalyze) / κ.k .bind))
          * (κ.k .bind * (γ 0 E + γ 0 ES) * (γ 0 S + γ 0 ES + γ 0 P)
              + κ.k .unbind * (γ 0 E + γ 0 ES))
          / (κ.k .unbind + κ.k .catalyze) := by
  set k₁ := κ.k .bind
  set km₁ := κ.k .unbind
  set k₂ := κ.k .catalyze
  set e₀ := γ 0 E + γ 0 ES with he₀
  set St := γ 0 S + γ 0 ES + γ 0 P with hSt
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  -- conservation laws along the solution
  have henz : ∀ t, 0 ≤ t → γ t E + γ t ES = e₀ := by
    intro t ht
    have := const_of_field_zero κ hsol (fun s => match s with | E => 1 | ES => 1 | _ => 0)
      (fun x => by
        have h := total_enzyme_conserved κ x
        simp [univ_species] at h ⊢; linarith) t ht
    simpa [univ_species, he₀] using this
  have hsub : ∀ t, 0 ≤ t → γ t S + γ t ES + γ t P = St := by
    intro t ht
    have := const_of_field_zero κ hsol (fun s => match s with | S => 1 | ES => 1 | P => 1 | _ => 0)
      (fun x => by
        have h := substrate_conserved κ x
        simp [univ_species] at h ⊢; linarith) t ht
    simp [univ_species] at this
    rw [hSt]; linarith
  have hkm : 0 < km₁ + k₂ := add_pos (κ.positive _) (κ.positive _)
  have he₀nn : 0 ≤ e₀ := by rw [he₀]; linarith [hγ0 E, hγ0 ES]
  have hE : ∀ t, 0 ≤ t → γ t E = e₀ - γ t ES := fun t ht => by linarith [henz t ht]
  refine Enzyme.qssa_error_le (κ.positive _) hkm he₀nn
    (D := k₁ * e₀ * St + km₁ * e₀) (by
      have := hγ0 S; have := hγ0 ES; have := hγ0 P
      have : 0 ≤ St := by rw [hSt]; linarith
      have := κ.positive Rxn.bind; have := κ.positive Rxn.unbind
      positivity)
    (s := fun t => γ t S) (c := fun t => γ t ES) ?_ ?_ ?_ ?_
  · intro t ht
    have h := (hasDerivAt_pi.mp (hsol t ht)) S
    rw [field_S, hE t ht] at h
    convert h using 1
  · intro t ht
    have h := (hasDerivAt_pi.mp (hsol t ht)) ES
    rw [field_ES, hE t ht] at h
    convert h using 1
    simp only [Enzyme.fastField]; ring
  · intro t ht; exact (hpos t ht S).le
  · intro t ht
    have hS := hpos t ht S; have hES := hpos t ht ES; have hEp := hpos t ht E; have hP := hpos t ht P
    have hEt := hE t ht
    have hSle : γ t S ≤ St := by linarith [hsub t ht]
    have hcle : γ t ES ≤ e₀ := by linarith
    have hk1 := κ.positive Rxn.bind; have hkm1 := κ.positive Rxn.unbind
    rw [abs_le]
    constructor
    · -- `-ṡ ≤ k₁ (e₀ - c) s ≤ k₁ e₀ S_tot`
      have h1 : k₁ * (e₀ - γ t ES) * γ t S ≤ k₁ * e₀ * St := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hk1.le) hSle hS.le
        exact mul_nonneg hk1.le he₀nn
      nlinarith [mul_nonneg hkm1.le hES.le, mul_nonneg hkm1.le he₀nn]
    · have h2 : km₁ * γ t ES ≤ km₁ * e₀ := mul_le_mul_of_nonneg_left hcle hkm1.le
      have h3 : 0 ≤ k₁ * (e₀ - γ t ES) * γ t S :=
        mul_nonneg (mul_nonneg hk1.le (by linarith)) hS.le
      nlinarith [mul_nonneg (mul_nonneg hk1.le he₀nn) (show 0 ≤ St by linarith)]

/-- **Tikhonov-type QSSA bound for the mass-action enzyme network**: decaying initial mismatch. -/
theorem qssa_error_decay_enzyme (κ : N.RateConstants) {γ : ℝ → Concentration Species}
    (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    ∀ t, 0 ≤ t →
      |γ t ES - Enzyme.qss (κ.k .bind) (κ.k .unbind) (κ.k .catalyze) (γ 0 E + γ 0 ES) (γ t S)| ≤
        Real.exp (-(κ.k .unbind + κ.k .catalyze) * t) *
          |γ 0 ES - Enzyme.qss (κ.k .bind) (κ.k .unbind) (κ.k .catalyze) (γ 0 E + γ 0 ES) (γ 0 S)|
        + ((γ 0 E + γ 0 ES) / ((κ.k .unbind + κ.k .catalyze) / κ.k .bind))
          * (κ.k .bind * (γ 0 E + γ 0 ES) * (γ 0 S + γ 0 ES + γ 0 P)
              + κ.k .unbind * (γ 0 E + γ 0 ES))
          / (κ.k .unbind + κ.k .catalyze) := by
  set k₁ := κ.k .bind
  set km₁ := κ.k .unbind
  set k₂ := κ.k .catalyze
  set e₀ := γ 0 E + γ 0 ES with he₀
  set St := γ 0 S + γ 0 ES + γ 0 P with hSt
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  -- conservation laws along the solution
  have henz : ∀ t, 0 ≤ t → γ t E + γ t ES = e₀ := by
    intro t ht
    have := const_of_field_zero κ hsol (fun s => match s with | E => 1 | ES => 1 | _ => 0)
      (fun x => by
        have h := total_enzyme_conserved κ x
        simp [univ_species] at h ⊢; linarith) t ht
    simpa [univ_species, he₀] using this
  have hsub : ∀ t, 0 ≤ t → γ t S + γ t ES + γ t P = St := by
    intro t ht
    have := const_of_field_zero κ hsol (fun s => match s with | S => 1 | ES => 1 | P => 1 | _ => 0)
      (fun x => by
        have h := substrate_conserved κ x
        simp [univ_species] at h ⊢; linarith) t ht
    simp [univ_species] at this
    rw [hSt]; linarith
  have hkm : 0 < km₁ + k₂ := add_pos (κ.positive _) (κ.positive _)
  have he₀nn : 0 ≤ e₀ := by rw [he₀]; linarith [hγ0 E, hγ0 ES]
  have hE : ∀ t, 0 ≤ t → γ t E = e₀ - γ t ES := fun t ht => by linarith [henz t ht]
  refine Enzyme.qssa_error_decay (κ.positive _) hkm he₀nn
    (D := k₁ * e₀ * St + km₁ * e₀) (by
      have := hγ0 S; have := hγ0 ES; have := hγ0 P
      have : 0 ≤ St := by rw [hSt]; linarith
      have := κ.positive Rxn.bind; have := κ.positive Rxn.unbind
      positivity)
    (s := fun t => γ t S) (c := fun t => γ t ES) ?_ ?_ ?_ ?_
  · intro t ht
    have h := (hasDerivAt_pi.mp (hsol t ht)) S
    rw [field_S, hE t ht] at h
    convert h using 1
  · intro t ht
    have h := (hasDerivAt_pi.mp (hsol t ht)) ES
    rw [field_ES, hE t ht] at h
    convert h using 1
    simp only [Enzyme.fastField]; ring
  · intro t ht; exact (hpos t ht S).le
  · intro t ht
    have hS := hpos t ht S; have hES := hpos t ht ES; have hEp := hpos t ht E; have hP := hpos t ht P
    have hEt := hE t ht
    have hSle : γ t S ≤ St := by linarith [hsub t ht]
    have hcle : γ t ES ≤ e₀ := by linarith
    have hk1 := κ.positive Rxn.bind; have hkm1 := κ.positive Rxn.unbind
    rw [abs_le]
    constructor
    · -- `-ṡ ≤ k₁ (e₀ - c) s ≤ k₁ e₀ S_tot`
      have h1 : k₁ * (e₀ - γ t ES) * γ t S ≤ k₁ * e₀ * St := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hk1.le) hSle hS.le
        exact mul_nonneg hk1.le he₀nn
      nlinarith [mul_nonneg hkm1.le hES.le, mul_nonneg hkm1.le he₀nn]
    · have h2 : km₁ * γ t ES ≤ km₁ * e₀ := mul_le_mul_of_nonneg_left hcle hkm1.le
      have h3 : 0 ≤ k₁ * (e₀ - γ t ES) * γ t S :=
        mul_nonneg (mul_nonneg hk1.le (by linarith)) hS.le
      nlinarith [mul_nonneg (mul_nonneg hk1.le he₀nn) (show 0 ≤ St by linarith)]

end CRNT.Examples.Enzyme
