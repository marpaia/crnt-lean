import CRNT.Oscillation.Basic

/-!
# From local attraction plus absorption to a class-global limit cycle

Global attraction should not be bundled into the local Floquet theorem.  This module isolates the
separate global ingredient: every exact forward solution in the target stoichiometric class must
*eventually enter* a basin on which the periodic orbit is already known to attract.

The main theorem is elementary but important for the certificate architecture:

`local attraction on U + absorption of the class into U -> class-global attraction`.

The proof uses only autonomy of the ODE: after the entry time `τ`, shift the exact solution by `τ`
and apply the local attraction statement to the shifted solution.  No global-flow object or hidden
uniqueness assumption is needed.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every exact forward solution starting in `source` eventually enters `target`.

This is deliberately trajectory-quantified, matching `PositivePeriodicOrbit.GloballyAttractsSolutions`.
It can later be established by a trapping-region, Lyapunov, persistence, or dissipativity theorem. -/
def SolutionsEventuallyEnter (N : Network S) (κ : N.RateConstants)
    (source target : Set (Concentration S)) : Prop :=
  ∀ x ∈ source, ∀ γ : ℝ → Concentration S,
    γ 0 = x →
    (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
    ∃ τ : ℝ, 0 ≤ τ ∧ γ τ ∈ target

namespace PositivePeriodicOrbit

variable {N : Network S} {κ : N.RateConstants}

/-- Time-shifting an exact forward mass-action solution preserves the ODE on forward time. -/
theorem shiftedSolution
    {γ : ℝ → Concentration S}
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ∀ t, 0 ≤ t →
      HasDerivAt (fun u => γ (u + τ))
        (N.massActionVectorField κ (γ (t + τ))) t := by
  intro t ht
  have hshift : HasDerivAt (fun u : ℝ => u + τ) 1 t := by
    simpa using (hasDerivAt_id t).add_const τ
  have hγ := hsol (t + τ) (by linarith)
  simpa [Function.comp_def] using hγ.scomp t hshift

/-- **Local-to-global attraction bridge.**

If `P` attracts every exact solution starting in a local basin `U`, and every exact solution
starting in a larger set `C` eventually enters `U`, then `P` attracts every exact solution starting
in `C`. -/
theorem globallyAttractsSolutions_of_eventuallyEnters
    (P : N.PositivePeriodicOrbit κ)
    {C U : Set (Concentration S)}
    (hlocal : P.GloballyAttractsSolutions U)
    (henter : N.SolutionsEventuallyEnter κ C U) :
    P.GloballyAttractsSolutions C := by
  intro x hx γ hγ0 hsol ε hε
  obtain ⟨τ, hτ, hτU⟩ := henter x hx γ hγ0 hsol
  let shifted : ℝ → Concentration S := fun u => γ (u + τ)
  have hshift0 : shifted 0 = γ τ := by
    simp [shifted]
  have hshiftSol : ∀ t, 0 ≤ t →
      HasDerivAt shifted (N.massActionVectorField κ (shifted t)) t := by
    intro t ht
    simpa [shifted] using
      (PositivePeriodicOrbit.shiftedSolution (N := N) (κ := κ) hsol hτ t ht)
  obtain ⟨T, hT, hnear⟩ := hlocal (γ τ) hτU shifted hshift0 hshiftSol ε hε
  refine ⟨τ + T, by linarith, ?_⟩
  intro t ht
  have hsub : T ≤ t - τ := by linarith
  obtain ⟨phase, hphase⟩ := hnear (t - τ) hsub
  refine ⟨phase, ?_⟩
  simpa [shifted] using hphase

/-- A locally attracting cycle becomes a class-global limit cycle once its positive
stoichiometric class is absorbed into the local basin. -/
def globalLimitCycleOnClass_of_localAttraction_and_absorption
    (P : N.PositivePeriodicOrbit κ)
    (U : Set (Concentration S))
    (hlocal : P.GloballyAttractsSolutions U)
    (henter : N.SolutionsEventuallyEnter κ
      (N.positiveCompatibilityClass (P.orbit 0)) U) :
    N.GlobalLimitCycleOnClass κ where
  orbit := P
  attracts := P.globallyAttractsSolutions_of_eventuallyEnters hlocal henter

end PositivePeriodicOrbit

/-- Network-level form of the local-attraction + absorption principle. -/
theorem hasGlobalLimitCycleOnClass_of_localAttraction_and_absorption
    {N : Network S} {κ : N.RateConstants}
    (P : N.PositivePeriodicOrbit κ)
    (U : Set (Concentration S))
    (hlocal : P.GloballyAttractsSolutions U)
    (henter : N.SolutionsEventuallyEnter κ
      (N.positiveCompatibilityClass (P.orbit 0)) U) :
    N.HasGlobalLimitCycleOnClass κ :=
  ⟨P.globalLimitCycleOnClass_of_localAttraction_and_absorption U hlocal henter⟩

end Network

end CRNT
