import CRNT.Equilibria.DetailedBalanceEntropy
import CRNT.Dynamics.ConservationLaw
import CRNT.Stoich.ConservationDimension
import CRNT.Theorems.DeficiencyZero.Stability

/-!
# Gibbs free energy with standard chemical potentials

This module formalizes the **Gibbs free energy** built from a vector of *standard
chemical potentials* `μ : S → ℝ` for a mass-action network, and the classical
statements about it.

For a state `x` (a concentration vector) the Gibbs free energy is

```text
G_μ (x) = ∑_s μ_s x_s .
```

Its rate of change along the mass-action flow `ẋ = f_κ(x)` is

```text
dG/dt = ∑_s μ_s f_κ(x)_s = ∑_r κ_r (⟨μ, y'_r⟩ − ⟨μ, y_r⟩) x^{y_r} ,
```

where `⟨μ, y⟩ = ∑_s μ_s y_s` is the chemical content of a complex `y`, `y_r` is the
source complex of reaction `r` and `y'_r` its target complex. The **chemical
affinity** of reaction `r` is

```text
A_r := ⟨μ, y_r⟩ − ⟨μ, y'_r⟩ ,
```

so that `dG/dt = −∑_r κ_r A_r x^{y_r}`: a reaction with `A_r > 0` is
*thermodynamically favoured* in the forward direction, because firing it lowers the
Gibbs free energy.

## What is proved here

* `Network.gibbsFreeEnergy_rateOfChange` — the rate of change identity above.
* `Network.chemicalAffinity_pos_iff_forwardDecreasesFreeEnergy` — a reaction is
  thermodynamically favoured exactly when its affinity is positive.
* `Network.chemicalAffinity_eq_zero_iff_conservationLaw` — the standard chemical
  potentials are a **P-invariant** (a conserved quantity) of the network exactly when
  every affinity vanishes.  This *reuses* the existing conservation-law theory
  (`Network.IsPInvariant`, `Network.conservationLawSpace`,
  `Network.mem_conservationLawSpace_iff`) instead of re-proving it.
* `Network.gibbsFreeEnergy_const_along_solution` — with such `μ`, the Gibbs free
  energy is a constant of motion of the mass-action dynamics (reusing
  `Network.conservationLaw_const_along_solution`).
* `Network.gibbsFreeEnergy_stationary_at_complexBalanced` — at a complex-balanced
  equilibrium `x*` the Gibbs free energy is **stationary for every** `μ`, and the
  network affinity `∑_r κ_r x*^{y_r} A_r` vanishes there.
* `Network.gibbsFreeEnergy_dissipation_eq_affinity_netCurrent` — the classical
  **De Donder** identity: the free-energy dissipation rate is
  `−dG/dt = ½ ∑_r A_r J_r`, with `J_r = v_r − v_{rev(r)}` the net current of the
  reaction pair.
* `Network.gibbsFreeEnergy_dissipation_eq_sum_squares` — under the classical
  *linear local detailed balance* hypothesis on the rate law, the dissipation is the
  **sum of the squares of the affinities**:
  `−dG/dt = (1/2τ) ∑_r κ_r A_r² x^{y_r}` (with `τ = 1` this is exactly
  `−dG/dt = ½ ∑_r κ_r A_r² x^{y_r}`), hence nonnegative.
* `Network.gibbsFreeEnergy_dissipation_eq_tau_entropyProduction` — with
  *thermodynamically consistent* standard chemical potentials
  (`A_r = τ (log v_r − log v_{rev(r)})`) the free-energy dissipation rate is
  `τ` times the **entropy production** of leaf E1, hence nonnegative.

### A remark on the "sum of squares" identity

The *unconditional* classical statement is De Donder's identity
(`Network.gibbsFreeEnergy_dissipation_eq_affinity_netCurrent`): the dissipation rate
is `½ ∑_r A_r J_r` with `J_r = v_r − v_{rev(r)}` the net current, i.e. it is
*linear* in the affinities.  The "sum of the squares of the affinities" form
`½ ∑_r κ_r A_r² x^{y_r}` is the **linear-response** version of that identity: it
requires the net current to be the affinity times the average flux, which is exactly
the hypothesis `Network.HasLinearAffinityLaw` (the classical local detailed balance
condition with a linear rate law).  Under that hypothesis the two forms coincide,
because

```text
½ ∑_r A_r J_r = ½ ∑_r A_r · (A_r/2τ)(v_r + v_rev(r)) = (1/2τ) ∑_r A_r² v_r ,
```

where the last step uses `A_{rev(r)}² = A_r²`.  The hypothesis is explicit and is
*not* silently assumed; the same file also exhibits a concrete network and a concrete
state at which it holds (`CRNT.Examples.GibbsIsomerization.linearAffinityLaw_at_state`)
and at which the identity reads `−dG/dt = ½ (1·1²·3 + 1·1²·1) = 2`.

## Relation to leaf E1 (entropy production)

Leaf E1 (`CRNT.Network.entropyProduction_nonneg`) proves that the entropy production
`σ = ½ ∑_r (v_r − v_{rev(r)}) (log v_r − log v_{rev(r)})` of a detailed-balanced
network is nonnegative.  This module supplies the missing "standard chemical
potentials" half of the classical picture: the Gibbs free energy `G_μ`, its chemical
affinity `A_r`, the fact that `μ` is a conserved quantity exactly when all affinities
vanish, and the identity that ties the free-energy dissipation to the entropy
production of E1 (`gibbsFreeEnergy_dissipation_eq_tau_entropyProduction`).

### Relation to the pseudo-Helmholtz free energy (leaf E1)

The pseudo-Helmholtz function of the deficiency-zero theory
(`CRNT.Theorems.DeficiencyZero.Lyapunov`,
`relEntropy x* x = ∑_s x_s (log(x_s/x*_s) − 1) + x*_s`) is the *non-ideal*
(activity-based) counterpart of `G_μ`: it is the free energy of the complex-balanced
equilibrium `x*` taken with the *local* chemical potentials `μ_s = log x*_s + const`,
and it is a strict Lyapunov function of the mass-action flow
(`CRNT.Network.relEntropy_antitone_along_solution`).  The `G_μ` formalized here is the
free energy of the *standard* chemical potentials: it is linear in `x`, it is
conserved exactly for the P-invariants of the network, and its dissipation rate is
the entropy production of leaf E1 once the standard chemical potentials are
thermodynamically consistent (`gibbsFreeEnergy_dissipation_eq_tau_entropyProduction`).

Two classical statements that are *not* formalized here (and are not part of the
cited result): non-ideal (activity-based) thermodynamics, and thermodynamic
potentials for networks that are not complex balanced.

Depends on: `CRNT.Equilibria.DetailedBalanceEntropy`, `CRNT.Dynamics.ConservationLaw`,
`CRNT.Stoich.ConservationDimension`, `CRNT.Theorems.DeficiencyZero.Stability`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The chemical content in a complex.** `⟨μ, y⟩ = ∑_s μ_s y_s`: the total
standard free energy of the complex `y` at the standard chemical potentials `μ`. -/
def complexChemicalPotential (μ : S → ℝ) (y : Complex S) : ℝ :=
  ∑ s : S, μ s * (y s : ℝ)

/-- **The chemical affinity of a reaction.** `A_r = ⟨μ, y_r⟩ − ⟨μ, y'_r⟩`: the
difference of the chemical content of the source and the target complex of reaction
`r`.  `A_r > 0` means the reaction is thermodynamically favoured in the forward
direction. -/
def chemicalAffinity (N : Network S) (μ : S → ℝ) (r : N.R) : ℝ :=
  complexChemicalPotential μ (N.reaction r).source - complexChemicalPotential μ (N.reaction r).target

/-- **The Gibbs free energy** of the state `x` at the standard chemical potentials
`μ`: `G_μ (x) = ∑_s μ_s x_s`. -/
def gibbsFreeEnergy (μ : S → ℝ) (x : Concentration S) : ℝ :=
  ∑ s : S, μ s * x s

/-- **The rate of dissipation of the Gibbs free energy**, `−dG/dt`.  It is the
affinity-weighted reaction flux, `∑_r κ_r A_r x^{y_r}`. -/
def gibbsFreeEnergyDissipation (N : Network S) (κ : RateConstants N) (μ : S → ℝ)
    (x : Concentration S) : ℝ :=
  ∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ r x

/-- The pairing of `μ` with the (stoichiometric) reaction vector is the negative of
the affinity of the reaction.  This is the bridge to the conservation-law theory,
since the reaction vectors span the stoichiometric subspace. -/
theorem reactionVector_pairing_eq_neg_affinity (N : Network S) (μ : S → ℝ) (r : N.R) :
    (∑ s, μ s * N.reactionVector r s) = -(N.chemicalAffinity μ r) := by
  rw [chemicalAffinity, complexChemicalPotential, complexChemicalPotential,
    ← Finset.sum_sub_distrib]
  simp only [reactionVector_apply]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- The affinity of a reaction is the negative of the pairing of `μ` with the
(stoichiometric) reaction vector. -/
theorem chemicalAffinity_eq_neg_reactionVector_pairing (N : Network S) (μ : S → ℝ)
    (r : N.R) :
    N.chemicalAffinity μ r = -∑ s, μ s * N.reactionVector r s := by
  have h := N.reactionVector_pairing_eq_neg_affinity μ r
  rw [h]
  ring

/-- Reversing a reaction reverses the sign of its affinity. -/
theorem chemicalAffinity_rev (N : Network S) (ρ : ReversiblePairing N) (μ : S → ℝ)
    (r : N.R) :
    N.chemicalAffinity μ (ρ.rev r) = -(N.chemicalAffinity μ r) := by
  simp only [chemicalAffinity, complexChemicalPotential, ρ.source_rev_apply, ρ.target_rev_apply]
  ring

omit [DecidableEq S] in
/-- The Gibbs free energy is the weighted total of the species. -/
theorem gibbsFreeEnergy_eq_weightedTotal (μ : S → ℝ) (x : Concentration S) :
    gibbsFreeEnergy μ x = weightedTotal μ x := by
  rfl

/-- **Rate of change of the Gibbs free energy.** Along the mass-action flow,
`dG/dt = ∑_s μ_s f_κ(x)_s = −∑_r κ_r A_r x^{y_r}`. -/
theorem gibbsFreeEnergy_rateOfChange (N : Network S) (κ : RateConstants N) (μ : S → ℝ)
    (x : Concentration S) :
    (∑ s, μ s * N.massActionVectorField κ x s)
      = -∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ r x := by
  calc
    (∑ s, μ s * N.massActionVectorField κ x s)
        = ∑ r : N.R, ∑ s, μ s *
            (N.massActionRate κ r x * N.reactionVector r s) := by
            simp only [massActionVectorField_apply, Finset.mul_sum]
            rw [Finset.sum_comm]
    _ = ∑ r : N.R, ∑ s, (μ s * N.massActionRate κ r x) * N.reactionVector r s := by
          apply Finset.sum_congr rfl
          intro r _
          apply Finset.sum_congr rfl
          intro s _
          rw [← mul_assoc]
    _ = ∑ r : N.R, (∑ s, μ s * N.reactionVector r s) * N.massActionRate κ r x := by
          apply Finset.sum_congr rfl
          intro r _
          have h1 : (∑ s, (μ s * N.massActionRate κ r x) * N.reactionVector r s)
              = ∑ s, N.massActionRate κ r x * (μ s * N.reactionVector r s) := by
            apply Finset.sum_congr rfl
            intro s _
            ring
          have h2 : (∑ s, N.massActionRate κ r x * (μ s * N.reactionVector r s))
              = N.massActionRate κ r x * (∑ s, μ s * N.reactionVector r s) := by
            rw [← Finset.mul_sum]
          rw [h1, h2]
          ring
    _ = -∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ r x := by
          rw [← Finset.sum_neg_distrib]
          apply Finset.sum_congr rfl
          intro r _
          rw [reactionVector_pairing_eq_neg_affinity]
          ring

/-- **The dissipation rate.** `−dG/dt = ∑_r κ_r A_r x^{y_r}`. -/
theorem gibbsFreeEnergy_dissipation_eq_neg_rate (N : Network S) (κ : RateConstants N)
    (μ : S → ℝ) (x : Concentration S) :
    N.gibbsFreeEnergyDissipation κ μ x = -(∑ s, μ s * N.massActionVectorField κ x s) := by
  have h := N.gibbsFreeEnergy_rateOfChange κ μ x
  unfold gibbsFreeEnergyDissipation
  rw [h]
  ring

/-- **Thermodynamic favour.** The forward reaction `r` is thermodynamically favoured
(it lowers the Gibbs free energy) exactly when its chemical affinity is positive. -/
theorem chemicalAffinity_pos_iff_forwardDecreasesFreeEnergy (N : Network S)
    (κ : RateConstants N) {x : Concentration S} (hx : x.Positive) (μ : S → ℝ) (r : N.R) :
    0 < N.chemicalAffinity μ r ↔
      N.massActionRate κ r x * (∑ s, μ s * N.reactionVector r s) < 0 := by
  have hv : 0 < N.massActionRate κ r x := N.massActionRate_pos κ r hx
  have hA : (∑ s, μ s * N.reactionVector r s) = -(N.chemicalAffinity μ r) :=
    N.reactionVector_pairing_eq_neg_affinity μ r
  constructor
  · intro h
    have hs : (∑ s, μ s * N.reactionVector r s) < 0 := by linarith
    have h' := mul_neg_of_neg_of_pos hs hv
    simpa [mul_comm] using h'
  · intro h
    by_contra hcon
    have hA0 : N.chemicalAffinity μ r ≤ 0 := le_of_not_gt hcon
    have hs : 0 ≤ ∑ s, μ s * N.reactionVector r s := by linarith [hA]
    have hprod : 0 ≤ N.massActionRate κ r x * (∑ s, μ s * N.reactionVector r s) :=
      mul_nonneg hv.le hs
    linarith

/-- **The affinity is positive exactly when the source complex has the larger chemical
content.**  This is the definition-level form of "the reaction is thermodynamically
favoured". -/
theorem chemicalAffinity_pos_iff (N : Network S) (μ : S → ℝ) (r : N.R) :
    0 < N.chemicalAffinity μ r ↔
      complexChemicalPotential μ (N.reaction r).source
        > complexChemicalPotential μ (N.reaction r).target := by
  rw [chemicalAffinity]
  exact sub_pos

/-- **The standard chemical potentials are a conserved quantity exactly when every
affinity vanishes.**  This is the classical statement that the "equilibrium chemical
potentials" (a left null vector of the reaction vectors) make the Gibbs free energy a
P-invariant of the network.

The proof *reuses* the existing conservation-law theory: `Network.IsPInvariant`,
`Network.conservationLawSpace` and `Network.mem_conservationLawSpace_iff`. -/
theorem chemicalAffinity_eq_zero_iff_conservationLaw (N : Network S) (μ : S → ℝ) :
    (∀ r : N.R, N.chemicalAffinity μ r = 0) ↔ μ ∈ N.conservationLawSpace := by
  constructor
  · intro h
    have horth : μ ∈ orthSum (Submodule.span ℝ N.reactionVectors) := by
      refine mem_orthSum_span ?_
      rintro g ⟨r, rfl⟩
      have hz : (∑ s, μ s * N.reactionVector r s) = 0 := by
        rw [N.reactionVector_pairing_eq_neg_affinity μ r, h r]
        ring
      exact hz
    rw [Network.mem_conservationLawSpace_iff, Network.IsPInvariant]
    simpa [Network.stoichSubspace] using horth
  · intro h
    have horth : μ ∈ orthSum N.stoichSubspace := by
      rw [Network.mem_conservationLawSpace_iff, Network.IsPInvariant] at h
      exact h
    intro r
    have hz : (∑ s, μ s * N.reactionVector r s) = 0 :=
      (mem_orthSum.mp horth) (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)
    have hpair := N.reactionVector_pairing_eq_neg_affinity μ r
    rw [hpair] at hz
    linarith

/-- **The Gibbs free energy is stationary when `μ` is a conservation law.** -/
theorem gibbsFreeEnergy_rateOfChange_eq_zero_of_conservationLaw (N : Network S)
    (κ : RateConstants N) {μ : S → ℝ} (hμ : μ ∈ N.conservationLawSpace)
    (x : Concentration S) :
    (∑ s, μ s * N.massActionVectorField κ x s) = 0 := by
  have hzero : ∀ r : N.R, N.chemicalAffinity μ r = 0 :=
    (N.chemicalAffinity_eq_zero_iff_conservationLaw μ).2 hμ
  rw [N.gibbsFreeEnergy_rateOfChange κ μ x, ← Finset.sum_neg_distrib]
  apply Finset.sum_eq_zero
  intro r _
  rw [hzero r]
  ring

/-- **The Gibbs free energy is a constant of motion.** With conservation-law standard
chemical potentials, `G_μ` is constant along every mass-action solution.  This
reuses `Network.conservationLaw_const_along_solution`. -/
theorem gibbsFreeEnergy_const_along_solution (N : Network S) (κ : RateConstants N)
    {μ : S → ℝ} (hμ : μ ∈ N.conservationLawSpace)
    {γ : ℝ → Concentration S} {t : ℝ} (ht : 0 ≤ t)
    (hsol : ∀ τ ∈ Set.Icc (0 : ℝ) t, HasDerivAt γ (N.massActionVectorField κ (γ τ)) τ) :
    gibbsFreeEnergy μ (γ t) = gibbsFreeEnergy μ (γ 0) := by
  have hμ' : μ ∈ orthSum N.stoichSubspace := by
    rw [Network.mem_conservationLawSpace_iff, Network.IsPInvariant] at hμ
    exact hμ
  exact N.conservationLaw_const_along_solution κ hμ' ht hsol

/-- **Complex balance makes the Gibbs free energy stationary.** At a complex-balanced
equilibrium `x*` the mass-action vector field vanishes, so `G_μ` is stationary there
for *every* choice of standard chemical potentials `μ`. -/
theorem gibbsFreeEnergy_stationary_at_complexBalanced (N : Network S)
    (κ : RateConstants N) (μ : S → ℝ) {xstar : Concentration S}
    (hcb : N.IsComplexBalanced κ xstar) :
    (∑ s, μ s * N.massActionVectorField κ xstar s) = 0 := by
  have hsteady : N.IsMassActionSteadyState κ xstar := hcb.isMassActionSteadyState N κ
  have hf : ∀ s, N.massActionVectorField κ xstar s = 0 := by
    intro s
    exact hsteady s
  rw [Finset.sum_eq_zero]
  intro s _
  rw [hf s]
  ring

/-- **The network affinity vanishes at a complex-balanced equilibrium.** Complex balance
makes `∑_r κ_r x*^{y_r} (y'_r − y_r) = 0`, i.e. the affinity-weighted rate
`∑_r κ_r x*^{y_r} A_r` is zero, for every `μ`. -/
theorem networkAffinity_eq_zero_of_complexBalanced (N : Network S) (κ : RateConstants N)
    (μ : S → ℝ) {xstar : Concentration S} (hcb : N.IsComplexBalanced κ xstar) :
    (∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ r xstar) = 0 := by
  have h := N.gibbsFreeEnergy_stationary_at_complexBalanced κ μ hcb
  have h' : (-∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ r xstar) = 0 := by
    rw [← N.gibbsFreeEnergy_rateOfChange κ μ xstar]
    exact h
  linarith

/-- **De Donder's identity.** The free-energy dissipation rate is the affinity times
the net current, summed over the reaction pairs:
`−dG/dt = ½ ∑_r A_r (v_r − v_{rev(r)})`.  The factor `1/2` compensates for the
involutive double count of the reverse pairing. -/
theorem gibbsFreeEnergy_dissipation_eq_affinity_netCurrent (N : Network S)
    (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ) (x : Concentration S) :
    N.gibbsFreeEnergyDissipation κ μ x
      = (1 / 2 : ℝ) * ∑ r : N.R, N.chemicalAffinity μ r *
          (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x) := by
  have hsplit : (∑ r : N.R, N.chemicalAffinity μ r *
        (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x))
      = (∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ r x)
        - (∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ (ρ.rev r) x) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro r _
    ring
  have hneg : (∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ (ρ.rev r) x)
      = -∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ r x := by
    have hsubst : (∑ r : N.R, N.chemicalAffinity μ r * N.massActionRate κ (ρ.rev r) x)
        = ∑ r : N.R, N.chemicalAffinity μ (ρ.rev r) * N.massActionRate κ r x := by
      exact Fintype.sum_equiv ρ.equiv
        (fun b => N.chemicalAffinity μ b * N.massActionRate κ (ρ.rev b) x)
        (fun a => N.chemicalAffinity μ (ρ.rev a) * N.massActionRate κ a x)
        (fun a => by rw [show ρ.equiv a = ρ.rev a from rfl, ρ.rev_rev])
    rw [hsubst, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [N.chemicalAffinity_rev ρ μ r]
    ring
  unfold gibbsFreeEnergyDissipation
  rw [hsplit, hneg]
  ring

/-- **Linear local detailed balance.** The net current of the reaction pair `r` is the
affinity times the average of the two fluxes.  This is the classical linear-response
form of the local detailed balance condition, and it is exactly what turns De Donder's
identity into a sum of squares. -/
def HasLinearAffinityLaw (N : Network S) (ρ : ReversiblePairing N) (κ : RateConstants N)
    (μ : S → ℝ) (τ : ℝ) (x : Concentration S) : Prop :=
  ∀ r : N.R,
    N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x
      = (N.chemicalAffinity μ r / (2 * τ)) *
        (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x)

/-- **Thermodynamically consistent standard chemical potentials.** The affinity of each
reaction pair equals `τ` times the logarithmic flux ratio.  This is the classical
condition that the standard free energies of reaction are the (negative) logarithms of
the equilibrium constants. -/
def HasConsistentChemicalPotentials (N : Network S) (ρ : ReversiblePairing N)
    (κ : RateConstants N) (μ : S → ℝ) (τ : ℝ) (x : Concentration S) : Prop :=
  ∀ r : N.R,
    N.chemicalAffinity μ r
      = τ * (Real.log (N.massActionRate κ r x) - Real.log (N.massActionRate κ (ρ.rev r) x))

/-- **The dissipation is the sum of the squares of the affinities.** Under the linear
local detailed balance hypothesis, the free-energy dissipation rate is
`−dG/dt = (1/2τ) ∑_r κ_r A_r² x^{y_r}`; with `τ = 1` this is the classical identity
`−dG/dt = ½ ∑_r κ_r A_r² x^{y_r}`. -/
theorem gibbsFreeEnergy_dissipation_eq_sum_squares (N : Network S)
    (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ) {τ : ℝ}
    {x : Concentration S} (hlin : N.HasLinearAffinityLaw ρ κ μ τ x) :
    N.gibbsFreeEnergyDissipation κ μ x
      = (1 / (2 * τ)) * ∑ r : N.R, κ.k r * (N.chemicalAffinity μ r)^2 *
          (N.reaction r).source.massActionMonomial x := by
  have hd := N.gibbsFreeEnergy_dissipation_eq_affinity_netCurrent ρ κ μ x
  have hstep : ∀ r : N.R,
      N.chemicalAffinity μ r *
          (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x)
        = (N.chemicalAffinity μ r ^ 2 / (2 * τ)) *
            (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x) := by
    intro r
    have h := hlin r
    rw [h]
    ring
  have hrev : (∑ r : N.R, N.chemicalAffinity μ r ^ 2 * N.massActionRate κ (ρ.rev r) x)
      = ∑ r : N.R, N.chemicalAffinity μ r ^ 2 * N.massActionRate κ r x := by
    have hsubst : (∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
          N.massActionRate κ (ρ.rev r) x)
        = ∑ r : N.R, N.chemicalAffinity μ (ρ.rev r) ^ 2 * N.massActionRate κ r x := by
      exact Fintype.sum_equiv ρ.equiv
        (fun b => N.chemicalAffinity μ b ^ 2 * N.massActionRate κ (ρ.rev b) x)
        (fun a => N.chemicalAffinity μ (ρ.rev a) ^ 2 * N.massActionRate κ a x)
        (fun a => by rw [show ρ.equiv a = ρ.rev a from rfl, ρ.rev_rev])
    rw [hsubst]
    apply Finset.sum_congr rfl
    intro r _
    rw [N.chemicalAffinity_rev ρ μ r]
    ring
  have hT1 : (∑ r : N.R, N.chemicalAffinity μ r *
        (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x))
      = ∑ r : N.R, (N.chemicalAffinity μ r ^ 2 / (2 * τ)) *
          (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x) := by
    apply Finset.sum_congr rfl
    intro r _
    exact hstep r
  have hT2 : (∑ r : N.R, (N.chemicalAffinity μ r ^ 2 / (2 * τ)) *
        (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x))
      = (1 / (2 * τ)) * ∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
          (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x) := by
    calc
      (∑ r : N.R, (N.chemicalAffinity μ r ^ 2 / (2 * τ)) *
          (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x))
          = ∑ r : N.R, (1 / (2 * τ)) * (N.chemicalAffinity μ r ^ 2 *
              (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x)) := by
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ = (1 / (2 * τ)) * ∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
              (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x) := by
            rw [← Finset.mul_sum]
  have hT3 : (∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
        (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x))
      = (∑ r : N.R, N.chemicalAffinity μ r ^ 2 * N.massActionRate κ r x)
        + (∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
              N.massActionRate κ (ρ.rev r) x) := by
    calc
      (∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
          (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x))
          = ∑ r : N.R, (N.chemicalAffinity μ r ^ 2 * N.massActionRate κ r x
              + N.chemicalAffinity μ r ^ 2 * N.massActionRate κ (ρ.rev r) x) := by
            apply Finset.sum_congr rfl
            intro r _
            ring
      _ = (∑ r : N.R, N.chemicalAffinity μ r ^ 2 * N.massActionRate κ r x)
          + (∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
                N.massActionRate κ (ρ.rev r) x) := by
            rw [Finset.sum_add_distrib]
  have hT4 : (∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
        (N.massActionRate κ r x + N.massActionRate κ (ρ.rev r) x))
      = 2 * ∑ r : N.R, N.chemicalAffinity μ r ^ 2 * N.massActionRate κ r x := by
    rw [hT3, hrev]
    ring
  have hsq : (∑ r : N.R, N.chemicalAffinity μ r ^ 2 * N.massActionRate κ r x)
      = ∑ r : N.R, κ.k r * (N.chemicalAffinity μ r)^2 *
          (N.reaction r).source.massActionMonomial x := by
    apply Finset.sum_congr rfl
    intro r _
    rw [massActionRate]
    ring
  calc
    N.gibbsFreeEnergyDissipation κ μ x
        = (1 / 2 : ℝ) * ∑ r : N.R, N.chemicalAffinity μ r *
            (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x) := hd
    _ = (1 / (2 * τ)) * ∑ r : N.R, N.chemicalAffinity μ r ^ 2 *
            N.massActionRate κ r x := by
          rw [hT1, hT2, hT4]
          ring
    _ = (1 / (2 * τ)) * ∑ r : N.R, κ.k r * (N.chemicalAffinity μ r)^2 *
            (N.reaction r).source.massActionMonomial x := by
          rw [hsq]

/-- **The classical sum-of-squares identity.** In units where the thermal energy is
one (`τ = 1`), the free-energy dissipation rate is exactly
`−dG/dt = ½ ∑_r κ_r A_r² x^{y_r}`. -/
theorem gibbsFreeEnergy_dissipation_eq_sum_squares_unit (N : Network S)
    (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ)
    {x : Concentration S} (hlin : N.HasLinearAffinityLaw ρ κ μ 1 x) :
    N.gibbsFreeEnergyDissipation κ μ x
      = (1 / 2 : ℝ) * ∑ r : N.R, κ.k r * (N.chemicalAffinity μ r)^2 *
          (N.reaction r).source.massActionMonomial x := by
  have h := N.gibbsFreeEnergy_dissipation_eq_sum_squares ρ κ μ hlin
  rw [h]
  norm_num

/-- **The free-energy dissipation is nonnegative.** Under the linear local detailed
balance hypothesis, `−dG/dt = (1/2τ) ∑_r κ_r A_r² x^{y_r} ≥ 0`. -/
theorem gibbsFreeEnergy_dissipation_nonneg_of_linearAffinityLaw (N : Network S)
    (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {x : Concentration S} (hx : x.Nonnegative)
    (hlin : N.HasLinearAffinityLaw ρ κ μ τ x) :
    0 ≤ N.gibbsFreeEnergyDissipation κ μ x := by
  have h := N.gibbsFreeEnergy_dissipation_eq_sum_squares ρ κ μ hlin
  rw [h]
  refine mul_nonneg (by positivity) ?_
  apply Finset.sum_nonneg
  intro r _
  have hk : 0 ≤ κ.k r := (κ.positive r).le
  have hm : 0 ≤ (N.reaction r).source.massActionMonomial x :=
    Complex.massActionMonomial_nonneg hx _
  have ha : 0 ≤ (N.chemicalAffinity μ r)^2 := sq_nonneg _
  exact mul_nonneg (mul_nonneg hk ha) hm

/-- **The free-energy dissipation is the entropy production.** With thermodynamically
consistent standard chemical potentials, the free-energy dissipation rate is `τ` times
the entropy production of leaf E1:
`−dG/dt = τ · ½ ∑_r (v_r − v_{rev(r)}) (log v_r − log v_{rev(r)})`. -/
theorem gibbsFreeEnergy_dissipation_eq_tau_entropyProduction (N : Network S)
    (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ) {τ : ℝ}
    {x : Concentration S} (hcons : N.HasConsistentChemicalPotentials ρ κ μ τ x) :
    N.gibbsFreeEnergyDissipation κ μ x = τ * N.entropyProduction ρ κ x := by
  have hd := N.gibbsFreeEnergy_dissipation_eq_affinity_netCurrent ρ κ μ x
  have hstep : ∀ r : N.R,
      N.chemicalAffinity μ r *
          (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x)
        = τ * ((N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x) *
            (Real.log (N.massActionRate κ r x)
              - Real.log (N.massActionRate κ (ρ.rev r) x))) := by
    intro r
    have h := hcons r
    rw [h]
    ring
  rw [hd]
  calc
    (1 / 2 : ℝ) * ∑ r : N.R, N.chemicalAffinity μ r *
        (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x)
        = (1 / 2 : ℝ) * ∑ r : N.R, τ *
            ((N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x) *
              (Real.log (N.massActionRate κ r x)
                - Real.log (N.massActionRate κ (ρ.rev r) x))) := by
          apply congrArg (fun t : ℝ => (1 / 2 : ℝ) * t)
          apply Finset.sum_congr rfl
          intro r _
          exact hstep r
    _ = τ * ((1 / 2 : ℝ) * ∑ r : N.R,
          (N.massActionRate κ r x - N.massActionRate κ (ρ.rev r) x) *
            (Real.log (N.massActionRate κ r x)
              - Real.log (N.massActionRate κ (ρ.rev r) x))) := by
          rw [← Finset.mul_sum]
          ring
    _ = τ * N.entropyProduction ρ κ x := by
          unfold entropyProduction reactionEntropyProduction
          rfl

/-- **The free energy does not increase along the flow.** With thermodynamically
consistent standard chemical potentials, the Gibbs free energy is nonincreasing, by
the entropy production inequality of leaf E1
(`CRNT.Network.entropyProduction_nonneg`). -/
theorem gibbsFreeEnergy_dissipation_nonneg_of_consistentChemicalPotentials (N : Network S)
    (ρ : ReversiblePairing N) (κ : RateConstants N) (μ : S → ℝ) {τ : ℝ} (hτ : 0 < τ)
    {x : Concentration S} (hx : x.Positive)
    (hcons : N.HasConsistentChemicalPotentials ρ κ μ τ x) :
    0 ≤ N.gibbsFreeEnergyDissipation κ μ x := by
  rw [N.gibbsFreeEnergy_dissipation_eq_tau_entropyProduction ρ κ μ hcons]
  exact mul_nonneg hτ.le (N.entropyProduction_nonneg ρ κ hx)

end Network

end CRNT

/-! ## A concrete instance: the isomerization `A ⇌ B`

The network `A ⇌ B` with unit rate constants is the smallest system with a
non-trivial chemical affinity.  We take the standard chemical potentials
`μ_A = 1`, `μ_B = 0`, so that the forward reaction `A → B` is thermodynamically
favoured (its affinity is `1`), and we check every hypothesis of the theorems above
explicitly:

* the affinities of the two channels;
* the rate of change of the Gibbs free energy at the state `(3, 1)`;
* the linear local detailed balance hypothesis at `(3, 1)`, and the resulting
  *sum of squares* identity `−dG/dt = ½ ∑_r κ_r A_r² x^{y_r} = 2`;
* the characterization of the P-invariants of this network: `μ' ∈ conservationLawSpace`
  exactly when `μ'_A = μ'_B`;
* the complex-balanced equilibrium `(1, 1)`, at which the free energy is stationary
  for *every* choice of standard chemical potentials;
* the entropy-production identity of leaf E1 at the state `(e, 1)`, where the standard
  chemical potentials are thermodynamically consistent. -/

namespace CRNT.Examples.GibbsIsomerization

open CRNT
open scoped BigOperators

/-- Two species, `A` and `B`. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | B => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

/-- The two reaction channels. -/
inductive Rxn
  | fwd
  | bwd
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.fwd, Rxn.bwd}
  complete := by intro r; cases r <;> simp

/-- The reaction map: `A → B` forward and `B → A` backward. -/
def rxn : Rxn → Reaction Species
  | .fwd => { source := cA, target := cB }
  | .bwd => { source := cB, target := cA }

/-- The network `A ⇌ B`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- Sums over the two species expand to a single sum. -/
theorem sum_univ_species (f : Species → ℝ) : (∑ s : Species, f s) = f A + f B := by
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Products over the two species expand to a single product. -/
theorem prod_univ_species (f : Species → ℝ) : (∏ s : Species, f s) = f A * f B := by
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_singleton]

/-- Sums over the two reaction channels expand to a single sum. -/
theorem sum_univ_rxn (f : Rxn → ℝ) : (∑ r : Rxn, f r) = f .fwd + f .bwd := by
  have huniv : (Finset.univ : Finset Rxn) = {.fwd, .bwd} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Unit rate constants for both directions. -/
def rates : Network.RateConstants N where
  k := fun _ => 1
  positive := by intro r; cases r <;> norm_num

/-- The reverse pairing of the two channels. -/
def revStruct : Network.ReversiblePairing N where
  rev := fun r => match r with | .fwd => .bwd | .bwd => .fwd
  involutive := by intro r; cases r <;> rfl
  source_rev := by intro r; cases r <;> rfl
  target_rev := by intro r; cases r <;> rfl

/-- The standard chemical potentials `μ_A = 1`, `μ_B = 0`. -/
def mu : Concentration Species := fun s => match s with | A => 1 | B => 0

/-- The state `(3, 1)`. -/
def state : Concentration Species := fun s => match s with | A => 3 | B => 1

/-- The state `(e, 1)`, at which the standard chemical potentials are thermodynamically
consistent. -/
noncomputable def expState : Concentration Species :=
  fun s => match s with | A => Real.exp 1 | B => 1

/-- The complex-balanced equilibrium `(1, 1)`. -/
def equilibrium : Concentration Species := fun _ => 1

/-- The chemical content of the complex `A`. -/
theorem complexChemicalPotential_cA (μ' : Concentration Species) :
    Network.complexChemicalPotential μ' cA = μ' A := by
  simp [Network.complexChemicalPotential, cA, sum_univ_species]

/-- The chemical content of the complex `B`. -/
theorem complexChemicalPotential_cB (μ' : Concentration Species) :
    Network.complexChemicalPotential μ' cB = μ' B := by
  simp [Network.complexChemicalPotential, cB, sum_univ_species]

/-- **The affinity of the forward channel** is `μ_A − μ_B`. -/
theorem chemicalAffinity_fwd (μ' : Concentration Species) :
    N.chemicalAffinity μ' .fwd = μ' A - μ' B := by
  simp [Network.chemicalAffinity, N, rxn, complexChemicalPotential_cA,
    complexChemicalPotential_cB]

/-- **The affinity of the backward channel** is `μ_B − μ_A`. -/
theorem chemicalAffinity_bwd (μ' : Concentration Species) :
    N.chemicalAffinity μ' .bwd = μ' B - μ' A := by
  simp [Network.chemicalAffinity, N, rxn, complexChemicalPotential_cA,
    complexChemicalPotential_cB]

/-- The forward channel of the standard chemical potentials `μ_A = 1`, `μ_B = 0` has
affinity `1`: the reaction `A → B` is thermodynamically favoured. -/
theorem chemicalAffinity_mu_fwd : N.chemicalAffinity mu .fwd = 1 := by
  rw [chemicalAffinity_fwd]
  simp [mu]

/-- The backward channel has affinity `−1`. -/
theorem chemicalAffinity_mu_bwd : N.chemicalAffinity mu .bwd = -1 := by
  rw [chemicalAffinity_bwd]
  simp [mu]

/-- The Gibbs free energy of the state `(3, 1)` at the standard chemical potentials
`μ_A = 1`, `μ_B = 0` is `3`. -/
theorem gibbsFreeEnergy_mu_state : Network.gibbsFreeEnergy mu state = 3 := by
  simp [Network.gibbsFreeEnergy, mu, state, sum_univ_species]

/-- The forward mass-action rate at `(3, 1)` is `3`. -/
theorem massActionRate_fwd_state : N.massActionRate rates .fwd state = 3 := by
  simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, state, cA,
    prod_univ_species]

/-- The backward mass-action rate at `(3, 1)` is `1`. -/
theorem massActionRate_bwd_state : N.massActionRate rates .bwd state = 1 := by
  simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, state, cB,
    prod_univ_species]

/-- The mass-action vector field at `(3, 1)` is `(−2, 2)`. -/
theorem massActionVectorField_state :
    N.massActionVectorField rates state = fun s => match s with | A => -2 | B => 2 := by
  funext s
  cases s with
  | A =>
      simp only [Network.massActionVectorField_apply]
      change (∑ r : Rxn, N.massActionRate rates r state * N.reactionVector r A) = -2
      rw [sum_univ_rxn]
      simp [Network.massActionRate, rates, N, rxn, state, cA, cB, Network.reactionVector,
        Complex.massActionMonomial, prod_univ_species]; ring
  | B =>
      simp only [Network.massActionVectorField_apply]
      change (∑ r : Rxn, N.massActionRate rates r state * N.reactionVector r B) = 2
      rw [sum_univ_rxn]
      simp [Network.massActionRate, rates, N, rxn, state, cA, cB, Network.reactionVector,
        Complex.massActionMonomial, prod_univ_species]; ring

/-- **The free-energy dissipation rate at `(3, 1)` is `2`.**  The forward channel is
favoured and its flux dominates the backward one, so the Gibbs free energy decreases. -/
theorem dissipation_at_state : N.gibbsFreeEnergyDissipation rates mu state = 2 := by
  unfold Network.gibbsFreeEnergyDissipation
  change (∑ r : Rxn, N.chemicalAffinity mu r * N.massActionRate rates r state) = 2
  rw [sum_univ_rxn]
  simp [Network.massActionRate, Network.chemicalAffinity, complexChemicalPotential_cA,
    complexChemicalPotential_cB, rates, N, rxn, state, cA, cB, mu,
    Complex.massActionMonomial, prod_univ_species]; ring

/-- Equivalently, the rate of change of the Gibbs free energy at `(3, 1)` is `−2`. -/
theorem rateOfChange_at_state :
    (∑ s, mu s * N.massActionVectorField rates state s) = -2 := by
  have h := N.gibbsFreeEnergy_dissipation_eq_neg_rate rates mu state
  rw [dissipation_at_state] at h
  linarith

/-- **Linear local detailed balance holds at `(3, 1)`.**  The net current `3 − 1 = 2` is
the affinity `1` times the average flux `(3 + 1)/2`. -/
theorem linearAffinityLaw_at_state :
    N.HasLinearAffinityLaw revStruct rates mu 1 state := by
  intro r
  cases r with
  | fwd =>
      simp [revStruct, massActionRate_fwd_state, massActionRate_bwd_state,
        chemicalAffinity_mu_fwd]; ring
  | bwd =>
      simp [revStruct, massActionRate_fwd_state, massActionRate_bwd_state,
        chemicalAffinity_mu_bwd]; ring

/-- **The sum of the squares of the affinities, evaluated directly.**  At `(3, 1)` it is
`1·1²·3 + 1·1²·1 = 4`. -/
theorem sum_of_affinity_squares_at_state :
    (∑ r : N.R, rates.k r * (N.chemicalAffinity mu r)^2 *
        (N.reaction r).source.massActionMonomial state) = 4 := by
  change (∑ r : Rxn, rates.k r * (N.chemicalAffinity mu r)^2 *
        (N.reaction r).source.massActionMonomial state) = 4
  rw [sum_univ_rxn]
  simp [Network.chemicalAffinity, complexChemicalPotential_cA,
    complexChemicalPotential_cB, rates, N, rxn, state, cA, cB, mu,
    Complex.massActionMonomial, prod_univ_species]; ring

/-- **The sum of the squares of the affinities.**  At `(3, 1)` the dissipation rate is
`½ (1·1²·3 + 1·1²·1) = 2`, exactly the value computed directly. -/
theorem sum_of_squares_at_state :
    (1 / 2 : ℝ) * ∑ r : N.R, rates.k r * (N.chemicalAffinity mu r)^2 *
        (N.reaction r).source.massActionMonomial state = 2 := by
  have h := N.gibbsFreeEnergy_dissipation_eq_sum_squares_unit revStruct rates mu
    linearAffinityLaw_at_state
  rw [dissipation_at_state] at h
  linarith [h]

/-- **The dissipation is nonnegative at `(3, 1)`.** -/
theorem dissipation_nonneg_at_state : 0 ≤ N.gibbsFreeEnergyDissipation rates mu state := by
  rw [dissipation_at_state]
  norm_num

/-- **The P-invariants of this network.**  A vector of standard chemical potentials is a
conservation law exactly when its two components agree. -/
theorem conservationLaw_iff_eq (μ' : Concentration Species) :
    μ' ∈ N.conservationLawSpace ↔ μ' A = μ' B := by
  have hiff := N.chemicalAffinity_eq_zero_iff_conservationLaw μ'
  constructor
  · intro hc
    have hz : ∀ r : N.R, N.chemicalAffinity μ' r = 0 := hiff.mpr hc
    have h' : N.chemicalAffinity μ' .fwd = 0 := hz .fwd
    rw [chemicalAffinity_fwd] at h'
    linarith
  · intro h
    refine hiff.mp ?_
    intro r
    cases r with
    | fwd => rw [chemicalAffinity_fwd, h]; ring
    | bwd => rw [chemicalAffinity_bwd, h]; ring

/-- The standard chemical potentials `μ_A = 1`, `μ_B = 0` are **not** a conservation law:
the Gibbs free energy is not conserved, it decreases along the flow. -/
theorem mu_not_conservationLaw : mu ∉ N.conservationLawSpace := by
  rw [conservationLaw_iff_eq]
  simp [mu]

/-- **The equilibrium `(1, 1)` is complex balanced.**  At `(1, 1)` every complex has
inflow equal to outflow. -/
theorem equilibrium_isComplexBalanced : N.IsComplexBalanced rates equilibrium := by
  intro c hc
  have hcomplexes : N.complexes = {cA, cB} := by decide
  rw [hcomplexes] at hc
  simp only [Finset.mem_insert, Finset.mem_singleton] at hc
  rcases hc with rfl | rfl
  · rw [Network.inflow, Network.outflow]
    change
      (∑ r : Rxn, (if (N.reaction r).target = cA then N.massActionRate rates r equilibrium
        else 0))
        = (∑ r : Rxn, (if (N.reaction r).source = cA then N.massActionRate rates r equilibrium
          else 0))
    rw [sum_univ_rxn, sum_univ_rxn]
    simp [Network.massActionRate, rates, N, rxn, equilibrium, cA, cB,
      Complex.massActionMonomial]; ring
  · rw [Network.inflow, Network.outflow]
    change
      (∑ r : Rxn, (if (N.reaction r).target = cB then N.massActionRate rates r equilibrium
        else 0))
        = (∑ r : Rxn, (if (N.reaction r).source = cB then N.massActionRate rates r equilibrium
          else 0))
    rw [sum_univ_rxn, sum_univ_rxn]
    simp [Network.massActionRate, rates, N, rxn, equilibrium, cA, cB,
      Complex.massActionMonomial]; ring

/-- **The Gibbs free energy is stationary at the complex-balanced equilibrium**, for every
choice of standard chemical potentials. -/
theorem stationary_at_equilibrium (μ' : Concentration Species) :
    (∑ s, μ' s * N.massActionVectorField rates equilibrium s) = 0 :=
  N.gibbsFreeEnergy_stationary_at_complexBalanced rates μ' equilibrium_isComplexBalanced

/-- **The network affinity vanishes at the complex-balanced equilibrium.** -/
theorem networkAffinity_zero_at_equilibrium :
    (∑ r : N.R, N.chemicalAffinity mu r * N.massActionRate rates r equilibrium) = 0 :=
  N.networkAffinity_eq_zero_of_complexBalanced rates mu equilibrium_isComplexBalanced

/-- The forward mass-action rate at `(e, 1)` is `e`. -/
theorem massActionRate_fwd_expState : N.massActionRate rates .fwd expState = Real.exp 1 := by
  simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, expState, cA,
    prod_univ_species]

/-- The backward mass-action rate at `(e, 1)` is `1`. -/
theorem massActionRate_bwd_expState : N.massActionRate rates .bwd expState = 1 := by
  simp [Network.massActionRate, Complex.massActionMonomial, rates, N, rxn, expState, cB,
    prod_univ_species]

/-- **The standard chemical potentials are thermodynamically consistent at `(e, 1)`.**  The
affinity `1` is the logarithm of the flux ratio `e / 1`. -/
theorem consistentChemicalPotentials_at_expState :
    N.HasConsistentChemicalPotentials revStruct rates mu 1 expState := by
  intro r
  cases r with
  | fwd =>
      simp [revStruct, massActionRate_fwd_expState,
        massActionRate_bwd_expState, chemicalAffinity_mu_fwd, Real.log_exp]
  | bwd =>
      simp [revStruct, massActionRate_fwd_expState,
        massActionRate_bwd_expState, chemicalAffinity_mu_bwd, Real.log_exp]

/-- **The free-energy dissipation is the entropy production of leaf E1.**  At `(e, 1)` the
dissipation rate is `e − 1`. -/
theorem dissipation_at_expState :
    N.gibbsFreeEnergyDissipation rates mu expState
      = Network.entropyProduction N revStruct rates expState := by
  have h := N.gibbsFreeEnergy_dissipation_eq_tau_entropyProduction revStruct rates mu
    consistentChemicalPotentials_at_expState
  rw [h]
  ring

/-- **The entropy production of leaf E1 is nonnegative here, and so is the
free-energy dissipation.** -/
theorem dissipation_nonneg_at_expState :
    0 ≤ N.gibbsFreeEnergyDissipation rates mu expState := by
  refine N.gibbsFreeEnergy_dissipation_nonneg_of_consistentChemicalPotentials revStruct
    rates mu (by norm_num) ?_ consistentChemicalPotentials_at_expState
  intro s
  cases s with
  | A => exact Real.exp_pos _
  | B => simp [expState]

end CRNT.Examples.GibbsIsomerization
