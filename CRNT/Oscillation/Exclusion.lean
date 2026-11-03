import CRNT.Oscillation.Basic
import CRNT.Theorems.DeficiencyZero.NoPeriodicOrbit
import CRNT.Kinetics.General
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Connected.Clopen

/-!
# Sound exclusion of periodic mass-action oscillations

This module turns existing convergence/Lyapunov theory into the common oscillation API.

The first result promotes the deficiency-zero theorem already present in `crnt-lean` to a structural
certificate: every weakly reversible deficiency-zero network is `NeverPositivePeriodic`, i.e. no
positive rate constants can produce a nonconstant positive periodic orbit.

The second result is a reusable Lyapunov pattern.  If an observable is antitone along a periodic
trajectory and equality with its initial value can occur only at the initial state, periodicity
forces a contradiction with nonconstancy.  Network-specific Lyapunov functions can discharge these
hypotheses without rebuilding the periodic-orbit argument.
-/

namespace CRNT

open Filter Topology

/-- **Periodic + convergent implies constant.** A function on real time with a strictly positive
period cannot converge to a single point at `+∞` unless every phase already equals that point.

The proof samples the trajectory at `t + nT`.  Periodicity makes this sampled sequence constant,
while `T > 0` sends the sampling times to `+∞`; uniqueness of limits then identifies that constant
with the asymptotic limit. -/
theorem periodic_eq_limit_of_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ℝ → E} {T : ℝ} (hT : 0 < T) (hper : Function.Periodic f T)
    {xstar : E} (hlim : Tendsto f atTop (𝓝 xstar)) :
    ∀ t : ℝ, f t = xstar := by
  intro t
  have hmul : Tendsto (fun n : ℕ => T * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hT (tendsto_natCast_atTop_atTop (R := ℝ))
  have htimes : Tendsto (fun n : ℕ => t + (n : ℝ) * T) atTop atTop := by
    have hadd := tendsto_atTop_add_const_right atTop t hmul
    simpa [mul_comm, add_comm] using hadd
  have hsample : Tendsto (fun n : ℕ => f (t + (n : ℝ) * T)) atTop (𝓝 xstar) :=
    hlim.comp htimes
  have hfun : (fun n : ℕ => f (t + (n : ℝ) * T)) = (fun _ : ℕ => f t) := by
    funext n
    exact (hper.nat_mul n) t
  rw [hfun] at hsample
  exact (tendsto_nhds_unique hsample tendsto_const_nhds).symm

/-- A nonconstant periodic trajectory therefore cannot converge to a point at `+∞`. -/
theorem not_periodicTrajectory_of_tendsto_atTop
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) {xstar : E}
    (hlim : Tendsto P.orbit atTop (𝓝 xstar)) : False := by
  have hall := periodic_eq_limit_of_tendsto_atTop P.period_pos P.periodic hlim
  obtain ⟨t, ht⟩ := P.nonconstant
  exact ht ((hall t).trans (hall 0).symm)

/-- **A locally unique autonomous trajectory cannot pass through an equilibrium and leave it.**
If the vector field is locally Lipschitz and a global exact solution reaches a state where the field
vanishes, then that solution is constant for all real time.  The proof uses local ODE uniqueness to
show that the set of times at which the trajectory equals the equilibrium is open; continuity makes
the same set closed, and connectedness of `ℝ` makes it all of time.

This is deliberately stated at the trajectory level, so any later CRN argument that produces an
equilibrium point on a putative cycle can reuse the same uniqueness bridge. -/
theorem PeriodicTrajectory.orbit_eq_equilibrium_of_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (hfield : LocallyLipschitz field)
    {t₀ : ℝ} (heq : field (P.orbit t₀) = 0) :
    ∀ t : ℝ, P.orbit t = P.orbit t₀ := by
  let xstar : E := P.orbit t₀
  let A : Set ℝ := P.orbit ⁻¹' ({xstar} : Set E)
  have horbit_cont : Continuous P.orbit :=
    continuous_iff_continuousAt.2 fun t => (P.solution t).continuousAt
  have hclosed : IsClosed A := by
    exact IsClosed.preimage horbit_cont isClosed_singleton
  have heq' : field xstar = 0 := by
    simpa [xstar] using heq
  have hopen : IsOpen A := by
    rw [isOpen_iff_mem_nhds]
    intro t ht
    have ht' : P.orbit t = xstar := by
      simpa [A] using ht
    obtain ⟨K, U, hU, hLip⟩ := hfield xstar
    have hxU : xstar ∈ U := mem_of_mem_nhds hU
    have horbitU : ∀ᶠ u in 𝓝 t, P.orbit u ∈ U := by
      have htend : Tendsto P.orbit (𝓝 t) (𝓝 xstar) := by
        have hc : ContinuousAt P.orbit t := (P.solution t).continuousAt
        rw [ContinuousAt, ht'] at hc
        exact hc
      exact htend hU
    have hv : ∀ᶠ u in 𝓝 t,
        LipschitzOnWith K ((fun _ : ℝ => field) u) U :=
      Filter.Eventually.of_forall fun _ => hLip
    have hf : ∀ᶠ u in 𝓝 t,
        HasDerivAt P.orbit ((fun _ : ℝ => field) u (P.orbit u)) u ∧ P.orbit u ∈ U := by
      filter_upwards [horbitU] with u hu
      exact ⟨P.solution u, hu⟩
    let c : ℝ → E := fun _ => xstar
    have hg : ∀ᶠ u in 𝓝 t,
        HasDerivAt c ((fun _ : ℝ => field) u (c u)) u ∧ c u ∈ U :=
      Filter.Eventually.of_forall fun u => by
        constructor
        · simpa [c, heq'] using (hasDerivAt_const u xstar)
        · simpa [c] using hxU
    have huniq : P.orbit =ᶠ[𝓝 t] c :=
      ODE_solution_unique_of_eventually (v := fun _ : ℝ => field) (s := fun _ => U)
        hv hf hg (by simpa [c] using ht')
    show A ∈ 𝓝 t
    filter_upwards [huniq] with u hu
    simpa [A, c] using hu
  have hclopen : IsClopen A := ⟨hclosed, hopen⟩
  have hA : A = Set.univ := hclopen.eq_univ ⟨t₀, by simp [A, xstar]⟩
  intro t
  have htA : t ∈ A := by rw [hA]; exact Set.mem_univ t
  simpa [A, xstar] using htA

/-- A locally Lipschitz periodic trajectory that contains an equilibrium contradicts its required
nonconstancy. -/
theorem not_periodicTrajectory_of_equilibrium_of_locallyLipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (hfield : LocallyLipschitz field)
    {t₀ : ℝ} (heq : field (P.orbit t₀) = 0) : False := by
  obtain ⟨t, ht⟩ := P.nonconstant
  have hall := P.orbit_eq_equilibrium_of_locallyLipschitz hfield heq
  exact ht ((hall t).trans (hall 0).symm)

/-- **Zero-field exclusion.** An exact solution of the identically zero autonomous vector field is
constant, so it cannot satisfy the nonconstancy requirement of `PeriodicTrajectory`.  This tiny
lemma is useful for zero-dimensional stoichiometric classes and any later reduction that collapses
the induced dynamics to the zero field. -/
theorem not_periodicTrajectory_of_field_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field)
    (hfield : ∀ x : E, field x = 0) : False := by
  have hderiv : ∀ t : ℝ, HasDerivAt P.orbit 0 t := by
    intro t
    have hsol := P.solution t
    rw [hfield (P.orbit t)] at hsol
    exact hsol
  have hdiff : Differentiable ℝ P.orbit := fun t => (hderiv t).differentiableAt
  have hzero : ∀ t : ℝ, deriv P.orbit t = 0 := fun t => (hderiv t).deriv
  obtain ⟨t, ht⟩ := P.nonconstant
  exact ht (is_const_of_deriv_eq_zero hdiff hzero t 0)

/-- **Strictly monotone observable exclusion.** A positive-period periodic trajectory cannot carry
a scalar observable that is strictly monotone in time.  This is the lightest-weight global
non-oscillation certificate: no differentiability or Lyapunov construction is needed once a
strictly one-way observable has been established. -/
theorem not_periodicTrajectory_of_strictMono_observable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (V : E → ℝ)
    (hmono : StrictMono (fun t => V (P.orbit t))) : False := by
  have hlt : V (P.orbit 0) < V (P.orbit P.period) := hmono P.period_pos
  rw [P.closes] at hlt
  exact (lt_irrefl _ hlt)

/-- Strictly decreasing observables exclude periodic trajectories as well. -/
theorem not_periodicTrajectory_of_strictAnti_observable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (V : E → ℝ)
    (hanti : StrictAnti (fun t => V (P.orbit t))) : False := by
  have hlt : V (P.orbit P.period) < V (P.orbit 0) := hanti P.period_pos
  rw [P.closes] at hlt
  exact (lt_irrefl _ hlt)

/-- **Generic strict-Lyapunov exclusion.** An exact periodic trajectory cannot coexist with an
observable that is antitone along the trajectory and whose initial level is attained only at the
initial state. -/
theorem not_periodicTrajectory_of_strictLyapunov
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (V : E → ℝ)
    (hanti : Antitone (fun t => V (P.orbit t)))
    (hstrict : ∀ t, V (P.orbit t) = V (P.orbit 0) → P.orbit t = P.orbit 0) : False := by
  have hVper : Function.Periodic (fun t => V (P.orbit t)) P.period := by
    intro t
    dsimp only
    rw [P.periodic t]
  have hconstV : ∀ x y, V (P.orbit x) = V (P.orbit y) :=
    eq_of_antitone_periodic P.period_pos hanti hVper
  obtain ⟨t, ht⟩ := P.nonconstant
  exact ht (hstrict t (hconstV t 0))



/-- **Derivative-form Lyapunov exclusion.** If a differentiable observable is nonincreasing along a
periodic trajectory and has strictly negative derivative at at least one point, the trajectory cannot
be periodic.  This is often easier for CRN applications than proving a state-separating Lyapunov
level-set condition: one supplies the chain-rule derivative and a single strict-dissipation witness. -/
theorem not_periodicTrajectory_of_lyapunov_derivative_negative_somewhere
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {field : E → E} (P : PeriodicTrajectory field) (V : E → ℝ) (dV : ℝ → ℝ)
    (hderiv : ∀ t, HasDerivAt (fun τ => V (P.orbit τ)) (dV t) t)
    (hnonpos : ∀ t, dV t ≤ 0)
    (hneg : ∃ t, dV t < 0) : False := by
  have hanti : Antitone (fun t => V (P.orbit t)) :=
    antitone_of_deriv_nonpos (fun t => (hderiv t).differentiableAt) fun t => by
      rw [(hderiv t).deriv]
      exact hnonpos t
  have hVper : Function.Periodic (fun t => V (P.orbit t)) P.period := by
    intro t
    dsimp only
    rw [P.periodic t]
  have hconst : ∀ x y, V (P.orbit x) = V (P.orbit y) :=
    eq_of_antitone_periodic P.period_pos hanti hVper
  obtain ⟨t, ht⟩ := hneg
  have hzeroDeriv : HasDerivAt (fun τ => V (P.orbit τ)) 0 t := by
    have heq : (fun τ => V (P.orbit τ)) = fun _ => V (P.orbit t) := by
      funext u
      exact hconst u t
    rw [heq]
    exact hasDerivAt_const t _
  have : dV t = 0 := (hderiv t).unique hzeroDeriv
  linarith

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Rank zero means the stoichiometric subspace itself is trivial. -/
theorem stoichSubspace_eq_bot_of_stoichRank_zero (N : Network S)
    (h0 : N.stoichRank = 0) : N.stoichSubspace = ⊥ := by
  apply Submodule.finrank_eq_zero.mp
  simpa [Network.stoichRank] using h0

/-- Every admissible-kinetics vector field vanishes identically on a rank-zero network.  This is
kinetics-independent: the field always lies in the stoichiometric subspace, which is `{0}` here. -/
theorem Kinetics.vectorField_eq_zero_of_stoichRank_zero
    {N : Network S} (K : N.Kinetics) (h0 : N.stoichRank = 0) :
    ∀ x : Concentration S, K.vectorField x = 0 := by
  intro x
  have hmem := K.vectorField_mem_stoichSubspace x
  rw [N.stoichSubspace_eq_bot_of_stoichRank_zero h0] at hmem
  simpa using hmem

/-- In particular, the mass-action vector field of a rank-zero network is identically zero for
every positive rate vector. -/
theorem massActionVectorField_eq_zero_of_stoichRank_zero
    (N : Network S) (h0 : N.stoichRank = 0) (κ : N.RateConstants) :
    ∀ x : Concentration S, N.massActionVectorField κ x = 0 := by
  intro x
  have h := (N.massActionKinetics κ).vectorField_eq_zero_of_stoichRank_zero h0 x
  simpa [N.massActionKinetics_vectorField κ] using h

/-- **Rank-zero structural non-oscillation.** If the stoichiometric compatibility classes are
zero-dimensional, every mass-action vector field is zero and hence every exact trajectory is
constant.  This excludes positive periodic orbits for *all* positive rate constants, independently
of weak reversibility or deficiency. -/
theorem neverPositivePeriodic_of_stoichRank_zero
    (N : Network S) (h0 : N.stoichRank = 0) : N.NeverPositivePeriodic := by
  intro κ hperiodic
  obtain ⟨P⟩ := hperiodic
  exact not_periodicTrajectory_of_field_eq_zero P.toPeriodicTrajectory
    (N.massActionVectorField_eq_zero_of_stoichRank_zero h0 κ)

/-- Capacity form of the rank-zero exclusion theorem. -/
theorem not_oscillatoryCapacity_of_stoichRank_zero
    (N : Network S) (h0 : N.stoichRank = 0) : ¬ N.OscillatoryCapacity :=
  (N.neverPositivePeriodic_iff_not_oscillatoryCapacity).mp
    (N.neverPositivePeriodic_of_stoichRank_zero h0)

/-- If every positive periodic-orbit candidate at a fixed parameterization is known to converge to
some point, then no positive periodic orbit exists.  This is the adapter from global-convergence
results to the fixed-parameter oscillation API. -/
theorem not_hasPositivePeriodicOrbit_of_every_candidate_tendsto
    {N : Network S} {κ : N.RateConstants}
    (hconv : ∀ P : N.PositivePeriodicOrbit κ,
      ∃ xstar : Concentration S, Tendsto P.orbit atTop (𝓝 xstar)) :
    ¬ N.HasPositivePeriodicOrbit κ := by
  intro hperiodic
  obtain ⟨P⟩ := hperiodic
  obtain ⟨xstar, hlim⟩ := hconv P
  exact not_periodicTrajectory_of_tendsto_atTop P.toPeriodicTrajectory hlim

/-- If the preceding convergence property holds for every positive rate vector, the network is
structurally non-oscillatory. -/
theorem neverPositivePeriodic_of_every_candidate_tendsto
    (N : Network S)
    (hconv : ∀ κ : N.RateConstants, ∀ P : N.PositivePeriodicOrbit κ,
      ∃ xstar : Concentration S, Tendsto P.orbit atTop (𝓝 xstar)) :
    N.NeverPositivePeriodic := by
  intro κ
  exact not_hasPositivePeriodicOrbit_of_every_candidate_tendsto (hconv κ)

/-- **Weakly reversible deficiency-zero networks never sustain a positive periodic orbit.**

This is a structural, all-parameter statement.  The existing Horn--Jackson relative-entropy proof
`eq_of_periodic_solution` shows that every positive periodic solution is constant; packaging the
same theorem through `NeverPositivePeriodic` makes it usable by generic oscillation tooling. -/
theorem neverPositivePeriodic_of_weaklyReversible_deficiencyZero
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) :
    N.NeverPositivePeriodic := by
  intro κ hperiodic
  obtain ⟨P⟩ := hperiodic
  obtain ⟨t, ht⟩ := P.nonconstant
  have hconst : ∀ u, P.orbit u = P.orbit 0 :=
    N.eq_of_periodic_solution hwr hδ κ P.period_pos P.positive P.solution P.periodic
  exact ht (hconst t)

/-- Equivalent capacity form of the deficiency-zero exclusion theorem. -/
theorem not_oscillatoryCapacity_of_weaklyReversible_deficiencyZero
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyZero) :
    ¬ N.OscillatoryCapacity :=
  (N.neverPositivePeriodic_iff_not_oscillatoryCapacity).mp
    (N.neverPositivePeriodic_of_weaklyReversible_deficiencyZero hwr hδ)

end Network

end CRNT
