import CRNT

open CRNT
open CRNT.Network
open scoped BigOperators NNReal

namespace SemanticAudit

-- This deliberately asks for existence as well as convergence, without an ambient
-- mass-action flow from negative initial concentrations.
theorem complexBalanced_exists_convergent_solution
    {S : Type} [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    {xstar x₀ : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hx₀ : x₀.Positive)
    (hc : N.StoichCompatible x₀ xstar) :
    ∃ Γ : ℝ → Concentration S, Γ 0 = x₀ ∧
      (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField κ (Γ t)) t) ∧
      Filter.Tendsto Γ Filter.atTop (nhds xstar) := by
  let C := relEntropy xstar x₀
  let B := 1 + |C| + ∑ s, Real.exp 2 * xstar s
  have hsum : 0 ≤ ∑ s, Real.exp 2 * xstar s :=
    Finset.sum_nonneg fun s _ => (mul_pos (Real.exp_pos 2) (hxs s)).le
  have hB : 0 ≤ B := by dsimp [B]; linarith [abs_nonneg C]
  have hbig : ∀ s, max (Real.exp 2 * xstar s) C < B := by
    intro s
    have hs : Real.exp 2 * xstar s ≤ ∑ s', Real.exp 2 * xstar s' :=
      Finset.single_le_sum (fun s' _ => (mul_pos (Real.exp_pos 2) (hxs s')).le)
        (Finset.mem_univ s)
    rw [max_lt_iff]
    dsimp [B]
    exact ⟨by linarith [abs_nonneg C], by linarith [le_abs_self C]⟩
  obtain ⟨L, hL, hlower⟩ := N.exists_field_lower_bound κ B
  obtain ⟨_, _, hlip, hbound⟩ := N.exists_cutoff κ hB
  obtain ⟨ϕ, γ, hzero, hderiv, hflow⟩ := ODE.exists_flow hlip hbound
  have hd : ∀ t, HasDerivAt (γ x₀)
      (N.massActionVectorField κ (clampBox B (γ x₀ t))) t := hderiv x₀
  have hp : ∀ t, 0 ≤ t → Concentration.Positive (γ x₀ t) :=
    orbit_pos N κ hB hL hlower (by simpa [hzero] using hx₀) hd
  have hsub : ∀ t, 0 ≤ t → relEntropy xstar (γ x₀ t) ≤ C := by
    intro t ht
    simpa [hzero, C] using orbit_relEntropy_le N κ hxs hcb hp hd
      (by simpa [hzero, C] using hbig) t ht
  have hsol : ∀ t, 0 ≤ t → HasDerivAt (γ x₀)
      (N.massActionVectorField κ (γ x₀ t)) t := by
    intro t ht
    have heq := clampBox_eq_of_sublevel hxs (hp t ht).nonnegative (hsub t ht) hbig
    simpa [heq] using hd t
  refine ⟨γ x₀, hzero x₀, hsol, ?_⟩
  exact N.complexBalanced_trajectory_converges κ hxs hcb (γ x₀)
    (by simpa [hzero] using hx₀) (by simpa [hzero] using hc) hsol

-- Regression witness: the removed one-operator all-time contract forced identity.
theorem allTimeRegraph_forces_identity
    {Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE.CoupledFlowGraphTransform Y E)
    (h : ∀ t σ, Set.MapsTo (F.flow.toFun t) (ODE.graphSet σ) (ODE.graphSet (F.op σ))) :
    F.op = id := by
  funext σ y
  have hp := h 0 σ (ODE.graphMap_mem_graphSet σ y)
  simpa [ODE.graphSet, ODE.graphMap] using hp.symm

-- Classical semilinear-graph functions include division; PiecewiseNatAffine does not.
theorem half_not_repo_piecewiseNatAffine :
    ¬ Computation.PiecewiseNatAffine (fun x : Fin 1 → ℕ => x 0 / 2) := by
  rintro ⟨pieces, hpieces⟩
  let C := (pieces.map (fun p => p.2.const)).sum
  obtain ⟨p, hp, _, heq⟩ := hpieces (fun _ => 2 * (C + 1))
  have hc : p.2.const ≤ C := by
    exact List.single_le_sum (fun _ _ => Nat.zero_le _) _
      (List.mem_map.mpr ⟨p, hp, rfl⟩)
  have hv : C + 1 = p.2.const + p.2.coeff 0 * (2 * (C + 1)) := by
    simpa [Computation.Affine.eval] using heq
  by_cases hzero : p.2.coeff 0 = 0
  · simp [hzero] at hv
    omega
  · have hge : 1 ≤ p.2.coeff 0 := Nat.one_le_iff_ne_zero.mpr hzero
    have hmul := Nat.mul_le_mul_right (2 * (C + 1)) hge
    omega

namespace Parity

def N : Network (Fin 1) where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => ⟨fun _ => 2, fun _ => 3⟩

def rates : N.fullyOpen.RateConstants where
  k := fun r => match r with
    | .inl _ => 2
    | .inr (.inl _) => 1
    | .inr (.inr _) => 3
  positive := by intro r; rcases r with r | (s | s) <;> norm_num

theorem field (x : Concentration (Fin 1)) :
    N.fullyOpen.massActionVectorField rates x 0 = 2 * (x 0)^2 - 3 * x 0 + 1 := by
  simp [Network.massActionVectorField_apply, Network.massActionRate,
    Network.reactionVector_apply, Complex.massActionMonomial, rates,
    Network.fullyOpen,
    inflowReaction, outflowReaction, N]
  ring

theorem steady_iff (x : Concentration (Fin 1)) :
    N.fullyOpen.IsMassActionSteadyState rates x ↔ x 0 = 1 ∨ x 0 = 1 / 2 := by
  have hf : 2 * (x 0)^2 - 3 * x 0 + 1 = (x 0 - 1) * (2 * x 0 - 1) := by ring
  constructor
  · intro h
    have hz := h 0
    rw [field, hf, mul_eq_zero] at hz
    rcases hz with h | h
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · intro h s
    fin_cases s
    change N.fullyOpen.massActionVectorField rates x 0 = 0
    rw [field]
    rcases h with h | h <;> rw [h] <;> norm_num

theorem exactly_two_positive_steady_states :
    {x : Concentration (Fin 1) | x.Positive ∧ N.fullyOpen.IsMassActionSteadyState rates x} =
      {fun _ => 1, fun _ => 1 / 2} := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, h⟩
    rcases (steady_iff x).mp h with h | h
    · left; funext s; fin_cases s; exact h
    · right; funext s; fin_cases s; exact h
  · rintro (rfl | rfl) <;>
      exact ⟨by intro s; norm_num, (steady_iff _).mpr (by simp)⟩

theorem positive_steady_state_count_eq_two :
    {x : Concentration (Fin 1) | x.Positive ∧
      N.fullyOpen.IsMassActionSteadyState rates x}.ncard = 2 := by
  rw [exactly_two_positive_steady_states]
  have hne : (fun _ : Fin 1 => (1 : ℝ)) ≠ (fun _ => (1 : ℝ) / 2) := by
    intro h
    have := congrFun h 0
    norm_num at this
  exact Set.ncard_pair hne

end Parity

namespace Autocatalysis

def N : Network (Fin 1) where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => ⟨fun _ => 1, fun _ => 2⟩

theorem repo_SingletonSource : N.SingletonSource := by
  intro r
  refine ⟨0, ?_⟩
  constructor
  · rfl
  · intro s hs
    fin_cases s
    exact (hs rfl).elim

theorem not_conservative : ¬ N.IsConservative := by
  rintro ⟨w, hwinv, hw⟩
  have hv := (mem_orthSum.mp hwinv) (N.reactionVector (show N.R from (0 : Fin 1)))
    (N.reactionVector_mem_stoichSubspace (show N.R from (0 : Fin 1)))
  have hν : N.reactionVector (show N.R from (0 : Fin 1)) 0 = 1 := by
    change ((2 : ℕ) : ℝ) - ((1 : ℕ) : ℝ) = 1
    norm_num
  have hz : w 0 = 0 := by
    simpa only [Fin.sum_univ_one, hν, mul_one] using hv
  exact (hw 0).ne' hz

end Autocatalysis

namespace Division

def N : Network (Fin 2) where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => ⟨![2, 0], ![0, 1]⟩

def init (n : ℕ) : Computation.Config (Fin 2) := ![n, 0]

theorem computes_half : Computation.StablyComputes N init 1 (fun n => n / 2) := by
  apply Computation.stablyComputes_of_terminating N init 1 (fun n => n / 2)
    (fun c => c 0)
  · rintro c c' ⟨r, hr, rfl⟩
    have h := hr 0
    simp only [N, Matrix.cons_val_zero] at h
    simp [Computation.fire, N]
    omega
  · intro n c hc ht
    have hinv : c 0 + 2 * c 1 = n := by
      apply Computation.reach_invariant N (fun c => c 0 + 2 * c 1 = n) ?_ hc ?_
      · rintro a b ⟨r, hr, rfl⟩ hi
        have h := hr 0
        simp only [N, Matrix.cons_val_zero] at h
        simp [Computation.fire, N]
        omega
      · simp [init]
    have hsmall : c 0 < 2 := by
      by_contra h
      apply ht (show N.R from (0 : Fin 1))
      intro s
      fin_cases s
      · change 2 ≤ c 0
        omega
      · change 0 ≤ c 1
        omega
    omega

end Division

-- The exponentially attracting scalar ODE x'=-x is strongly order preserving,
-- but cannot satisfy the coercive, increasing-field predicate used in LaSalleConvergence.
theorem degradation_fails_repo_strong_monotonicity {c : ℝ} (hc : 0 < c) :
    ¬ CRNT.OrderPreservingStronglyMonotoneOperator (fun x : Concentration (Fin 1) => -x) c := by
  intro h
  have hb := h.2 (fun _ => 0) (fun _ => 1)
  simp [CRNT.euclideanSqNorm, CRNT.euclideanInner] at hb
  linarith

namespace TimeIndexedGraph

noncomputable def family : ODE.FlowGraphTransformFamily ℝ ℝ :=
  ODE.contractingGraphTransformFamily 1 0

example (σ : ℝ → ℝ) : family.op 0 σ = σ := family.op_zero σ

-- Positive-time contraction is compatible with the corrected all-time API.
theorem time_one_not_identity : family.op 1 ≠ id := by
  intro h
  have heq := congrFun (congrFun h (fun _ => 1)) 0
  have hexp : Real.exp (-1) = 1 := by
    simpa [family, ODE.contractingGraphTransformFamily, ODE.contractRegraph] using heq
  have hbad := Real.exp_injective (hexp.trans Real.exp_zero.symm)
  norm_num at hbad

theorem common_graph_invariant :
    IsInvariant family.flow.toFun (ODE.graphSet (fun _ => (0 : ℝ))) :=
  ODE.contracting_graph_invariant_allTime 1 0

end TimeIndexedGraph

namespace NullChannel

def N : Network (Fin 1) where
  R := Fin 1
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ => ⟨0, 0⟩

theorem absorbing (n : Fin 1 → ℕ) : N.IsAbsorbingCount n := by
  rw [N.isAbsorbingCount_iff]
  intro r _
  rfl

theorem not_deadlocked (n : Fin 1 → ℕ) : ¬ N.IsDeadlockedCount n := by
  intro h
  apply h (show N.R from (0 : Fin 1))
  intro s
  exact Nat.zero_le (n s)

theorem all_reachable_eq (n m : Fin 1 → ℕ) (h : N.CountReachable n m) : m = n :=
  N.reachable_eq_of_absorbing (absorbing n) h

end NullChannel

-- Exercise the stronger boundary conclusion, while the old positive-class API remains available.
example {S : Type} [DecidableEq S] [Fintype S] (N : Network S)
    (hN : N.Concordant) (K : N.Kinetics) (hK : K.WeaklyMonotonic)
    {x : Concentration S} (hx : x.Positive) (hmem : x ∈ N.stoichSubspace)
    (hf : K.vectorField 0 = K.vectorField x) : (0 : Concentration S) = x := by
  apply CRNT.Network.Concordant.boundaryInjective_of_weaklyMonotonic hN hK
    (by intro s; exact le_refl 0) hx.nonnegative (Or.inr hx) _ hf
  simpa using hmem

example (μ : ℝ) :
    CRNT.Examples.HopfPlanar2.N.IsMassActionSteadyState
      (CRNT.Examples.HopfPlanar2.κ μ)
      (CRNT.Examples.HopfPlanar2.xst μ) :=
  CRNT.Examples.HopfPlanar2.hopfData.steady_state μ

end SemanticAudit

/-- info: 'SemanticAudit.complexBalanced_exists_convergent_solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.complexBalanced_exists_convergent_solution

/-- info: 'SemanticAudit.allTimeRegraph_forces_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.allTimeRegraph_forces_identity

/-- info: 'SemanticAudit.half_not_repo_piecewiseNatAffine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.half_not_repo_piecewiseNatAffine

/-- info: 'SemanticAudit.Division.computes_half' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.Division.computes_half

/-- info: 'SemanticAudit.Parity.positive_steady_state_count_eq_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.Parity.positive_steady_state_count_eq_two

/-- info: 'SemanticAudit.Autocatalysis.not_conservative' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.Autocatalysis.not_conservative

/-- info: 'SemanticAudit.degradation_fails_repo_strong_monotonicity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.degradation_fails_repo_strong_monotonicity

/-- info: 'SemanticAudit.TimeIndexedGraph.time_one_not_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.TimeIndexedGraph.time_one_not_identity

/-- info: 'SemanticAudit.NullChannel.absorbing' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.NullChannel.absorbing

/-- info: 'SemanticAudit.NullChannel.not_deadlocked' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SemanticAudit.NullChannel.not_deadlocked
