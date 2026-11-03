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

-- The all-time regraph predicate uses one operator at every time, including zero.
theorem allTimeRegraph_forces_identity
    {Y E : Type*} [TopologicalSpace Y] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : ODE.CoupledFlowGraphTransform Y E) (h : F.AllTimeRegraph) :
    F.op = id := by
  funext σ y
  have hp := h 0 σ (ODE.graphMap_mem_graphSet σ y)
  simpa [ODE.graphSet, ODE.graphMap] using hp.symm

-- Published semilinear functions include integer division; this predicate does not.
theorem half_not_repo_semilinear :
    ¬ Computation.Semilinear (fun x : Fin 1 → ℕ => x 0 / 2) := by
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

theorem repo_MESSI : N.MESSI := by
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
-- but cannot satisfy the coercive, increasing-field predicate used in HirschConvergence.
theorem degradation_fails_repo_strong_monotonicity {c : ℝ} (hc : 0 < c) :
    ¬ CRNT.StronglyMonotone (fun x : Concentration (Fin 1) => -x) c := by
  intro h
  have hb := h.2 (fun _ => 0) (fun _ => 1)
  simp [CRNT.euclideanSqNorm, CRNT.euclideanInner] at hb
  linarith

end SemanticAudit

#print axioms SemanticAudit.complexBalanced_exists_convergent_solution
#print axioms SemanticAudit.allTimeRegraph_forces_identity
#print axioms SemanticAudit.half_not_repo_semilinear
#print axioms SemanticAudit.Division.computes_half
#print axioms SemanticAudit.Parity.positive_steady_state_count_eq_two
#print axioms SemanticAudit.Autocatalysis.not_conservative
#print axioms SemanticAudit.degradation_fails_repo_strong_monotonicity
