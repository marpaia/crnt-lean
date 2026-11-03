import CRNT.Stochastic.HarrisTheorem
import CRNT.Stochastic.FosterRecurrence
import CRNT.Stochastic.MinimalSemigroupNonExplosion
import CRNT.Stochastic.RecurrenceDichotomy
import CRNT.Stochastic.JumpReachabilityLift
import CRNT.Geometry.EndotacticGlobal

/-!
# Recurrence and non-explosion from explicit linear Lyapunov data

`LinearLyapunovData` supplies positive weights, a multiplicative generator drift
bound, and a jump-chain Foster bound. These hypotheses yield the stated
non-explosion, recurrence, and convergence conclusions, with irreducibility and
other premises where displayed. Immigration/death gives a concrete instance.

Strong endotacticity alone does not imply these stochastic conclusions in
several species. Anderson–Cappelletti–Kim–Nguyen, arXiv:1808.05328, Examples
3.1–3.2, give transient/explosive strongly endotactic examples. Accordingly the
Lyapunov data here are substantive additional assumptions, not a missing routine
transfer from deterministic permanence.
-/

open Filter Topology
open scoped BigOperators

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A positive linear Lyapunov datum for a stochastic mass-action system: a positive
weight `w`, a multiplicative drift bound `Q V ≤ −ε V + K` (which yields a
constant-negative drift outside a finite set), and an embedded jump-chain constant
drift (for Foster's hitting-time theorem). -/
structure LinearLyapunovData (N : Network S) (κ : RateConstants N) where
  w : S → ℝ
  hw : ∀ s, 0 < w s
  ε : ℝ
  hε : 0 < ε
  K : ℝ
  hK : 0 ≤ K
  hdrift : ∀ n, N.observableGenerator κ (linearObservable w) n ≤
      -ε * linearObservable w n + K
  C : Set (S → ℕ)
  hC : C.Finite
  εJ : ℝ
  hεJ : 0 < εJ
  hdriftJ : ∀ n, n ∉ C →
      (N.jumpChain κ).expect (linearObservable w) n ≤ linearObservable w n - εJ

/-- Nonnegativity of the linear Lyapunov function. -/
theorem linearObservable_nonneg {w : S → ℝ} (hw : ∀ s, 0 < w s) (n : S → ℕ) :
    0 ≤ linearObservable w n :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hw s).le (Nat.cast_nonneg _)

/-- **(1) Constant drift outside a finite set**, derived from the multiplicative bound. -/
theorem constant_drift_of_linearLyapunovData (N : Network S) (κ : RateConstants N)
    (d : LinearLyapunovData N κ) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : Set (S → ℕ), C.Finite ∧
      ∀ n ∉ C, N.observableGenerator κ (linearObservable d.w) n ≤ -c := by
  refine ⟨1, one_pos, {n | linearObservable d.w n ≤ (d.K + 1) / d.ε}, ?_, ?_⟩
  · exact finite_linearObservable_le d.w d.hw ((d.K + 1) / d.ε)
  · intro n hn
    have hV : (d.K + 1) / d.ε < linearObservable d.w n := by
      simpa [Set.mem_ofPred_eq] using hn
    have hεV : d.K + 1 < d.ε * linearObservable d.w n := by
      have h := (div_lt_iff₀ d.hε).mp hV
      linarith [h]
    have := d.hdrift n
    linarith

/-- **(2a) Foster hitting time** for the embedded jump chain. -/
theorem foster_hitting_time_of_linearLyapunovData (N : Network S) (κ : RateConstants N)
    (d : LinearLyapunovData N κ) [DecidablePred (· ∈ d.C)] (x : S → ℕ) :
    (∀ m, ∑ k ∈ Finset.range m, (N.jumpChain κ).survival d.C k x ≤
        1 + (N.jumpChain κ).expect (linearObservable d.w) x / d.εJ) ∧
      Tendsto (fun m => (N.jumpChain κ).survival d.C m x) atTop (𝓝 0) := by
  classical
  exact N.jumpChain_foster_hitting_time κ d.C (linearObservable_nonneg d.hw)
    d.hεJ d.hdriftJ x

/-- **(3) Non-explosion** from the multiplicative drift (affine form). -/
theorem nonExplosion_of_linearLyapunovData (N : Network S) (κ : RateConstants N)
    (d : LinearLyapunovData N κ) {t : ℝ} (ht : 0 ≤ t) (n : S → ℕ) :
    HasSum (fun m => N.transition κ t n m) 1 := by
  classical
  refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable d.w)
    (linearObservable_nonneg d.hw) (finite_linearObservable_le d.w d.hw)
    (le_refl 0) d.hK (fun m => by
      rw [N.jumpSystem_drift_linear κ d.w m, ← N.observableGenerator_linear κ d.w m]
      have := d.hdrift m
      linarith [mul_nonneg d.hε.le (linearObservable_nonneg d.hw m)]) ht n

/-- **(3') Non-explosion** via a positive weight increased only by monomolecular steps. -/
theorem nonExplosion_of_weight_bound (N : Network S) (κ : RateConstants N)
    (w : S → ℝ) (hw : ∀ s, 0 < w s)
    (hmol : ∀ r, 0 < ∑ s, w s * N.reactionVector r s →
      ∑ s, (N.reaction r).source s ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) (n : S → ℕ) :
    HasSum (fun m => N.transition κ t n m) 1 :=
  N.hasSum_transition_one_of_weight κ w hw hmol ht n

/-- **(2b) Geometric ergodicity / positive recurrence** from the multiplicative drift. -/
theorem positiveRecurrence_of_linearLyapunovData (N : Network S) (κ : RateConstants N)
    (d : LinearLyapunovData N κ)
    (hirr : ∀ a b : S → ℕ, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (S → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * linearObservable d.w b) ≤
          C₀ * (1 + linearObservable d.w a) * ρ ^ ⌊t⌋₊ := by
  classical
  set V := linearObservable d.w with hVdef
  have hV0 : ∀ n, 0 ≤ V n := linearObservable_nonneg d.hw
  have hfinV : ∀ R : ℝ, {n | V n ≤ R}.Finite := finite_linearObservable_le d.w d.hw
  have hstoch : ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (N.jumpSystem κ).Pmin t n m) 1 := by
    intro t ht n
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine V hV0 hfinV (le_refl 0) d.hK
      (fun m => by
        rw [N.jumpSystem_drift_linear κ d.w m, ← N.observableGenerator_linear κ d.w m]
        have := d.hdrift m
        linarith [mul_nonneg d.hε.le (linearObservable_nonneg d.hw m)]) ht n
  have hdrift : ∀ n, (N.jumpSystem κ).drift V n ≤ -d.ε * V n + d.K := by
    intro n
    rw [N.jumpSystem_drift_linear κ d.w n, ← N.observableGenerator_linear κ d.w n]
    exact d.hdrift n
  exact (N.jumpSystem κ).geometric_ergodic V hV0 hfinV d.hε d.hK hdrift hstoch hirr

/-- Analogue of `tendsto_transition_self_pos_of_recurrent` (conservative setting). -/
theorem tendsto_transition_self_pos_of_linearLyapunovData (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) {b : S → ℕ}
    (hrec : ∀ m, (N.jumpSystem κ).ReachPos b m → (N.jumpSystem κ).ReachPos m b) :
    ∃ p : ℝ, 0 < p ∧ Tendsto (fun t => N.transition κ t b b) atTop (𝓝 p) :=
  N.tendsto_transition_self_pos_of_recurrent κ hcons hrec

end Network

namespace Examples
namespace EndotacticBirthDeath

open Network

/-- The reaction pair `0 → X`, `X → 0` (one species). -/
abbrev net : Network (Fin 1) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![0], ![1]⟩ else ⟨![1], ![0]⟩⟩

theorem stronglyEndotacticStd : net.StronglyEndotacticStd := by
  refine ⟨?_, ?_⟩
  · intro w r hmax
    by_cases hr : r = 0
    · subst hr
      have hmax1 : net.wValue w 1 ≤ net.wValue w 0 := hmax 1
      have hw1 : net.wValue w 1 = w 0 := by
        simp [Network.wValue, Network.dotProduct, exponentVector, net]
      have hw0 : net.wValue w 0 = 0 := by
        simp [Network.wValue, Network.dotProduct, exponentVector, net]
      have hr0 : net.wRate w 0 = w 0 := by
        simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, net]
      rw [hw1, hw0] at hmax1
      rw [hr0]
      exact hmax1
    · have hr1 : r = 1 := by
        fin_cases r
        · exfalso; exact hr rfl
        · rfl
      subst hr1
      have hmax0 : net.wValue w 0 ≤ net.wValue w 1 := hmax 0
      have hw0 : net.wValue w 0 = 0 := by
        simp [Network.wValue, Network.dotProduct, exponentVector, net]
      have hw1 : net.wValue w 1 = w 0 := by
        simp [Network.wValue, Network.dotProduct, exponentVector, net]
      have hr1r : net.wRate w 1 = -w 0 := by
        simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, net]
      rw [hw0, hw1] at hmax0
      rw [hr1r]
      linarith
  · intro w hactive
    by_cases hpos : 0 < w 0
    · refine ⟨1, ?_, ?_⟩
      · intro r'
        fin_cases r'
        · simp [Network.wValue, Network.dotProduct, exponentVector, net]; linarith [hpos]
        · simp [Network.wValue, Network.dotProduct, exponentVector, net]
      · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, net]; linarith [hpos]
    · by_cases hneg : w 0 < 0
      · refine ⟨0, ?_, ?_⟩
        · intro r'
          fin_cases r'
          · simp [Network.wValue, Network.dotProduct, exponentVector, net]
          · simp [Network.wValue, Network.dotProduct, exponentVector, net]; linarith [hneg]
        · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, net]; linarith [hneg]
      · exfalso
        have hw0 : w 0 = 0 := le_antisymm (le_of_not_gt hpos) (le_of_not_gt hneg)
        have hall : ∀ r : net.R, net.wRate w r = 0 := by
          intro r
          fin_cases r
          · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, net, hw0]
          · simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, net, hw0]
        obtain ⟨r, hrne⟩ := hactive
        exact hrne (hall r)

/-- Reachability of the birth-death chain: every count reaches every other count. -/
theorem reachPos (κ : net.RateConstants) (a b : Fin 1 → ℕ) :
    (net.jumpSystem κ).ReachPos a b := by
  have ha : a = fun _ => a 0 := by funext s; fin_cases s; rfl
  have hb : b = fun _ => b 0 := by funext s; fin_cases s; rfl
  rw [ha, hb]
  -- reach 0 from m
  have toZero : ∀ m : ℕ, (net.jumpSystem κ).ReachPos (fun _ => m) (fun _ => 0) := by
    intro m
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
        have hen : net.Enabled (fun _ => m + 1) (1 : Fin 2) := by
          intro s; fin_cases s; simp
        have hrate : 0 < (net.jumpSystem κ).rate (1 : Fin 2) (fun _ => m + 1) :=
          CRNT.Network.stochasticMassActionRate_pos_of_enabled net κ hen
        have hnext : (net.jumpSystem κ).next (1 : Fin 2) (fun _ => m + 1) = (fun _ => m) := by
          funext s
          fin_cases s
          simp [Network.jumpSystem, Network.jumpNextCount, net]
        exact Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨(1 : Fin 2), hrate, hnext.symm⟩) ih
  -- reach n from 0
  have fromZero : ∀ n : ℕ, (net.jumpSystem κ).ReachPos (fun _ => 0) (fun _ => n) := by
    intro n
    induction n with
    | zero => exact Relation.ReflTransGen.refl
    | succ n ih =>
        have hen : net.Enabled (fun _ => n) (0 : Fin 2) := by
          intro s; fin_cases s; simp
        have hrate : 0 < (net.jumpSystem κ).rate (0 : Fin 2) (fun _ => n) :=
          CRNT.Network.stochasticMassActionRate_pos_of_enabled net κ hen
        have hnext : (net.jumpSystem κ).next (0 : Fin 2) (fun _ => n) = (fun _ => n + 1) := by
          funext s
          fin_cases s
          simp [Network.jumpSystem, Network.jumpNextCount, net]
        exact Relation.ReflTransGen.trans ih
          (Relation.ReflTransGen.single ⟨(0 : Fin 2), hrate, hnext.symm⟩)
  exact Relation.ReflTransGen.trans (toZero (a 0)) (fromZero (b 0))

/-- Linear Lyapunov datum for the birth-death instance. -/
noncomputable def data (κ : net.RateConstants) : LinearLyapunovData net κ where
  w := fun _ => 1
  hw := by intro s; fin_cases s; norm_num
  ε := κ.k 1 / 2
  hε := by have := κ.positive 1; linarith
  K := κ.k 0
  hK := (κ.positive 0).le
  hdrift := by
    intro n
    have hr0 : net.stochasticMassActionRate κ n 0 = κ.k 0 := by
      unfold Network.stochasticMassActionRate
      simp [net]
    have hr1 : net.stochasticMassActionRate κ n 1 = κ.k 1 * (n 0 : ℝ) := by
      unfold Network.stochasticMassActionRate
      simp [net, Nat.descFactorial_one]
    have inner0 : ∑ s : Fin 1, (1 : ℝ) * net.reactionVector 0 s = 1 := by
      simp [net, Network.reactionVector_apply, Fin.sum_univ_one]
    have inner1 : ∑ s : Fin 1, (1 : ℝ) * net.reactionVector 1 s = -1 := by
      simp [net, Network.reactionVector_apply, Fin.sum_univ_one]
    have hgen : net.observableGenerator κ (linearObservable (fun _ => 1)) n =
        κ.k 0 - κ.k 1 * (n 0 : ℝ) := by
      rw [Network.observableGenerator_linear]
      simp only [hr0, hr1, inner0, inner1, Fin.sum_univ_two]
      ring
    have hV : linearObservable (fun _ => 1) n = (n 0 : ℝ) := by
      simp [linearObservable, Fin.sum_univ_one]
    rw [hgen, hV]
    linarith [mul_nonneg (κ.positive 1).le (Nat.cast_nonneg (n 0))]
  C := {n | linearObservable (fun _ => (1 : ℝ)) n ≤
      (Nat.floor (3 * κ.k 0 / κ.k 1) : ℝ)}
  hC := finite_linearObservable_le (fun _ => (1 : ℝ))
    (by intro s; fin_cases s; norm_num) (Nat.floor (3 * κ.k 0 / κ.k 1) : ℝ)
  εJ := 1 / 2
  hεJ := by norm_num
  hdriftJ := by
    intro n hn
    set a := κ.k 0
    set b := κ.k 1
    have hr0 : net.stochasticMassActionRate κ n 0 = a := by
      unfold Network.stochasticMassActionRate
      simp [net, a]
    have hr1 : net.stochasticMassActionRate κ n 1 = b * (n 0 : ℝ) := by
      unfold Network.stochasticMassActionRate
      simp [net, b, Nat.descFactorial_one]
    have inner0 : ∑ s : Fin 1, (1 : ℝ) * net.reactionVector 0 s = 1 := by
      simp [net, Network.reactionVector_apply, Fin.sum_univ_one]
    have inner1 : ∑ s : Fin 1, (1 : ℝ) * net.reactionVector 1 s = -1 := by
      simp [net, Network.reactionVector_apply, Fin.sum_univ_one]
    have hgen : net.observableGenerator κ (linearObservable (fun _ => 1)) n =
        a - b * (n 0 : ℝ) := by
      rw [Network.observableGenerator_linear]
      simp only [hr0, hr1, inner0, inner1, Fin.sum_univ_two]
      ring
    have hexit : net.exitRate κ n = a + b * (n 0 : ℝ) := by
      unfold Network.exitRate
      simp only [hr0, hr1, Fin.sum_univ_two]
    have hne : net.exitRate κ n ≠ 0 := by
      rw [hexit]
      exact (add_pos_of_pos_of_nonneg (κ.positive 0)
        (mul_nonneg (κ.positive 1).le (Nat.cast_nonneg (n 0)))).ne'
    have hmul := net.observableGenerator_eq_exitRate_mul κ
      (linearObservable (fun _ => 1)) n hne
    rw [hmul] at hgen
    have hV : linearObservable (fun _ => 1) n = (n 0 : ℝ) := by
      simp [linearObservable, Fin.sum_univ_one]
    have hn0 : (Nat.floor (3 * a / b) : ℝ) < (n 0 : ℝ) := by
      have : ¬ (linearObservable (fun _ => (1 : ℝ)) n ≤
          (Nat.floor (3 * a / b) : ℝ)) := hn
      simpa [linearObservable, Fin.sum_univ_one] using this
    have hfloor_lt : 3 * a / b < (Nat.floor (3 * a / b) : ℝ) + 1 :=
      Nat.lt_floor_add_one (3 * a / b)
    have hcast : Nat.floor (3 * a / b) < n 0 :=
      Nat.cast_lt.mp hn0
    have hle : (Nat.floor (3 * a / b) : ℝ) + 1 ≤ (n 0 : ℝ) := by
      exact_mod_cast (Nat.add_one_le_of_lt hcast)
    have hx : 3 * a / b < (n 0 : ℝ) := hfloor_lt.trans_le hle
    have hx' : 3 * a < b * (n 0 : ℝ) := by
      linarith [(div_lt_iff₀ (κ.positive 1)).mp hx]
    have hden : 0 < a + b * (n 0 : ℝ) := by
      exact add_pos_of_pos_of_nonneg (κ.positive 0)
        (mul_nonneg (κ.positive 1).le (Nat.cast_nonneg (n 0)))
    have hratio : (a - b * (n 0 : ℝ)) / (a + b * (n 0 : ℝ)) ≤ -(1 / 2 : ℝ) := by
      rw [div_le_iff₀ hden]
      linarith [hx']
    have hdiff : (net.jumpChain κ).expect (linearObservable (fun _ => 1)) n -
        linearObservable (fun _ => 1) n =
        (a - b * (n 0 : ℝ)) / (a + b * (n 0 : ℝ)) := by
      have : (net.jumpChain κ).expect (linearObservable (fun _ => 1)) n -
          linearObservable (fun _ => 1) n =
          (a - b * (n 0 : ℝ)) / net.exitRate κ n := by
        rw [eq_div_iff hne]
        rw [mul_comm]
        exact hgen
      rw [this, hexit]
    have : (net.jumpChain κ).expect (linearObservable (fun _ => 1)) n ≤
        linearObservable (fun _ => 1) n - 1 / 2 := by
      linarith [hdiff, hratio]
    simpa [hV] using this

/-- Non-explosion for the birth-death instance. -/
theorem nonExplosion (κ : net.RateConstants) {t : ℝ} (ht : 0 ≤ t)
    (n : Fin 1 → ℕ) :
    HasSum (fun m => net.transition κ t n m) 1 :=
  nonExplosion_of_linearLyapunovData net κ (data κ) ht n

/-- Positive recurrence (geometric ergodicity) for the birth-death instance. -/
theorem positiveRecurrence (κ : net.RateConstants) :
    ∃ π : (Fin 1 → ℕ) → ℝ, (∀ m, 0 ≤ π m) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ m, ∑' x, π x * net.transition κ s x m = π m) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' m, |net.transition κ t a m - π m| *
            (1 + β * linearObservable (fun _ => 1) m) ≤
          C₀ * (1 + linearObservable (fun _ => 1) a) * ρ ^ ⌊t⌋₊ := by
  refine positiveRecurrence_of_linearLyapunovData net κ (data κ) (fun a b => reachPos κ a b)

end EndotacticBirthDeath
end Examples

end CRNT