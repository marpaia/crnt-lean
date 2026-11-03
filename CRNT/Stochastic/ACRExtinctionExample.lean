import CRNT.Stochastic.JumpAbsorption
import CRNT.Equilibria.SteadyState
import Mathlib.Tactic.FinCases

/-!
# Deterministic ACR versus stochastic extinction: `A + B → 2B`, `B → A`

The network `A + B → 2B`, `B → A` (Shinar–Feinberg's basic example) has absolute concentration
robustness: every positive steady state has `x_A = κ₁ / κ₀`. Its stochastic model nevertheless
goes extinct: on each conservation class `{a + b = m}` the counts with `b = 0` are absorbing and
reachable from every count, so the embedded jump chain is absorbed with probability one
(Anderson–Enciso–Johnston, *Stochastic analysis of biochemical reaction networks with absolute
concentration robustness*, J. R. Soc. Interface 11 (2014), the motivating example).

Main results:
* `CRNT.ACRExample.deterministic_ACR`.
* `CRNT.ACRExample.stochastic_extinction`.
-/

namespace CRNT

namespace ACRExample

open Filter Topology Network FiniteAbsorption

/-- `A + B → 2B` (reaction `0`) and `B → A` (reaction `1`); species `0 = A`, `1 = B`. -/
def net : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![1, 1], ![0, 2]⟩ else ⟨![0, 1], ![1, 0]⟩⟩

theorem r0 : net.reaction (0 : Fin 2) = ⟨![1, 1], ![0, 2]⟩ := rfl
theorem r1 : net.reaction (1 : Fin 2) = ⟨![0, 1], ![1, 0]⟩ := rfl
theorem sum_R (g : net.R → ℝ) : ∑ r, g r = g (0 : Fin 2) + g (1 : Fin 2) := Fin.sum_univ_two g

/-- **Deterministic ACR.** Every positive steady state has `x_A = κ₁ / κ₀`. -/
theorem deterministic_ACR (κ : net.RateConstants) {x : Concentration (Fin 2)} (hx : x.Positive)
    (hss : net.IsMassActionSteadyState κ x) : x 0 = κ.k (1 : Fin 2) / κ.k (0 : Fin 2) := by
  have h := hss 1
  rw [Network.massActionVectorField_apply, sum_R] at h
  simp [massActionRate, reactionVector, r0, r1, Complex.massActionMonomial,
    Fin.prod_univ_two] at h
  have hk0 := κ.positive (0 : Fin 2)
  have hx1 := hx 1
  rw [eq_div_iff hk0.ne']
  have : x 1 * (κ.k (0 : Fin 2) * x 0 - κ.k (1 : Fin 2)) = 0 := by linarith
  rcases mul_eq_zero.mp this with h1 | h1
  · exact absurd h1 hx1.ne'
  · linarith

theorem rate0 (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n (0 : Fin 2) = κ.k (0 : Fin 2) * (n 0 * n 1 : ℕ) := by
  simp [stochasticMassActionRate, r0, Fin.prod_univ_two]

theorem rate1 (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n (1 : Fin 2) = κ.k (1 : Fin 2) * (n 1 : ℕ) := by
  simp [stochasticMassActionRate, r1, Fin.prod_univ_two]

theorem exitRate_eq_zero_iff (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.exitRate κ n = 0 ↔ n 1 = 0 := by
  have hk0 := κ.positive (0 : Fin 2)
  have hk1 := κ.positive (1 : Fin 2)
  rw [exitRate, sum_R, rate0, rate1]
  constructor
  · intro h
    have h0 : 0 ≤ κ.k (0 : Fin 2) * ((n 0 * n 1 : ℕ) : ℝ) := by positivity
    have h1 : κ.k (1 : Fin 2) * ((n 1 : ℕ) : ℝ) = 0 := by
      have : 0 ≤ κ.k (1 : Fin 2) * ((n 1 : ℕ) : ℝ) := by positivity
      linarith
    rcases mul_eq_zero.mp h1 with h | h
    · exact absurd h hk1.ne'
    · exact_mod_cast h
  · intro h; simp [h]

/-- The conservation class `{a + b = m}`. -/
def cls (m : ℕ) : Finset (Fin 2 → ℕ) := (Finset.range (m + 1)).image (fun k => ![m - k, k])

theorem mem_cls {m : ℕ} {n : Fin 2 → ℕ} : n ∈ cls m ↔ n 0 + n 1 = m := by
  constructor
  · intro h
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp h
    have := Finset.mem_range.mp hk
    simp; omega
  · intro h
    refine Finset.mem_image.mpr ⟨n 1, Finset.mem_range.mpr (by omega), ?_⟩
    funext i; fin_cases i <;> simp <;> omega

theorem jumpClosed (κ : net.RateConstants) (m : ℕ) : net.JumpClosed κ (cls m) := by
  intro n hn r hr
  rw [mem_cls] at hn ⊢
  have hr' : r = (0 : Fin 2) ∨ r = (1 : Fin 2) := by
    rcases Fin.exists_fin_two.mp ⟨r, rfl⟩ with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hr' with rfl | rfl
  · rw [rate0] at hr
    have : 0 < n 0 * n 1 := by
      have := (mul_pos_iff_of_pos_left (κ.positive (0 : Fin 2))).mp hr
      exact_mod_cast this
    have h0 : 0 < n 0 := Nat.pos_of_mul_pos_right this
    have h1 : 0 < n 1 := Nat.pos_of_mul_pos_left this
    simp [jumpNextCount, r0]; omega
  · rw [rate1] at hr
    have h1 : 0 < n 1 := by
      have := (mul_pos_iff_of_pos_left (κ.positive (1 : Fin 2))).mp hr
      exact_mod_cast this
    simp [jumpNextCount, r1]; omega

/-- From every count of the class the absorbing count `(m, 0)` is reachable. -/
theorem reach_absorbing (κ : net.RateConstants) (m : ℕ) :
    ∀ k (j : cls m), (j : Fin 2 → ℕ) 1 = k →
      Relation.ReflTransGen (net.JumpAbsStep κ (cls m)) j
        ⟨![m, 0], mem_cls.mpr (by simp)⟩ := by
  intro k
  induction k with
  | zero =>
    intro j hj
    have hj' := mem_cls.mp j.2
    have : j = ⟨![m, 0], mem_cls.mpr (by simp)⟩ := by
      apply Subtype.ext; funext i; fin_cases i <;> simp <;> omega
    rw [this]
  | succ k ih =>
    intro j hj
    have hj' := mem_cls.mp j.2
    let nxt : cls m := ⟨net.jumpNextCount j (1 : Fin 2), jumpClosed κ m j j.2 _ (by
      rw [rate1]; have := κ.positive (1 : Fin 2); rw [hj]; positivity)⟩
    have hstep : net.JumpAbsStep κ (cls m) j nxt := ⟨(1 : Fin 2), by
      rw [rate1]; have := κ.positive (1 : Fin 2); rw [hj]; positivity, rfl⟩
    have hnxt : (nxt : Fin 2 → ℕ) 1 = k := by
      simp [nxt, jumpNextCount, r1]; omega
    exact Relation.ReflTransGen.head hstep (ih nxt hnxt)

/-- **Stochastic extinction.** On every conservation class the embedded jump chain is absorbed
in the `B`-free counts with probability one, although the deterministic model has absolute
concentration robustness. -/
theorem stochastic_extinction (κ : net.RateConstants) (m : ℕ) (j : cls m) :
    Tendsto (fun n => absorbedMass (net.jumpMatrix κ (cls m)) (net.absorbingCounts κ (cls m)) n j)
      atTop (𝓝 1) := by
  refine net.tendsto_jumpAbsorption_one κ (jumpClosed κ m) (fun j => ?_) j
  exact ⟨⟨![m, 0], mem_cls.mpr (by simp)⟩, (exitRate_eq_zero_iff κ _).mpr (by simp),
    reach_absorbing κ m _ j rfl⟩

/-- The absorbing counts are exactly those without `B`. -/
theorem absorbing_iff (κ : net.RateConstants) (m : ℕ) (j : cls m) :
    j ∈ net.absorbingCounts κ (cls m) ↔ (j : Fin 2 → ℕ) 1 = 0 := by
  simp [absorbingCounts, exitRate_eq_zero_iff]

end ACRExample

end CRNT
