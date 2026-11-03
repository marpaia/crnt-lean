import CRNT.Open.Augmentation
import CRNT.Equilibria.SteadyState

/-!
# Fully open networks with one non-flow reaction: uniqueness (Joshi 2013, Theorem 4.1)

For the fully open network with the single non-flow reaction `a → b`, if
`∑_{i : b_i > a_i} a_i ≤ 1` then for every choice of positive rate constants there is at most one
positive steady state (`oneRxn_unique_steadyState`).  This is the "only if" half of
Joshi's characterization (multistationary iff `∑_{i : b_i > a_i} a_i > 1`).

Proof (direct, without the Deficiency One Algorithm).  At a steady state
`l_i x_i = k_i + d_i u` with `u = k x^a`, `d_i = b_i - a_i`.  For two steady states with
`u < v`, each ratio `z_i / x_i` is `< v/u` if `d_i > 0` and `≤ 1` otherwise, so
`v/u = ∏ (z_i/x_i)^{a_i} < (v/u)^{∑_{d_i>0} a_i} ≤ v/u`; and `u = v` forces `x = z`.

Nothing here is an axiom or a `sorry`.
-/

open Finset

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The network with the single reaction `a → b`. -/
abbrev oneRxn (a b : Complex S) : Network S := ⟨Unit, inferInstance, inferInstance, fun _ => ⟨a, b⟩⟩

theorem oneRxn_fullyOpen_field (a b : Complex S) (κ : (oneRxn a b).fullyOpen.RateConstants)
    (x : Concentration S) (s : S) :
    (oneRxn a b).fullyOpen.massActionVectorField κ x s =
      κ.k (Sum.inl ()) * a.massActionMonomial x * ((b s : ℝ) - a s) +
        κ.k (Sum.inr (Sum.inl s)) - κ.k (Sum.inr (Sum.inr s)) * x s := by
  have hrin : ((oneRxn a b).fullyOpen.reaction (Sum.inr (Sum.inl s))) = inflowReaction s := rfl
  have hrout : ((oneRxn a b).fullyOpen.reaction (Sum.inr (Sum.inr s))) = outflowReaction s := rfl
  rw [massActionVectorField_apply]
  erw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [massActionRate]
  have h1 : (∑ r : (oneRxn a b).R, κ.k (Sum.inl r) *
      ((oneRxn a b).fullyOpen.reaction (Sum.inl r)).source.massActionMonomial x *
        (oneRxn a b).fullyOpen.reactionVector (Sum.inl r) s) =
      κ.k (Sum.inl ()) * a.massActionMonomial x * ((b s : ℝ) - a s) := by
    rw [Fintype.sum_unique]; erw [reactionVector_apply]; rfl
  have h2 : (∑ s' : S, κ.k (Sum.inr (Sum.inl s')) *
      ((oneRxn a b).fullyOpen.reaction (Sum.inr (Sum.inl s'))).source.massActionMonomial x *
        (oneRxn a b).fullyOpen.reactionVector (Sum.inr (Sum.inl s')) s) =
      κ.k (Sum.inr (Sum.inl s)) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_inflow]; simp [Pi.single_apply, Ne.symm hs']) (by simp)]
    erw [reactionVector_inflow, hrin]
    simp [inflowReaction]
  have h3 : (∑ s' : S, κ.k (Sum.inr (Sum.inr s')) *
      ((oneRxn a b).fullyOpen.reaction (Sum.inr (Sum.inr s'))).source.massActionMonomial x *
        (oneRxn a b).fullyOpen.reactionVector (Sum.inr (Sum.inr s')) s) =
      -(κ.k (Sum.inr (Sum.inr s)) * x s) := by
    rw [Finset.sum_eq_single s (fun s' _ hs' => by
      erw [reactionVector_outflow]; simp [Pi.single_apply, Ne.symm hs']) (by simp)]
    erw [reactionVector_outflow, hrout]
    simp [outflowReaction, Complex.massActionMonomial, singletonComplex, Pi.single_apply]
  rw [h1, h2, h3]; ring

/-- The key inequality: no two steady states with `u < v`. -/
theorem oneRxn_no_two_levels (a b : Complex S)
    (hA : ∑ s ∈ univ.filter (fun s => a s < b s), a s ≤ 1)
    (κ : (oneRxn a b).fullyOpen.RateConstants) {x z : Concentration S}
    (hx : x.Positive) (hz : z.Positive)
    (hxs : (oneRxn a b).fullyOpen.IsMassActionSteadyState κ x)
    (hzs : (oneRxn a b).fullyOpen.IsMassActionSteadyState κ z)
    (hlt : κ.k (Sum.inl ()) * a.massActionMonomial x < κ.k (Sum.inl ()) * a.massActionMonomial z) :
    False := by
  classical
  set k := κ.k (Sum.inl ())
  set u := k * a.massActionMonomial x with hu
  set v := k * a.massActionMonomial z with hv
  have hk := κ.positive (Sum.inl ())
  have hmx : 0 < a.massActionMonomial x := Complex.massActionMonomial_pos hx a
  have hmz : 0 < a.massActionMonomial z := Complex.massActionMonomial_pos hz a
  have hupos : 0 < u := mul_pos hk hmx
  have hvpos : 0 < v := mul_pos hk hmz
  -- steady-state relations `l_s x_s = k_s + d_s u`
  have hrelx : ∀ s, κ.k (Sum.inr (Sum.inr s)) * x s =
      κ.k (Sum.inr (Sum.inl s)) + ((b s : ℝ) - a s) * u := fun s => by
    have := hxs s; rw [oneRxn_fullyOpen_field] at this; rw [hu]; linarith
  have hrelz : ∀ s, κ.k (Sum.inr (Sum.inr s)) * z s =
      κ.k (Sum.inr (Sum.inl s)) + ((b s : ℝ) - a s) * v := fun s => by
    have := hzs s; rw [oneRxn_fullyOpen_field] at this; rw [hv]; linarith
  set r : S → ℝ := fun s => z s / x s with hr
  have hrpos : ∀ s, 0 < r s := fun s => div_pos (hz s) (hx s)
  have hratio : ∀ s, r s = (κ.k (Sum.inr (Sum.inl s)) + ((b s : ℝ) - a s) * v) /
      (κ.k (Sum.inr (Sum.inl s)) + ((b s : ℝ) - a s) * u) := by
    intro s
    have hl := κ.positive (Sum.inr (Sum.inr s))
    rw [← hrelx, ← hrelz, hr]; field_simp
  -- bounds on the ratios
  have hbig : ∀ s, a s < b s → r s < v / u := by
    intro s hs
    have hcast : (a s : ℝ) < b s := by exact_mod_cast hs
    have hd : (0 : ℝ) < (b s : ℝ) - a s := by linarith
    have hin := κ.positive (Sum.inr (Sum.inl s))
    have hden : 0 < κ.k (Sum.inr (Sum.inl s)) + ((b s : ℝ) - a s) * u := by positivity
    rw [hratio, div_lt_div_iff₀ hden hupos]
    nlinarith [mul_lt_mul_of_pos_left hlt hin]
  have hsmall : ∀ s, ¬ a s < b s → r s ≤ 1 := by
    intro s hs
    have hcast : (b s : ℝ) ≤ a s := by exact_mod_cast not_lt.mp hs
    have hd : (b s : ℝ) - a s ≤ 0 := by linarith
    have hden : 0 < κ.k (Sum.inr (Sum.inl s)) + ((b s : ℝ) - a s) * u := by
      have := hrelx s; have := κ.positive (Sum.inr (Sum.inr s)); have := hx s
      nlinarith
    rw [hratio, div_le_one hden]
    nlinarith
  -- `v / u = ∏ r_s ^ a_s`
  have hprod : v / u = ∏ s, r s ^ a s := by
    rw [hu, hv, mul_div_mul_left _ _ hk.ne']
    simp only [Complex.massActionMonomial, hr, div_pow]
    rw [prod_div_distrib]
  set P := univ.filter (fun s => a s < b s) with hP
  have hsplit := prod_filter_mul_prod_filter_not univ (fun s => a s < b s) (fun s => r s ^ a s)
  have hrest : ∏ s ∈ univ.filter (fun s => ¬ a s < b s), r s ^ a s ≤ 1 :=
    prod_le_one₀ (fun s _ => (pow_pos (hrpos s) _).le) fun s hs =>
      pow_le_one₀ (hrpos s).le (hsmall s (mem_filter.mp hs).2)
  have hPpart : ∏ s ∈ P, r s ^ a s < v / u := by
    have hvu : 1 < v / u := by rw [one_lt_div hupos]; exact hlt
    rcases Nat.lt_or_ge (∑ s ∈ P, a s) 1 with h0 | h1
    · have hz0 : ∀ s ∈ P, a s = 0 := fun s hs => by
        have := single_le_sum (f := fun s => a s) (fun _ _ => Nat.zero_le _) hs; omega
      rw [prod_eq_one fun s hs => by rw [hz0 s hs, pow_zero]]; exact hvu
    · have heq : ∑ s ∈ P, a s = 1 := le_antisymm hA h1
      obtain ⟨s₀, hs₀, hpos⟩ : ∃ s₀ ∈ P, 0 < a s₀ := by
        by_contra hall; push Not at hall
        have : ∑ s ∈ P, a s = 0 := sum_eq_zero fun s hs => Nat.le_zero.mp (hall s hs)
        omega
      have ha0 : a s₀ = 1 := by
        have := single_le_sum (f := fun s => a s) (fun _ _ => Nat.zero_le _) hs₀; omega
      have hothers : ∀ s ∈ P, s ≠ s₀ → a s = 0 := by
        intro s hs hne
        have hsub : ({s, s₀} : Finset S) ⊆ P := by
          intro t ht; simp only [mem_insert, mem_singleton] at ht; rcases ht with rfl | rfl <;> assumption
        have := sum_le_sum_of_subset (f := fun s => a s) hsub
        rw [sum_pair hne] at this; omega
      rw [prod_eq_single_of_mem s₀ hs₀ (fun s hs hne => by rw [hothers s hs hne, pow_zero]), ha0,
        pow_one]
      exact hbig s₀ (mem_filter.mp hs₀).2
  have := hsplit ▸ hprod
  have hle : (∏ s ∈ P, r s ^ a s) * ∏ s ∈ univ.filter (fun s => ¬ a s < b s), r s ^ a s ≤
      ∏ s ∈ P, r s ^ a s :=
    mul_le_of_le_one_right (prod_nonneg fun s _ => (pow_pos (hrpos s) _).le) hrest
  linarith

/-- **Joshi 2013, Theorem 4.1 ("only if").** If `∑_{i : b_i > a_i} a_i ≤ 1`, the fully open
network with the single non-flow reaction `a → b` has at most one positive steady state, for every
choice of positive rate constants. -/
theorem oneRxn_unique_steadyState (a b : Complex S)
    (hA : ∑ s ∈ univ.filter (fun s => a s < b s), a s ≤ 1)
    (κ : (oneRxn a b).fullyOpen.RateConstants) {x z : Concentration S}
    (hx : x.Positive) (hz : z.Positive)
    (hxs : (oneRxn a b).fullyOpen.IsMassActionSteadyState κ x)
    (hzs : (oneRxn a b).fullyOpen.IsMassActionSteadyState κ z) : x = z := by
  rcases lt_trichotomy (κ.k (Sum.inl ()) * a.massActionMonomial x)
      (κ.k (Sum.inl ()) * a.massActionMonomial z) with hlt | heq | hgt
  · exact (oneRxn_no_two_levels a b hA κ hx hz hxs hzs hlt).elim
  · funext s
    have h1 := hxs s; have h2 := hzs s
    rw [oneRxn_fullyOpen_field] at h1 h2
    have hl := κ.positive (Sum.inr (Sum.inr s))
    have : κ.k (Sum.inr (Sum.inr s)) * x s = κ.k (Sum.inr (Sum.inr s)) * z s := by
      have e1 : κ.k (Sum.inr (Sum.inr s)) * x s = κ.k (Sum.inr (Sum.inl s)) +
          κ.k (Sum.inl ()) * a.massActionMonomial x * ((b s : ℝ) - a s) := by linarith
      have e2 : κ.k (Sum.inr (Sum.inr s)) * z s = κ.k (Sum.inr (Sum.inl s)) +
          κ.k (Sum.inl ()) * a.massActionMonomial z * ((b s : ℝ) - a s) := by linarith
      rw [e1, e2, heq]
    exact mul_left_cancel₀ hl.ne' this
  · exact (oneRxn_no_two_levels a b hA κ hz hx hzs hxs hgt).elim

end Network
end CRNT
