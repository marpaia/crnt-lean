import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Basic

/-!
# Kamke comparison principle for cooperative (monotone) systems

A vector field `f` on `ℝ^S` satisfies the **Kamke condition** on a set `K` if
`a ≤ b`, `a i = b i` imply `f a i ≤ f b i` (off-diagonal monotonicity, i.e. a cooperative
system). Kamke's theorem (Kamke 1932; Hirsch–Smith, *Monotone dynamical systems*, Prop. 1.1;
for reaction networks Angeli–Sontag 2008, Banaji 2009) states that such flows preserve the
componentwise order: `x(0) ≤ y(0)` implies `x(t) ≤ y(t)`.

We prove it for a field that is Lipschitz on a set `K` closed under componentwise maximum, for
solutions remaining in `K`. The proof shows that `V(t) = ∑ᵢ (max (xᵢ - yᵢ) 0)²` satisfies
`V' ≤ 2 L |S| V` and `V(0) = 0`.

We then give a structural criterion for mass-action networks: if every reaction that consumes a
species `i` has a source complex involving no species other than `i`, the mass-action field is
cooperative on the nonnegative orthant.

Main results:
* `CRNT.Monotone.hasDerivAt_posPart_sq`.
* `CRNT.Monotone.kamke_comparison`: the comparison principle.
* `CRNT.Network.IsCooperativeNetwork`, `CRNT.Network.massAction_kamke_of_cooperative`.
-/

namespace CRNT

namespace Monotone

open Filter Topology Asymptotics
open scoped BigOperators NNReal

theorem hasDerivAt_posPart_sq (a : ℝ) :
    HasDerivAt (fun u : ℝ => (max u 0) ^ 2) (2 * max a 0) a := by
  rcases lt_trichotomy a 0 with ha | ha | ha
  · have : (fun u : ℝ => (max u 0) ^ 2) =ᶠ[𝓝 a] fun _ => 0 := by
      filter_upwards [eventually_lt_nhds ha] with u hu
      simp [max_eq_right hu.le]
    rw [max_eq_right ha.le, mul_zero]
    exact (hasDerivAt_const a (0:ℝ)).congr_of_eventuallyEq this
  · subst ha
    rw [max_self, mul_zero, hasDerivAt_iff_isLittleO_nhds_zero]
    simp only [zero_add, max_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      sub_zero, smul_zero]
    have h2 : (fun d : ℝ => d ^ 2) =o[𝓝 0] fun d => d := by
      simpa using isLittleO_pow_id (by norm_num : 1 < 2)
    refine IsBigO.trans_isLittleO ?_ h2
    refine IsBigO.of_bound 1 (Eventually.of_forall fun d => ?_)
    rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
      abs_of_nonneg (sq_nonneg _)]
    rcases le_total d 0 with hd | hd
    · rw [max_eq_right hd]; nlinarith [sq_nonneg d]
    · rw [max_eq_left hd]
  · have : (fun u : ℝ => (max u 0) ^ 2) =ᶠ[𝓝 a] fun u => u ^ 2 := by
      filter_upwards [eventually_gt_nhds ha] with u hu
      simp [max_eq_left hu.le]
    rw [max_eq_left ha.le]
    have := (hasDerivAt_pow 2 a).congr_of_eventuallyEq this
    simpa [mul_comm] using this

variable {S : Type} [Fintype S]

/-- The Kamke (quasi-monotonicity) condition on `K`. -/
def KamkeOn (f : (S → ℝ) → (S → ℝ)) (K : Set (S → ℝ)) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, a ≤ b → ∀ i, a i = b i → f a i ≤ f b i

/-- **Kamke comparison principle.** Let `f` be Lipschitz and satisfy the Kamke condition on a
set `K` closed under componentwise maximum. If `x, y` solve `ẋ = f(x)` on `[0, T]` inside `K`
and `x 0 ≤ y 0`, then `x t ≤ y t` for all `t ∈ [0, T]`. -/
theorem kamke_comparison {f : (S → ℝ) → (S → ℝ)} {K : Set (S → ℝ)} {L : ℝ≥0}
    (hlip : LipschitzOnWith L f K) (hsup : ∀ a ∈ K, ∀ b ∈ K, a ⊔ b ∈ K) (hk : KamkeOn f K)
    {T : ℝ} {x y : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (f (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (f (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ K) (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ K)
    (h0 : x 0 ≤ y 0) : ∀ t ∈ Set.Icc 0 T, x t ≤ y t := by
  set D := Set.Icc (0 : ℝ) T
  set C : ℝ := 2 * L * Fintype.card S
  let w : ℝ → S → ℝ := fun t i => max (x t i - y t i) 0
  let V : ℝ → ℝ := fun t => ∑ i, (w t i) ^ 2
  have hV0 : ∀ t, 0 ≤ V t := fun t => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hw_le : ∀ t i, w t i ≤ Real.sqrt (V t) := by
    intro t i
    rw [Real.le_sqrt (le_max_right _ _) (hV0 t)]
    exact Finset.single_le_sum (f := fun i => (w t i) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  -- derivative of `V`
  have hVd : ∀ t ∈ D, HasDerivWithinAt V
      (∑ i, 2 * w t i * (f (x t) i - f (y t) i)) D t := by
    intro t ht
    refine HasDerivWithinAt.fun_sum fun i _ => ?_
    have hxi := (hasDerivWithinAt_pi.mp (hx t ht)) i
    have hyi := (hasDerivWithinAt_pi.mp (hy t ht)) i
    exact (hasDerivAt_posPart_sq (x t i - y t i)).comp_hasDerivWithinAt t (hxi.sub hyi)
  -- the differential inequality `V' ≤ C V`
  have hVineq : ∀ t ∈ D, (∑ i, 2 * w t i * (f (x t) i - f (y t) i)) ≤ C * V t := by
    intro t ht
    set z := x t ⊔ y t
    have hzK : z ∈ K := hsup _ (hxK t ht) _ (hyK t ht)
    have hzy : ‖z - y t‖ ≤ Real.sqrt (V t) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr fun i => ?_
      have : (z - y t) i = w t i := by
        simp only [z, Pi.sub_apply, Pi.sup_apply, w]
        rcases le_total (x t i) (y t i) with h | h
        · rw [max_eq_right h, max_eq_right (by linarith)]; ring
        · rw [max_eq_left h, max_eq_left (by linarith)]
      rw [this, Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
      exact hw_le t i
    have hfl : ‖f z - f (y t)‖ ≤ L * Real.sqrt (V t) :=
      (hlip.norm_sub_le hzK (hyK t ht)).trans (mul_le_mul_of_nonneg_left hzy L.2)
    have hterm : ∀ i, 2 * w t i * (f (x t) i - f (y t) i) ≤
        2 * L * Real.sqrt (V t) * Real.sqrt (V t) := by
      intro i
      by_cases hpos : 0 < x t i - y t i
      · have hwi : w t i = x t i - y t i := max_eq_left hpos.le
        have hxz : x t ≤ z := le_sup_left
        have hxi : x t i = z i := by
          simp only [z, Pi.sup_apply]
          exact (max_eq_left (by linarith)).symm
        have h1 : f (x t) i ≤ f z i := hk _ (hxK t ht) _ hzK hxz i hxi
        have h2 : f z i - f (y t) i ≤ L * Real.sqrt (V t) := by
          have := norm_le_pi_norm (f z - f (y t)) i
          rw [Pi.sub_apply, Real.norm_eq_abs] at this
          linarith [le_abs_self (f z i - f (y t) i)]
        have hw0 : 0 ≤ w t i := le_max_right _ _
        calc 2 * w t i * (f (x t) i - f (y t) i) ≤ 2 * w t i * (L * Real.sqrt (V t)) :=
              mul_le_mul_of_nonneg_left (by linarith) (by positivity)
          _ ≤ 2 * Real.sqrt (V t) * (L * Real.sqrt (V t)) := by
              have := hw_le t i
              have : 0 ≤ (L : ℝ) * Real.sqrt (V t) := by positivity
              nlinarith
          _ = 2 * L * Real.sqrt (V t) * Real.sqrt (V t) := by ring
      · have hwi : w t i = 0 := max_eq_right (not_lt.mp hpos)
        rw [hwi, mul_zero, zero_mul]
        positivity
    calc (∑ i, 2 * w t i * (f (x t) i - f (y t) i))
        ≤ ∑ _i : S, 2 * L * Real.sqrt (V t) * Real.sqrt (V t) :=
          Finset.sum_le_sum fun i _ => hterm i
      _ = C * V t := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_assoc (2 * (L : ℝ)),
            Real.mul_self_sqrt (hV0 t)]
          simp only [C]; ring
  -- `e^{-Ct} V(t)` is antitone, hence `V ≡ 0`
  let g : ℝ → ℝ := fun t => Real.exp (-C * t) * V t
  have hgd : ∀ t ∈ D, HasDerivWithinAt g
      (Real.exp (-C * t) * (-C) * V t +
        Real.exp (-C * t) * ∑ i, 2 * w t i * (f (x t) i - f (y t) i)) D t := by
    intro t ht
    have he : HasDerivWithinAt (fun t => Real.exp (-C * t)) (Real.exp (-C * t) * (-C)) D t := by
      have := ((hasDerivAt_id t).const_mul (-C)).exp
      simpa using this.hasDerivWithinAt
    exact he.mul (hVd t ht)
  have hanti : AntitoneOn g D := by
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 T)
      (fun t ht => (hgd t ht).continuousWithinAt)
      (fun t ht => (hgd t (interior_subset ht)).mono interior_subset) ?_
    intro t ht
    have := hVineq t (interior_subset ht)
    have hep := Real.exp_pos (-C * t)
    nlinarith [mul_le_mul_of_nonneg_left this hep.le]
  have hV00 : V 0 = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    have : x 0 i - y 0 i ≤ 0 := by linarith [h0 i]
    simp [w, max_eq_right this]
  intro t ht
  have h0D : (0 : ℝ) ∈ D := ⟨le_rfl, ht.1.trans ht.2⟩
  have hgt : g t ≤ g 0 := hanti h0D ht ht.1
  simp only [g, mul_zero, Real.exp_zero, hV00] at hgt
  have hVt : V t = 0 := by
    have := Real.exp_pos (-C * t)
    have : V t ≤ 0 := by nlinarith [hV0 t]
    linarith [hV0 t]
  intro i
  have hwi : w t i ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w t j))).mp hVt i (Finset.mem_univ i)
  have : max (x t i - y t i) 0 = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hwi
  have := le_max_left (x t i - y t i) 0
  linarith

end Monotone

end CRNT
