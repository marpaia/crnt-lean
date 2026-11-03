import CRNT.Dynamics.MonotoneComparison
import CRNT.Dynamics.CooperativeNetworks
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Logic.Relation

/-!
# Strong monotonicity of irreducible cooperative systems

A cooperative system whose influence graph is strongly connected is **strongly order-preserving**:
if `x(0) ≤ y(0)` and `x(0) ≠ y(0)`, then `x(t) ≪ y(t)` (strictly in every coordinate) for every
`t > 0` (Smith, *Monotone Dynamical Systems*, Theorem 4.1.1, in a derivative-free form).

The hypotheses are one-sided difference bounds on a set `K` closed under `⊔`:

* `f b i − f a i ≥ −L (b i − a i)` for `a ≤ b` (cooperativity with a Lipschitz diagonal); this
  implies the Kamke condition, so `z = y − x ≥ 0` (`kamke_comparison`);
* `f b i − f a i ≥ −L (b i − a i) + c (b j − a j)` along the edges `j → i` of a strongly connected
  influence graph (irreducibility).

Then `e^{Lt} z_i` is nondecreasing, so a positive coordinate stays positive
(`coord_pos_of_pos`), and along an edge `j → i` it is strictly increasing once `z_j > 0`, so
positivity spreads (`coord_pos_of_edge`); strong connectivity gives `z(t) ≫ 0` for `t > 0`
(`strong_order_preserving`).
-/

open Set Filter
open scoped Topology NNReal

namespace CRNT
namespace Monotone

variable {S : Type} [DecidableEq S] [Fintype S]

section

variable {f : (S → ℝ) → (S → ℝ)} {K : Set (S → ℝ)} {L : ℝ≥0} {T : ℝ} {x y : ℝ → (S → ℝ)}

/-- The weighted gap `e^{Lt} (y_i − x_i)` has derivative
`e^{Lt} (f_i(y) − f_i(x) + L (y_i − x_i))` on `[0, T]`. -/
theorem hasDerivWithinAt_weightedGap
    (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (f (x t)) (Icc 0 T) t)
    (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (f (y t)) (Icc 0 T) t) (i : S) {t : ℝ}
    (ht : t ∈ Icc 0 T) :
    HasDerivWithinAt (fun t => Real.exp (L * t) * (y t i - x t i))
      (Real.exp (L * t) * (f (y t) i - f (x t) i + L * (y t i - x t i))) (Icc 0 T) t := by
  have hxi := (hasDerivWithinAt_pi.mp (hx t ht)) i
  have hyi := (hasDerivWithinAt_pi.mp (hy t ht)) i
  have he : HasDerivWithinAt (fun t => Real.exp (L * t)) (Real.exp (L * t) * L) (Icc 0 T) t := by
    have := ((hasDerivAt_id t).const_mul (L : ℝ)).exp
    simpa using this.hasDerivWithinAt
  have := he.mul (hyi.sub hxi)
  convert this using 1
  simp only [Pi.sub_apply]
  ring

/-- Restriction of the derivative to the interior of a subinterval. -/
theorem hasDerivWithinAt_interior_of_Icc {g : ℝ → ℝ} {g' : ℝ → ℝ} {t₀ : ℝ} (ht₀ : 0 ≤ t₀)
    (hg : ∀ t ∈ Icc 0 T, HasDerivWithinAt g (g' t) (Icc 0 T) t) :
    ∀ t ∈ interior (Icc t₀ T), HasDerivWithinAt g (g' t) (interior (Icc t₀ T)) t := by
  intro t ht
  rw [interior_Icc] at ht ⊢
  have hmem : Icc 0 T ∈ 𝓝 t := Icc_mem_nhds (by linarith [ht.1]) ht.2
  exact ((hg t ⟨by linarith [ht.1], ht.2.le⟩).hasDerivAt hmem).hasDerivWithinAt

variable (hlip : LipschitzOnWith L f K) (hsup : ∀ a ∈ K, ∀ b ∈ K, a ⊔ b ∈ K)
  (hL : ∀ a ∈ K, ∀ b ∈ K, a ≤ b → ∀ i, -(L : ℝ) * (b i - a i) ≤ f b i - f a i)
  (hx : ∀ t ∈ Icc 0 T, HasDerivWithinAt x (f (x t)) (Icc 0 T) t)
  (hy : ∀ t ∈ Icc 0 T, HasDerivWithinAt y (f (y t)) (Icc 0 T) t)
  (hxK : ∀ t ∈ Icc 0 T, x t ∈ K) (hyK : ∀ t ∈ Icc 0 T, y t ∈ K) (h0 : x 0 ≤ y 0)
include hlip hsup hL hx hy hxK hyK h0

/-- The gap stays nonnegative. -/
theorem gap_nonneg : ∀ t ∈ Icc 0 T, x t ≤ y t := by
  have hk : KamkeOn f K := fun a ha b hb hab i hi => by
    have := hL a ha b hb hab i
    rw [hi, sub_self, mul_zero] at this
    linarith
  exact kamke_comparison hlip hsup hk hx hy hxK hyK h0

/-- **A positive coordinate of the gap stays positive.** -/
theorem coord_pos_of_pos (i : S) {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (hpos : x t₀ i < y t₀ i) :
    ∀ t ∈ Icc t₀ T, x t i < y t i := by
  have hgap := gap_nonneg hlip hsup hL hx hy hxK hyK h0
  set g : ℝ → ℝ := fun t => Real.exp (L * t) * (y t i - x t i) with hg
  have hmono : MonotoneOn g (Icc t₀ T) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _) ?_
      (hasDerivWithinAt_interior_of_Icc ht₀.1 fun t ht =>
        hasDerivWithinAt_weightedGap hx hy i ht) ?_
    · intro t ht
      exact (hasDerivWithinAt_weightedGap hx hy i ⟨ht₀.1.trans ht.1, ht.2⟩).continuousWithinAt.mono
        (Icc_subset_Icc ht₀.1 le_rfl)
    · intro t ht
      rw [interior_Icc] at ht
      have htI : t ∈ Icc 0 T := ⟨by linarith [ht₀.1, ht.1], ht.2.le⟩
      have h1 := hL (x t) (hxK t htI) (y t) (hyK t htI) (hgap t htI) i
      have : 0 ≤ f (y t) i - f (x t) i + L * (y t i - x t i) := by linarith
      exact mul_nonneg (Real.exp_pos _).le this
  intro t ht
  have h1 := hmono ⟨le_rfl, ht₀.2⟩ ht ht.1
  have h2 : 0 < g t₀ := mul_pos (Real.exp_pos _) (by linarith)
  have h3 : 0 < g t := lt_of_lt_of_le h2 h1
  have h4 : 0 < y t i - x t i := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h3
  linarith

/-- **Positivity spreads along an edge.** -/
theorem coord_pos_of_edge {c : ℝ} (hc : 0 < c) (i j : S)
    (hG : ∀ a ∈ K, ∀ b ∈ K, a ≤ b → -(L : ℝ) * (b i - a i) + c * (b j - a j) ≤ f b i - f a i)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) (hpos : x t₀ j < y t₀ j) :
    ∀ t ∈ Ioc t₀ T, x t i < y t i := by
  have hgap := gap_nonneg hlip hsup hL hx hy hxK hyK h0
  have hj := coord_pos_of_pos hlip hsup hL hx hy hxK hyK h0 j ht₀ hpos
  set g : ℝ → ℝ := fun t => Real.exp (L * t) * (y t i - x t i) with hg
  have hstrict : StrictMonoOn g (Icc t₀ T) := by
    refine strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc _ _) ?_
      (hasDerivWithinAt_interior_of_Icc ht₀.1 fun t ht =>
        hasDerivWithinAt_weightedGap hx hy i ht) ?_
    · intro t ht
      exact (hasDerivWithinAt_weightedGap hx hy i ⟨ht₀.1.trans ht.1, ht.2⟩).continuousWithinAt.mono
        (Icc_subset_Icc ht₀.1 le_rfl)
    · intro t ht
      rw [interior_Icc] at ht
      have htI : t ∈ Icc 0 T := ⟨by linarith [ht₀.1, ht.1], ht.2.le⟩
      have h1 := hG (x t) (hxK t htI) (y t) (hyK t htI) (hgap t htI)
      have h2 := hj t ⟨ht.1.le, ht.2.le⟩
      have : 0 < f (y t) i - f (x t) i + L * (y t i - x t i) := by nlinarith
      exact mul_pos (Real.exp_pos _) this
  intro t ht
  have h1 := hstrict ⟨le_rfl, ht₀.2⟩ ⟨ht.1.le, ht.2⟩ ht.1
  have h2 : 0 ≤ g t₀ := mul_nonneg (Real.exp_pos _).le (by
    have := hgap t₀ ht₀ i; linarith)
  have h3 : 0 < g t := lt_of_le_of_lt h2 h1
  have h4 : 0 < y t i - x t i := (mul_pos_iff_of_pos_left (Real.exp_pos _)).mp h3
  linarith

/-- **Strong order preservation for irreducible cooperative systems.** If the influence graph `E`
(`E i j`: `j` influences `i`) is strongly connected and the edge bounds hold, then
`x(0) ≤ y(0)`, `x(0) ≠ y(0)` imply `x(t) ≪ y(t)` for every `t ∈ (0, T]`. -/
theorem strong_order_preserving (E : S → S → Prop)
    (hE : ∀ i j, Relation.ReflTransGen (fun j i => E i j) j i) {c : ℝ} (hc : 0 < c)
    (hG : ∀ i j, E i j → ∀ a ∈ K, ∀ b ∈ K, a ≤ b →
      -(L : ℝ) * (b i - a i) + c * (b j - a j) ≤ f b i - f a i)
    (hne : x 0 ≠ y 0) : ∀ t ∈ Ioc 0 T, ∀ i, x t i < y t i := by
  have hgap := gap_nonneg hlip hsup hL hx hy hxK hyK h0
  obtain ⟨j₀, hj₀⟩ : ∃ j₀, x 0 j₀ < y 0 j₀ := by
    by_contra h
    push Not at h
    exact hne (funext fun j => le_antisymm (h0 j) (h j))
  intro t ht i
  have key : ∀ k, Relation.ReflTransGen (fun j i => E i j) j₀ k → ∀ s ∈ Ioc 0 T, x s k < y s k := by
    intro k hk
    induction hk with
    | refl =>
        intro s hs
        have hT : 0 ≤ T := by linarith [hs.1, hs.2]
        exact coord_pos_of_pos hlip hsup hL hx hy hxK hyK h0 j₀ ⟨le_rfl, hT⟩ hj₀ s
          ⟨hs.1.le, hs.2⟩
    | tail _ hedge ih =>
        intro s hs
        have hs2 : s / 2 ∈ Ioc 0 T := ⟨by linarith [hs.1], by linarith [hs.1, hs.2]⟩
        exact coord_pos_of_edge hlip hsup hL hx hy hxK hyK h0 hc _ _ (hG _ _ hedge)
          ⟨hs2.1.le, hs2.2⟩ (ih (s / 2) hs2) s ⟨by linarith [hs.1], hs.2⟩
  exact key i (hE i j₀) t ht

end

end Monotone
end CRNT

namespace CRNT
namespace Network

open Monotone

variable {S : Type} [DecidableEq S] [Fintype S]

/-- `b^m − a^m ≥ a^{m−1}(b − a)` for `0 ≤ a ≤ b`, `m ≥ 1`. -/
theorem pow_sub_pow_ge {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {m : ℕ} (hm : 1 ≤ m) :
    a ^ (m - 1) * (b - a) ≤ b ^ m - a ^ m := by
  induction m with
  | zero => omega
  | succ m ih =>
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h; simp
    · have ih' := ih h
      have hb : 0 ≤ b := ha.trans hab
      have h1 : a ^ m ≤ b ^ m := pow_le_pow_left₀ ha hab m
      have e1 : b ^ (m + 1) - a ^ (m + 1) = b * (b ^ m - a ^ m) + a ^ m * (b - a) := by ring
      have e2 : m + 1 - 1 = m := by omega
      rw [e1, e2]
      have : 0 ≤ b * (b ^ m - a ^ m) := mul_nonneg hb (by linarith)
      linarith

/-- `b^m − a^m ≤ m M^m (b − a)` for `0 ≤ a ≤ b ≤ M`, `M ≥ 1`. -/
theorem pow_sub_pow_le {a b M : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbM : b ≤ M) (hM : 1 ≤ M)
    (m : ℕ) : b ^ m - a ^ m ≤ m * M ^ m * (b - a) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hb : 0 ≤ b := ha.trans hab
    have e1 : b ^ (m + 1) - a ^ (m + 1) = b * (b ^ m - a ^ m) + a ^ m * (b - a) := by ring
    rw [e1]
    have h1 : b * (b ^ m - a ^ m) ≤ M * (m * M ^ m * (b - a)) := by
      have hnn : 0 ≤ b ^ m - a ^ m := by linarith [pow_le_pow_left₀ ha hab m]
      calc b * (b ^ m - a ^ m) ≤ M * (b ^ m - a ^ m) := mul_le_mul_of_nonneg_right hbM hnn
        _ ≤ M * (m * M ^ m * (b - a)) := mul_le_mul_of_nonneg_left ih (by linarith)
    have h2 : a ^ m * (b - a) ≤ M ^ (m + 1) * (b - a) := by
      apply mul_le_mul_of_nonneg_right _ (by linarith)
      calc a ^ m ≤ M ^ m := pow_le_pow_left₀ ha (hab.trans hbM) m
        _ ≤ M ^ (m + 1) := pow_le_pow_right₀ hM (by omega)
    have e3 : M * (m * M ^ m * (b - a)) = m * M ^ (m + 1) * (b - a) := by ring
    push_cast
    nlinarith

/-- The monomial is monotone in a positive box. -/
theorem massActionMonomial_sub_ge {y : Complex S} {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    {a b : Concentration S} (ha : ∀ k, δ ≤ a k) (hab : a ≤ b) {j : S} (hj : 0 < y j) :
    δ ^ (∑ k, y k) * (b j - a j) ≤ y.massActionMonomial b - y.massActionMonomial a := by
  classical
  have ha0 : ∀ k, 0 ≤ a k := fun k => hδ.le.trans (ha k)
  -- replace the `j`-th coordinate of `a` by that of `b`
  set a' : Concentration S := Function.update a j (b j) with ha'
  have haa' : a ≤ a' := fun k => by
    by_cases h : k = j
    · subst h; simp [ha', hab k]
    · simp [ha', Function.update_of_ne h]
  have ha'b : a' ≤ b := fun k => by
    by_cases h : k = j
    · subst h; simp [ha']
    · simp [ha', Function.update_of_ne h, hab k]
  have h1 : y.massActionMonomial a' ≤ y.massActionMonomial b :=
    massActionMonomial_mono (fun k => (ha0 k).trans (haa' k)) ha'b
  have hprod : ∀ c : Concentration S, y.massActionMonomial c =
      (∏ k ∈ Finset.univ.erase j, c k ^ y k) * c j ^ y j := fun c => by
    unfold Complex.massActionMonomial
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).symm
  have hrest : ∏ k ∈ Finset.univ.erase j, a' k ^ y k = ∏ k ∈ Finset.univ.erase j, a k ^ y k :=
    Finset.prod_congr rfl fun k hk => by
      rw [ha', Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  have h2 : y.massActionMonomial a' - y.massActionMonomial a =
      (∏ k ∈ Finset.univ.erase j, a k ^ y k) * (b j ^ y j - a j ^ y j) := by
    rw [hprod a', hprod a, hrest]
    simp only [ha', Function.update_self]
    ring
  have h3 : a j ^ (y j - 1) * (b j - a j) ≤ b j ^ y j - a j ^ y j :=
    pow_sub_pow_ge (ha0 j) (hab j) hj
  have hδpow : ∀ m : ℕ, ∀ c : ℝ, δ ≤ c → δ ^ m ≤ c ^ m := fun m c hc =>
    pow_le_pow_left₀ hδ.le hc m
  have hrestge : δ ^ (∑ k ∈ Finset.univ.erase j, y k) ≤ ∏ k ∈ Finset.univ.erase j, a k ^ y k := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_le_prod₀ (fun k _ => by positivity) fun k _ => hδpow _ _ (ha k)
  have hsum : (∑ k ∈ Finset.univ.erase j, y k) + (y j - 1) ≤ ∑ k, y k := by
    have := Finset.sum_erase_add (s := Finset.univ) (f := fun k => y k) (Finset.mem_univ j)
    omega
  have hδtot : δ ^ (∑ k, y k) ≤ δ ^ (∑ k ∈ Finset.univ.erase j, y k) * δ ^ (y j - 1) := by
    rw [← pow_add]; exact pow_le_pow_of_le_one hδ.le hδ1 hsum
  have hgap : 0 ≤ b j - a j := by linarith [hab j]
  calc δ ^ (∑ k, y k) * (b j - a j)
      ≤ δ ^ (∑ k ∈ Finset.univ.erase j, y k) * δ ^ (y j - 1) * (b j - a j) :=
        mul_le_mul_of_nonneg_right hδtot hgap
    _ ≤ (∏ k ∈ Finset.univ.erase j, a k ^ y k) * (a j ^ (y j - 1) * (b j - a j)) := by
        rw [mul_assoc]
        exact mul_le_mul hrestge (mul_le_mul_of_nonneg_right (hδpow _ _ (ha j)) hgap)
          (by positivity) (Finset.prod_nonneg fun k _ => pow_nonneg (ha0 k) _)
    _ ≤ (∏ k ∈ Finset.univ.erase j, a k ^ y k) * (b j ^ y j - a j ^ y j) :=
        mul_le_mul_of_nonneg_left h3 (Finset.prod_nonneg fun k _ => pow_nonneg (ha0 k) _)
    _ = y.massActionMonomial a' - y.massActionMonomial a := h2.symm
    _ ≤ y.massActionMonomial b - y.massActionMonomial a := by linarith

/-- A monomial supported on `{i}` grows at most linearly in `b_i − a_i` on `[0, M]`. -/
theorem massActionMonomial_sub_le_of_support {y : Complex S} {i : S}
    (hy : ∀ j, j ≠ i → y j = 0) {M : ℝ} (hM : 1 ≤ M) {a b : Concentration S}
    (ha : ∀ k, 0 ≤ a k) (hab : a ≤ b) (hbM : ∀ k, b k ≤ M) :
    y.massActionMonomial b - y.massActionMonomial a ≤ y i * M ^ y i * (b i - a i) := by
  have hmono : ∀ c : Concentration S, y.massActionMonomial c = c i ^ y i := fun c => by
    unfold Complex.massActionMonomial
    rw [Finset.prod_eq_single i (fun j _ hj => by rw [hy j hj, pow_zero]) (by simp)]
  rw [hmono b, hmono a]
  exact pow_sub_pow_le (ha i) (hab i) (hbM i) hM (y i)

/-- The influence graph: `j` influences `i` if some reaction produces `i` and consumes `j`. -/
def InfluenceEdge (N : Network S) (i j : S) : Prop :=
  ∃ r, 0 < N.reactionVector r i ∧ 0 < (N.reaction r).source j

/-- The diagonal constant. -/
noncomputable def coopL (N : Network S) (κ : N.RateConstants) (M : ℝ) : ℝ :=
  ∑ r, ∑ i, κ.k r * |N.reactionVector r i| * ((N.reaction r).source i * M ^ (N.reaction r).source i)

theorem coopL_nonneg (N : Network S) (κ : N.RateConstants) {M : ℝ} (hM : 1 ≤ M) :
    0 ≤ coopL N κ M := by
  unfold coopL
  refine Finset.sum_nonneg fun r _ => Finset.sum_nonneg fun i _ => ?_
  have : 0 ≤ M := by linarith
  have := (κ.positive r).le
  positivity

/-- **The diagonal bound** for cooperative networks on a box. -/
theorem coop_diag_bound (N : Network S) (κ : N.RateConstants) (hcoop : N.IsCooperativeNetwork)
    {M : ℝ} (hM : 1 ≤ M) {a b : Concentration S} (ha : ∀ k, 0 ≤ a k) (hab : a ≤ b)
    (hbM : ∀ k, b k ≤ M) (i : S) :
    -coopL N κ M * (b i - a i) ≤
      N.massActionVectorField κ b i - N.massActionVectorField κ a i := by
  rw [massActionVectorField_apply, massActionVectorField_apply, ← Finset.sum_sub_distrib]
  have hgap : 0 ≤ b i - a i := by linarith [hab i]
  have hterm : ∀ r, -(κ.k r * |N.reactionVector r i| *
      ((N.reaction r).source i * M ^ (N.reaction r).source i)) * (b i - a i) ≤
      N.massActionRate κ r b * N.reactionVector r i - N.massActionRate κ r a * N.reactionVector r i := by
    intro r
    simp only [massActionRate]
    have hk := (κ.positive r).le
    rcases lt_or_ge (N.reactionVector r i) 0 with hneg | hnn
    · have hsupp := hcoop r i hneg
      have h1 := massActionMonomial_sub_le_of_support hsupp hM ha hab hbM
      rw [abs_of_neg hneg]
      have e : κ.k r * (N.reaction r).source.massActionMonomial b * N.reactionVector r i -
          κ.k r * (N.reaction r).source.massActionMonomial a * N.reactionVector r i =
          κ.k r * N.reactionVector r i * ((N.reaction r).source.massActionMonomial b -
            (N.reaction r).source.massActionMonomial a) := by ring
      rw [e]
      have h2 : κ.k r * N.reactionVector r i * ((N.reaction r).source i * M ^ (N.reaction r).source i *
          (b i - a i)) ≤ κ.k r * N.reactionVector r i * ((N.reaction r).source.massActionMonomial b -
            (N.reaction r).source.massActionMonomial a) :=
        mul_le_mul_of_nonpos_left h1 (mul_nonpos_of_nonneg_of_nonpos hk hneg.le)
      nlinarith
    · have hmono := massActionMonomial_mono (y := (N.reaction r).source) ha hab
      have h0 : 0 ≤ κ.k r * (N.reaction r).source.massActionMonomial b * N.reactionVector r i -
          κ.k r * (N.reaction r).source.massActionMonomial a * N.reactionVector r i := by
        have : 0 ≤ κ.k r * ((N.reaction r).source.massActionMonomial b -
            (N.reaction r).source.massActionMonomial a) * N.reactionVector r i :=
          mul_nonneg (mul_nonneg hk (by linarith)) hnn
        linarith
      have h3 : 0 ≤ κ.k r * |N.reactionVector r i| *
          ((N.reaction r).source i * M ^ (N.reaction r).source i) * (b i - a i) := by
        have : 0 ≤ M := by linarith
        positivity
      linarith
  have hsum := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hterm r
  have hL : coopL N κ M * (b i - a i) ≥ ∑ r, κ.k r * |N.reactionVector r i| *
      ((N.reaction r).source i * M ^ (N.reaction r).source i) * (b i - a i) := by
    unfold coopL
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun r _ => ?_
    rw [Finset.sum_mul]
    refine Finset.single_le_sum (f := fun i' => κ.k r * |N.reactionVector r i'| *
      ((N.reaction r).source i' * M ^ (N.reaction r).source i') * (b i - a i))
      (fun i' _ => ?_) (Finset.mem_univ i)
    have : 0 ≤ M := by linarith
    have := (κ.positive r).le
    positivity
  have e : ∑ r, -(κ.k r * |N.reactionVector r i| *
      ((N.reaction r).source i * M ^ (N.reaction r).source i)) * (b i - a i) =
      -(∑ r, κ.k r * |N.reactionVector r i| *
        ((N.reaction r).source i * M ^ (N.reaction r).source i) * (b i - a i)) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun r _ => by ring
  rw [e] at hsum
  linarith


/-- A lower bound for all rates, `∏_r min(κ_r, 1)`. -/
noncomputable def kLow (N : Network S) (κ : N.RateConstants) : ℝ := ∏ r, min (κ.k r) 1

theorem kLow_pos (N : Network S) (κ : N.RateConstants) : 0 < kLow N κ :=
  Finset.prod_pos fun r _ => lt_min (κ.positive r) one_pos

theorem kLow_le (N : Network S) (κ : N.RateConstants) (r : N.R) : kLow N κ ≤ κ.k r := by
  unfold kLow
  have h1 : ∏ r', min (κ.k r') 1 ≤ min (κ.k r) 1 := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ r)]
    have hle : ∏ r' ∈ Finset.univ.erase r, min (κ.k r') 1 ≤ 1 :=
      Finset.prod_le_one₀ (fun r' _ => (lt_min (κ.positive r') one_pos).le)
        fun r' _ => min_le_right _ _
    have h0 : 0 ≤ min (κ.k r) 1 := (lt_min (κ.positive r) one_pos).le
    nlinarith
  exact h1.trans (min_le_left _ _)

/-- The total source degree. -/
def srcDeg (N : Network S) : ℕ := ∑ r, ∑ k, (N.reaction r).source k

/-- **The edge bound** for cooperative networks on a positive box. -/
theorem coop_edge_bound (N : Network S) (κ : N.RateConstants) (hcoop : N.IsCooperativeNetwork)
    {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 1 ≤ M) {a b : Concentration S}
    (ha : ∀ k, δ ≤ a k) (hab : a ≤ b) (hbM : ∀ k, b k ≤ M) {i j : S}
    (hedge : N.InfluenceEdge i j) :
    -coopL N κ M * (b i - a i) + kLow N κ * δ ^ srcDeg N * (b j - a j) ≤
      N.massActionVectorField κ b i - N.massActionVectorField κ a i := by
  classical
  obtain ⟨r₀, hΔ, hsrc⟩ := hedge
  have ha0 : ∀ k, 0 ≤ a k := fun k => hδ.le.trans (ha k)
  rw [massActionVectorField_apply, massActionVectorField_apply, ← Finset.sum_sub_distrib]
  set term : N.R → ℝ := fun r =>
    N.massActionRate κ r b * N.reactionVector r i - N.massActionRate κ r a * N.reactionVector r i
    with hterm
  set dg : N.R → ℝ := fun r => κ.k r * |N.reactionVector r i| *
    ((N.reaction r).source i * M ^ (N.reaction r).source i) * (b i - a i) with hdg
  have hgap : 0 ≤ b i - a i := by linarith [hab i]
  have hgapj : 0 ≤ b j - a j := by linarith [hab j]
  -- each term is at least the diagonal loss
  have hall : ∀ r, -dg r ≤ term r := by
    intro r
    simp only [hterm, hdg, massActionRate]
    have hk := (κ.positive r).le
    rcases lt_or_ge (N.reactionVector r i) 0 with hneg | hnn
    · have h1 := massActionMonomial_sub_le_of_support (hcoop r i hneg) hM ha0 hab hbM
      rw [abs_of_neg hneg]
      have h2 := mul_le_mul_of_nonpos_left h1 (mul_nonpos_of_nonneg_of_nonpos hk hneg.le)
      nlinarith
    · have hmono := massActionMonomial_mono (y := (N.reaction r).source) ha0 hab
      have : 0 ≤ κ.k r * ((N.reaction r).source.massActionMonomial b -
          (N.reaction r).source.massActionMonomial a) * N.reactionVector r i :=
        mul_nonneg (mul_nonneg hk (by linarith)) hnn
      have h3 : 0 ≤ κ.k r * |N.reactionVector r i| *
          ((N.reaction r).source i * M ^ (N.reaction r).source i) * (b i - a i) := by
        have : 0 ≤ M := by linarith
        positivity
      nlinarith
  -- the edge reaction gains
  have hr₀ : kLow N κ * δ ^ srcDeg N * (b j - a j) ≤ term r₀ := by
    simp only [hterm, massActionRate]
    have hm := massActionMonomial_sub_ge (y := (N.reaction r₀).source) hδ hδ1 ha hab hsrc
    have hΔ1 : 1 ≤ N.reactionVector r₀ i := by
      rw [reactionVector_apply] at hΔ ⊢
      have h1 : ((N.reaction r₀).source i : ℝ) < (N.reaction r₀).target i := by linarith
      have h2 : (N.reaction r₀).source i < (N.reaction r₀).target i := by exact_mod_cast h1
      have h3 : ((N.reaction r₀).source i : ℝ) + 1 ≤ (N.reaction r₀).target i := by
        exact_mod_cast h2
      linarith
    have hdeg : δ ^ srcDeg N ≤ δ ^ (∑ k, (N.reaction r₀).source k) := by
      apply pow_le_pow_of_le_one hδ.le hδ1
      unfold srcDeg
      exact Finset.single_le_sum (f := fun r => ∑ k, (N.reaction r).source k) (fun r _ => Nat.zero_le _)
        (Finset.mem_univ r₀)
    have hkl := kLow_le N κ r₀
    have hkl0 := (kLow_pos N κ).le
    have e : κ.k r₀ * (N.reaction r₀).source.massActionMonomial b * N.reactionVector r₀ i -
        κ.k r₀ * (N.reaction r₀).source.massActionMonomial a * N.reactionVector r₀ i =
        κ.k r₀ * N.reactionVector r₀ i * ((N.reaction r₀).source.massActionMonomial b -
          (N.reaction r₀).source.massActionMonomial a) := by ring
    rw [e]
    have hδp : 0 ≤ δ ^ srcDeg N := by positivity
    calc kLow N κ * δ ^ srcDeg N * (b j - a j)
        ≤ κ.k r₀ * 1 * (δ ^ (∑ k, (N.reaction r₀).source k) * (b j - a j)) := by
          rw [mul_one, ← mul_assoc]
          exact mul_le_mul_of_nonneg_right (mul_le_mul hkl hdeg hδp (κ.positive r₀).le) hgapj
      _ ≤ κ.k r₀ * N.reactionVector r₀ i * ((N.reaction r₀).source.massActionMonomial b -
            (N.reaction r₀).source.massActionMonomial a) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hΔ1 (κ.positive r₀).le) hm (by positivity)
            (by nlinarith [(κ.positive r₀).le])
  -- combine
  have hsplit : ∑ r, term r = term r₀ + ∑ r ∈ Finset.univ.erase r₀, term r :=
    (Finset.add_sum_erase _ _ (Finset.mem_univ r₀)).symm
  have hrest : -(∑ r ∈ Finset.univ.erase r₀, dg r) ≤ ∑ r ∈ Finset.univ.erase r₀, term r := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun r _ => hall r
  have hdg0 : ∀ r, 0 ≤ dg r := fun r => by
    simp only [hdg]
    have : 0 ≤ M := by linarith
    have := (κ.positive r).le
    positivity
  have hLsum : ∑ r ∈ Finset.univ.erase r₀, dg r ≤ coopL N κ M * (b i - a i) := by
    calc ∑ r ∈ Finset.univ.erase r₀, dg r ≤ ∑ r, dg r :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun r _ _ => hdg0 r
      _ ≤ coopL N κ M * (b i - a i) := by
          unfold coopL
          rw [Finset.sum_mul]
          refine Finset.sum_le_sum fun r _ => ?_
          rw [Finset.sum_mul]
          refine Finset.single_le_sum (f := fun i' => κ.k r * |N.reactionVector r i'| *
            ((N.reaction r).source i' * M ^ (N.reaction r).source i') * (b i - a i))
            (fun i' _ => ?_) (Finset.mem_univ i)
          have : 0 ≤ M := by linarith
          have := (κ.positive r).le
          positivity
  show -coopL N κ M * (b i - a i) + kLow N κ * δ ^ srcDeg N * (b j - a j) ≤ ∑ r, term r
  rw [hsplit]
  linarith

/-- **Strong order preservation for irreducible cooperative mass-action networks.** If the
network is cooperative and its influence graph is strongly connected, two solutions in a positive
box `[δ, M]^S` with `x(0) ≤ y(0)`, `x(0) ≠ y(0)` satisfy `x(t) ≪ y(t)` for all `t ∈ (0, T]`. -/
theorem massAction_strong_order_preserving (N : Network S) (κ : N.RateConstants)
    (hcoop : N.IsCooperativeNetwork)
    (hE : ∀ i j, Relation.ReflTransGen (fun j i => N.InfluenceEdge i j) j i)
    {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 1 ≤ M) {T : ℝ} {x y : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ Set.Icc (fun _ => δ) (fun _ => M))
    (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ Set.Icc (fun _ => δ) (fun _ => M))
    (h0 : x 0 ≤ y 0) (hne : x 0 ≠ y 0) : ∀ t ∈ Set.Ioc 0 T, ∀ i, x t i < y t i := by
  set K : Set (Concentration S) := Set.Icc (fun _ => δ) (fun _ => M) with hK
  obtain ⟨L₁, hL₁⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn (s := K)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  set L : ℝ≥0 := max L₁ ⟨coopL N κ M, coopL_nonneg N κ hM⟩ with hLdef
  have hlip : LipschitzOnWith L (N.massActionVectorField κ) K := hL₁.weaken (le_max_left _ _)
  have hLge : coopL N κ M ≤ (L : ℝ) := by
    have : (⟨coopL N κ M, coopL_nonneg N κ hM⟩ : ℝ≥0) ≤ L := le_max_right _ _
    exact_mod_cast this
  have hsup : ∀ a ∈ K, ∀ b ∈ K, a ⊔ b ∈ K := fun a ha b hb =>
    ⟨fun k => le_sup_of_le_left (ha.1 k), fun k => sup_le (ha.2 k) (hb.2 k)⟩
  have hdiag : ∀ a ∈ K, ∀ b ∈ K, a ≤ b → ∀ i, -(L : ℝ) * (b i - a i) ≤
      N.massActionVectorField κ b i - N.massActionVectorField κ a i := by
    intro a ha b hb hab i
    have h1 := coop_diag_bound N κ hcoop hM (fun k => hδ.le.trans (ha.1 k)) hab (fun k => hb.2 k) i
    have hgap : 0 ≤ b i - a i := by linarith [hab i]
    nlinarith
  have hc : 0 < kLow N κ * δ ^ srcDeg N := mul_pos (kLow_pos N κ) (pow_pos hδ _)
  have hG : ∀ i j, N.InfluenceEdge i j → ∀ a ∈ K, ∀ b ∈ K, a ≤ b →
      -(L : ℝ) * (b i - a i) + kLow N κ * δ ^ srcDeg N * (b j - a j) ≤
        N.massActionVectorField κ b i - N.massActionVectorField κ a i := by
    intro i j hedge a ha b hb hab
    have h1 := coop_edge_bound N κ hcoop hδ hδ1 hM ha.1 hab (fun k => hb.2 k) hedge
    have hgap : 0 ≤ b i - a i := by linarith [hab i]
    nlinarith
  exact strong_order_preserving hlip hsup hdiag hx hy hxK hyK h0 (N.InfluenceEdge) hE hc hG hne

end Network
end CRNT

namespace CRNT
namespace Examples
namespace StrongMonotoneIsomer

open Network

/-- `X ⇌ Y`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![1, 0], ![0, 1]⟩ else ⟨![0, 1], ![1, 0]⟩⟩

theorem cooperative : net.IsCooperativeNetwork := by
  intro r i hneg j hj
  fin_cases r <;> fin_cases i <;> fin_cases j <;> simp_all [reactionVector_apply] <;> norm_num at hneg

theorem edge_10 : net.InfluenceEdge 1 0 := ⟨0, by simp [reactionVector_apply], by simp⟩

theorem edge_01 : net.InfluenceEdge 0 1 := ⟨1, by simp [reactionVector_apply], by simp⟩

theorem strongly_connected :
    ∀ i j : Fin 2, Relation.ReflTransGen (fun j i => net.InfluenceEdge i j) j i := by
  intro i j
  fin_cases i <;> fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single edge_01
  · exact Relation.ReflTransGen.single edge_10
  · exact Relation.ReflTransGen.refl

/-- **`X ⇌ Y` is strongly monotone**: for every choice of rates, two solutions in a positive box
with `x(0) ≤ y(0)`, `x(0) ≠ y(0)` are strictly ordered at every positive time. -/
theorem strong_order (κ : net.RateConstants) {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 1 ≤ M)
    {T : ℝ} {x y : ℝ → Concentration (Fin 2)}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (net.massActionVectorField κ (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (net.massActionVectorField κ (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ Set.Icc (fun _ => δ) (fun _ => M))
    (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ Set.Icc (fun _ => δ) (fun _ => M))
    (h0 : x 0 ≤ y 0) (hne : x 0 ≠ y 0) : ∀ t ∈ Set.Ioc 0 T, ∀ i, x t i < y t i :=
  net.massAction_strong_order_preserving κ cooperative strongly_connected hδ hδ1 hM hx hy hxK hyK
    h0 hne

end StrongMonotoneIsomer
end Examples
end CRNT
