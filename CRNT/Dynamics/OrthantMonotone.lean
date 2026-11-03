import CRNT.Dynamics.MonotoneComparison
import CRNT.Dynamics.CooperativeNetworks
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Monotonicity with respect to an orthant order

A sign vector `σ ∈ {±1}^S` defines the orthant order `x ≤_σ y` iff `σ_i x_i ≤ σ_i y_i` for all `i`
(Smith, *Monotone Dynamical Systems*, 1995, ch. 3; Angeli–Sontag 2008 for reaction networks). The
Kamke condition for this order is `σ_i f_i(a) ≤ σ_i f_i(b)` whenever `a ≤_σ b` and `a_i = b_i`;
for `C¹` fields it is `σ_i σ_j ∂_j f_i ≥ 0` for `i ≠ j`. The change of variables `z = σ ∘ x`
turns it into the cooperative (standard-order) Kamke condition, so the comparison principle
`Monotone.kamke_comparison` transfers.

* `OrthantLE`, `KamkeOnSign`.
* `orthant_comparison`: solutions starting `≤_σ`-ordered stay ordered.
-/

namespace CRNT

namespace Monotone

open scoped NNReal

variable {S : Type} [Fintype S]

/-- The orthant order defined by a sign vector `σ`. -/
def OrthantLE (σ : S → ℝ) (x y : S → ℝ) : Prop := ∀ i, σ i * x i ≤ σ i * y i

/-- The Kamke condition for the orthant order on `K`. -/
def KamkeOnSign (σ : S → ℝ) (f : (S → ℝ) → (S → ℝ)) (K : Set (S → ℝ)) : Prop :=
  ∀ a ∈ K, ∀ b ∈ K, OrthantLE σ a b → ∀ i, a i = b i → σ i * f a i ≤ σ i * f b i

/-- **Orthant comparison principle.** Let `σ ∈ {±1}^S`, let `f` be Lipschitz on `K` with the Kamke
condition for `≤_σ`, and let the reflected set `{σ ∘ x : x ∈ K}` be closed under componentwise
maximum. If `x, y` solve `ẋ = f(x)` on `[0, T]` inside `K` with `x 0 ≤_σ y 0`, then
`x t ≤_σ y t` on `[0, T]`. -/
theorem orthant_comparison {σ : S → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1)
    {f : (S → ℝ) → (S → ℝ)} {K : Set (S → ℝ)} {L : ℝ≥0}
    (hlip : LipschitzOnWith L f K)
    (hsup : ∀ a ∈ K, ∀ b ∈ K, σ * ((σ * a) ⊔ (σ * b)) ∈ K)
    (hk : KamkeOnSign σ f K) {T : ℝ} {x y : ℝ → (S → ℝ)}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (f (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (f (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ K) (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ K)
    (h0 : OrthantLE σ (x 0) (y 0)) : ∀ t ∈ Set.Icc 0 T, OrthantLE σ (x t) (y t) := by
  have hσσ : σ * σ = 1 := by
    funext i; rcases hσ i with h | h <;> simp [h]
  have hσabs : ∀ i, |σ i| = 1 := fun i => by rcases hσ i with h | h <;> simp [h]
  -- the reflected field and set
  set g : (S → ℝ) → (S → ℝ) := fun z => σ * f (σ * z) with hg
  set K' : Set (S → ℝ) := {z | σ * z ∈ K} with hK'
  have hrefl : ∀ z : S → ℝ, σ * (σ * z) = z := fun z => by rw [← mul_assoc, hσσ, one_mul]
  have hnorm : ∀ v : S → ℝ, ‖σ * v‖ = ‖v‖ := by
    intro v
    simp only [Pi.norm_def, Pi.mul_apply]
    congr 1
    refine Finset.sup_congr rfl fun b _ => ?_
    have h1 : ‖σ b‖₊ = 1 := by
      rw [← NNReal.coe_eq_one, coe_nnnorm, Real.norm_eq_abs, hσabs]
    rw [nnnorm_mul, h1, one_mul]
  have hlip' : LipschitzOnWith L g K' := by
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    have h := hlip.dist_le_mul (σ * a) ha (σ * b) hb
    rw [dist_eq_norm, dist_eq_norm] at h ⊢
    calc ‖g a - g b‖ = ‖σ * (f (σ * a) - f (σ * b))‖ := by simp [hg, mul_sub]
      _ = ‖f (σ * a) - f (σ * b)‖ := hnorm _
      _ ≤ L * ‖σ * a - σ * b‖ := h
      _ = L * ‖a - b‖ := by rw [← mul_sub, hnorm]
  have hsup' : ∀ a ∈ K', ∀ b ∈ K', a ⊔ b ∈ K' := by
    intro a ha b hb
    have := hsup _ ha _ hb
    simpa [hK', hrefl] using this
  have hk' : KamkeOn g K' := by
    intro a ha b hb hab i hi
    have hle : OrthantLE σ (σ * a) (σ * b) := fun j => by
      have := hab j
      simp only [Pi.mul_apply]
      rw [← mul_assoc, ← mul_assoc, show σ j * σ j = 1 from congrFun hσσ j, one_mul, one_mul]
      exact this
    have := hk _ ha _ hb hle i (by simp [Pi.mul_apply, hi])
    simpa [hg, Pi.mul_apply] using this
  -- reflected solutions
  have hderiv : ∀ {u : ℝ → (S → ℝ)}, (∀ t ∈ Set.Icc 0 T, HasDerivWithinAt u (f (u t)) (Set.Icc 0 T) t) →
      ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt (fun t => σ * u t) (g (σ * u t)) (Set.Icc 0 T) t := by
    intro u hu t ht
    have h := hu t ht
    rw [hasDerivWithinAt_pi] at h ⊢
    intro i
    have := (h i).const_mul (σ i)
    simpa [hg, hrefl, Pi.mul_apply] using this
  have hmem : ∀ {u : ℝ → (S → ℝ)}, (∀ t ∈ Set.Icc 0 T, u t ∈ K) →
      ∀ t ∈ Set.Icc 0 T, σ * u t ∈ K' := fun hu t ht => by simpa [hK', hrefl] using hu t ht
  have h0' : σ * x 0 ≤ σ * y 0 := fun i => h0 i
  have := kamke_comparison hlip' hsup' hk' (hderiv hx) (hderiv hy) (hmem hxK) (hmem hyK) h0'
  intro t ht i
  exact this t ht i

end Monotone

end CRNT

namespace CRNT

namespace Network

open scoped BigOperators NNReal

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Structural orthant monotonicity.** For a sign vector `σ`, every reaction `r` changing a
species `i` has all its other reactant species `j` on the side `σ_i σ_j (y'_r − y_r)_i ≥ 0`. For
`σ ≡ 1` this is the cooperative condition (`IsCooperativeNetwork`). -/
def IsOrthantCooperative (N : Network S) (σ : S → ℝ) : Prop :=
  ∀ r i j, j ≠ i → (N.reaction r).source j ≠ 0 → 0 ≤ σ i * σ j * N.reactionVector r i

omit [DecidableEq S] in
theorem massActionMonomial_mono_on_support {y : Complex S} {a b : Concentration S}
    (ha : a.Nonnegative) (hab : ∀ j, y j ≠ 0 → a j ≤ b j) :
    y.massActionMonomial a ≤ y.massActionMonomial b := by
  refine Finset.prod_le_prod₀ (fun s _ => pow_nonneg (ha s) _) (fun s _ => ?_)
  by_cases hs : y s = 0
  · rw [hs, pow_zero, pow_zero]
  · exact pow_le_pow_left₀ (ha s) (hab s hs) _

/-- **Orthant-cooperative networks satisfy the orthant Kamke condition** on the nonnegative
orthant. -/
theorem massAction_kamkeOnSign_of_orthantCooperative (N : Network S) (κ : N.RateConstants)
    {σ : S → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (hcoop : N.IsOrthantCooperative σ) :
    Monotone.KamkeOnSign σ (N.massActionVectorField κ) {x | Concentration.Nonnegative x} := by
  intro a ha b hb hab i hi
  rw [massActionVectorField_apply, massActionVectorField_apply, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  simp only [massActionRate]
  set s := σ i * N.reactionVector r i with hs
  have hσsq : ∀ j, σ j * σ j = 1 := fun j => by rcases hσ j with h | h <;> rw [h] <;> norm_num
  -- rewrite both sides as `κ s y^{…}`
  have hform : ∀ x : Concentration S, σ i * (κ.k r * (N.reaction r).source.massActionMonomial x *
      N.reactionVector r i) = κ.k r * s * (N.reaction r).source.massActionMonomial x := by
    intro x; simp only [hs]; ring
  rw [hform, hform]
  rcases lt_trichotomy s 0 with hneg | hzero | hpos
  · -- every other reactant species has `σ_j = −1`, so `b_j ≤ a_j`
    have hmono : (N.reaction r).source.massActionMonomial b ≤
        (N.reaction r).source.massActionMonomial a := by
      refine massActionMonomial_mono_on_support hb fun j hj => ?_
      by_cases hji : j = i
      · rw [hji, hi]
      · have h1 := hcoop r i j hji hj
        have h2 := hab j
        have hσj : σ j = -1 := by
          rcases hσ j with h | h
          · exfalso; rw [h, mul_one] at h1; simp only [hs] at hneg; linarith
          · exact h
        rw [hσj] at h2; linarith
    exact mul_le_mul_of_nonpos_left hmono (mul_nonpos_of_nonneg_of_nonpos (κ.positive r).le hneg.le)
  · rw [hzero, mul_zero, zero_mul, zero_mul]
  · have hmono : (N.reaction r).source.massActionMonomial a ≤
        (N.reaction r).source.massActionMonomial b := by
      refine massActionMonomial_mono_on_support ha fun j hj => ?_
      by_cases hji : j = i
      · rw [hji, hi]
      · have h1 := hcoop r i j hji hj
        have h2 := hab j
        have hσj : σ j = 1 := by
          rcases hσ j with h | h
          · exact h
          · exfalso; rw [h] at h1; simp only [hs] at hpos; linarith
        rw [hσj] at h2; linarith
    exact mul_le_mul_of_nonneg_left hmono (mul_nonneg (κ.positive r).le hpos.le)

/-- **Orthant order preservation for orthant-cooperative mass-action networks.** Two solutions on
`[0, T]` in a box `[0, M]^S` that start `≤_σ`-ordered stay ordered. -/
theorem massAction_orthant_preserving (N : Network S) (κ : N.RateConstants)
    {σ : S → ℝ} (hσ : ∀ i, σ i = 1 ∨ σ i = -1) (hcoop : N.IsOrthantCooperative σ) (M : ℝ)
    {T : ℝ} {x y : ℝ → Concentration S}
    (hx : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt x (N.massActionVectorField κ (x t)) (Set.Icc 0 T) t)
    (hy : ∀ t ∈ Set.Icc 0 T, HasDerivWithinAt y (N.massActionVectorField κ (y t)) (Set.Icc 0 T) t)
    (hxK : ∀ t ∈ Set.Icc 0 T, x t ∈ Set.Icc (0 : S → ℝ) (fun _ => M))
    (hyK : ∀ t ∈ Set.Icc 0 T, y t ∈ Set.Icc (0 : S → ℝ) (fun _ => M))
    (h0 : Monotone.OrthantLE σ (x 0) (y 0)) :
    ∀ t ∈ Set.Icc 0 T, Monotone.OrthantLE σ (x t) (y t) := by
  set K := Set.Icc (0 : S → ℝ) (fun _ => M)
  obtain ⟨L, hL⟩ := ((N.contDiff_massActionVectorField κ).contDiffOn (s := K)).exists_lipschitzOnWith
    (by simp) (convex_Icc _ _) isCompact_Icc
  have hσσ : ∀ j, σ j * σ j = 1 := fun j => by rcases hσ j with h | h <;> rw [h] <;> norm_num
  have hsup : ∀ a ∈ K, ∀ b ∈ K, σ * ((σ * a) ⊔ (σ * b)) ∈ K := by
    intro a ha b hb
    constructor
    · intro j
      simp only [Pi.mul_apply, Pi.sup_apply, Pi.zero_apply]
      rcases hσ j with h | h <;> rw [h]
      · simp only [one_mul]; exact le_sup_of_le_left (ha.1 j)
      · have : ((-1) * a j) ⊔ ((-1) * b j) = -(a j ⊓ b j) := by
          rw [neg_inf]; ring_nf
        rw [this]; simp only [neg_mul, one_mul, neg_neg]; exact le_inf (ha.1 j) (hb.1 j)
    · intro j
      simp only [Pi.mul_apply, Pi.sup_apply]
      rcases hσ j with h | h <;> rw [h]
      · simp only [one_mul]; exact sup_le (ha.2 j) (hb.2 j)
      · have : ((-1) * a j) ⊔ ((-1) * b j) = -(a j ⊓ b j) := by
          rw [neg_inf]; ring_nf
        rw [this]; simp only [neg_mul, one_mul, neg_neg]; exact inf_le_left.trans (ha.2 j)
  have hk : Monotone.KamkeOnSign σ (N.massActionVectorField κ) K := by
    intro a ha b hb hab i hi
    exact N.massAction_kamkeOnSign_of_orthantCooperative κ hσ hcoop a (fun s => ha.1 s) b
      (fun s => hb.1 s) hab i hi
  exact Monotone.orthant_comparison hσ hL hsup hk hx hy hxK hyK h0

/-- Cooperative networks are orthant-cooperative for `σ ≡ 1`. -/
theorem isOrthantCooperative_one_of_cooperative (N : Network S) (h : N.IsCooperativeNetwork) :
    N.IsOrthantCooperative (fun _ => 1) := by
  intro r i j hji hj
  simp only [one_mul]
  by_contra hneg
  push Not at hneg
  exact hj (h r i hneg j hji)

end Network

end CRNT
