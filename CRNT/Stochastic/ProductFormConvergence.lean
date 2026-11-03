import CRNT.Stochastic.MinimalSemigroupErgodicInfinite
import CRNT.Stochastic.ComplexBalancedNonExplosion

/-!
# Convergence to the product form for weakly reversible complex-balanced networks

For a weakly reversible network with a positive complex-balanced equilibrium `c` and any initial
count `n`, the law of the stochastic mass-action chain converges in total variation to the
product form `π_c` restricted to the counts reachable from `n` and normalized
(`tendsto_l1_transition_productPoisson`). No conservation law is assumed: the class may be
infinite. Ingredients: non-explosion (`hasSum_transition_one_of_complexBalanced`), invariance of the
product form (`tsum_productPoisson_mul_transition`), symmetry of reachability (`reachPos_symm`),
and the ℓ¹ ergodic theorem `JumpSystem.tendsto_l1_of_invariant`.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The product form restricted to the counts reachable from `n`. -/
noncomputable def classProductForm (N : Network S) (κ : RateConstants N) (c : Concentration S)
    (n : S → ℕ) : (S → ℕ) → ℝ :=
  Set.indicator {m | (N.jumpSystem κ).ReachPos n m} (productPoissonPMF c)

/-- The normalized product form on the class reachable from `n`: positivity of the
normalization, total mass one, support, and invariance. -/
theorem classProductForm_facts (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) {c : Concentration S} (hc : c.Positive)
    (hcb : N.IsComplexBalanced κ c) (n : S → ℕ) :
    0 < ∑' x, N.classProductForm κ c n x ∧
    (∀ m, 0 ≤ N.classProductForm κ c n m / ∑' x, N.classProductForm κ c n x) ∧
    (∀ m, ¬ (N.jumpSystem κ).ReachPos n m →
      N.classProductForm κ c n m / ∑' x, N.classProductForm κ c n x = 0) ∧
    HasSum (fun m => N.classProductForm κ c n m / ∑' x, N.classProductForm κ c n x) 1 ∧
    ∀ t, 0 ≤ t → ∀ b, ∑' x, N.classProductForm κ c n x / (∑' y, N.classProductForm κ c n y) *
      N.transition κ t x b = N.classProductForm κ c n b / ∑' y, N.classProductForm κ c n y := by
  classical
  set E : Set (S → ℕ) := {m | (N.jumpSystem κ).ReachPos n m} with hE
  set w := N.classProductForm κ c n with hwdef
  have hc0 : c.Nonnegative := fun s => (hc s).le
  have hwE : ∀ m, (N.jumpSystem κ).ReachPos n m → w m = productPoissonPMF c m := fun m h =>
    Set.indicator_of_mem (s := E) h _
  have hwN : ∀ m, ¬ (N.jumpSystem κ).ReachPos n m → w m = 0 := fun m h =>
    Set.indicator_of_notMem (s := E) h _
  have hw0 : ∀ m, 0 ≤ w m := fun m => by
    by_cases h : (N.jumpSystem κ).ReachPos n m
    · rw [hwE m h]; exact productPoissonPMF_nonneg hc0 m
    · rw [hwN m h]
  have hπs : Summable (productPoissonPMF c) := summable_of_sum_le (c := 1)
    (fun m => productPoissonPMF_nonneg hc0 m) (sum_productPoissonPMF_le_one hc0)
  have hws : Summable w := Summable.of_nonneg_of_le hw0 (fun m => by
    by_cases h : (N.jumpSystem κ).ReachPos n m
    · rw [hwE m h]
    · rw [hwN m h]; exact productPoissonPMF_nonneg hc0 m) hπs
  have hwn : w n = productPoissonPMF c n := hwE n Relation.ReflTransGen.refl
  set Z := ∑' x, w x with hZdef
  have hZ : 0 < Z := lt_of_lt_of_le (hwn ▸ productPoissonPMF_pos hc n)
    (hws.le_tsum n fun _ _ => hw0 _)
  have hin : ∀ t x b, b ∈ E → x ∉ E → N.transition κ t x b = 0 := by
    intro t x b hb hx
    refine N.transition_eq_zero_of_not_reachPos κ t fun h => hx ?_
    exact (hb : (N.jumpSystem κ).ReachPos n b).trans (N.reachPos_symm κ hWR h)
  have hout : ∀ t x b, x ∈ E → b ∉ E → N.transition κ t x b = 0 := by
    intro t x b hx hb
    exact N.transition_eq_zero_of_not_reachPos κ t fun h =>
      hb ((hx : (N.jumpSystem κ).ReachPos n x).trans h)
  refine ⟨hZ, fun m => div_nonneg (hw0 m) hZ.le, fun m hm => by rw [hwN m hm, zero_div],
    by have h := hws.hasSum.div_const Z; rwa [div_self hZ.ne'] at h, ?_⟩
  intro t ht b
  have hinvπ := N.tsum_productPoisson_mul_transition κ hc0 hcb ht b
  have hkey : ∑' x, w x * N.transition κ t x b = w b := by
    by_cases hb : (N.jumpSystem κ).ReachPos n b
    · rw [hwE b hb, ← hinvπ]
      refine tsum_congr fun x => ?_
      by_cases hx : (N.jumpSystem κ).ReachPos n x
      · rw [hwE x hx]
      · rw [hwN x hx, hin t x b hb hx, zero_mul, mul_zero]
    · rw [hwN b hb]
      refine (tsum_congr fun x => ?_).trans tsum_zero
      by_cases hx : (N.jumpSystem κ).ReachPos n x
      · rw [hout t x b hx hb, mul_zero]
      · rw [hwN x hx, zero_mul]
  show ∑' x, w x / Z * N.transition κ t x b = w b / Z
  rw [← hkey, ← tsum_div_const]
  exact tsum_congr fun x => by ring

/-- **Convergence to the product form in total variation.** -/
theorem tendsto_l1_transition_productPoisson (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) {c : Concentration S} (hc : c.Positive)
    (hcb : N.IsComplexBalanced κ c) (n : S → ℕ) :
    Tendsto (fun t => ∑' m, |N.transition κ t n m -
        N.classProductForm κ c n m / ∑' x, N.classProductForm κ c n x|) atTop (𝓝 0) := by
  obtain ⟨hZ, h0, hsupp, h1, hinv⟩ := N.classProductForm_facts κ hWR hc hcb n
  have hwn : N.classProductForm κ c n n = productPoissonPMF c n :=
    Set.indicator_of_mem (s := {m | (N.jumpSystem κ).ReachPos n m}) Relation.ReflTransGen.refl _
  exact (N.jumpSystem κ).tendsto_l1_of_invariant (E := {m | (N.jumpSystem κ).ReachPos n m})
    (fun a ha i hr => (ha : (N.jumpSystem κ).ReachPos n a).tail ⟨i, hr, rfl⟩)
    (fun a ha b hb => (N.reachPos_symm κ hWR ha).trans hb)
    (fun t ht a _ => N.hasSum_transition_one_of_complexBalanced κ hc hcb ht a)
    h0 hsupp h1 hinv Relation.ReflTransGen.refl
    (by rw [hwn]; exact div_pos (productPoissonPMF_pos hc n) hZ)

/-- **Uniqueness of the stationary distribution on an irreducible class.** Every invariant
probability supported on the counts reachable from `n` is the normalized product form. -/
theorem stationary_eq_classProductForm (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) {c : Concentration S} (hc : c.Positive)
    (hcb : N.IsComplexBalanced κ c) (n : S → ℕ) {μ : (S → ℕ) → ℝ} (hμ0 : ∀ m, 0 ≤ μ m)
    (hμE : ∀ m, ¬ (N.jumpSystem κ).ReachPos n m → μ m = 0) (hμ1 : HasSum μ 1)
    (hμinv : ∀ t, 0 ≤ t → ∀ m, ∑' x, μ x * N.transition κ t x m = μ m) (m : S → ℕ) :
    μ m = N.classProductForm κ c n m / ∑' x, N.classProductForm κ c n x := by
  obtain ⟨-, h0, hsupp, h1, hinv⟩ := N.classProductForm_facts κ hWR hc hcb n
  exact (N.jumpSystem κ).invariant_unique (E := {m | (N.jumpSystem κ).ReachPos n m})
    (fun a ha i hr => (ha : (N.jumpSystem κ).ReachPos n a).tail ⟨i, hr, rfl⟩)
    (fun a ha b hb => (N.reachPos_symm κ hWR ha).trans hb)
    (fun t ht a _ => N.hasSum_transition_one_of_complexBalanced κ hc hcb ht a)
    h0 hsupp h1 hinv hμ0 hμE hμ1 hμinv m

/-- **Pointwise convergence to the product form.** -/
theorem tendsto_transition_classProductForm (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) {c : Concentration S} (hc : c.Positive)
    (hcb : N.IsComplexBalanced κ c) (n m : S → ℕ) :
    Tendsto (fun t => N.transition κ t n m) atTop
      (𝓝 (N.classProductForm κ c n m / ∑' x, N.classProductForm κ c n x)) := by
  set π := fun x => N.classProductForm κ c n x / ∑' y, N.classProductForm κ c n y with hπ
  have hl1 := N.tendsto_l1_transition_productPoisson κ hWR hc hcb n
  have hc0 : c.Nonnegative := fun s => (hc s).le
  have hπ0 : ∀ x, 0 ≤ π x := fun x => div_nonneg (Set.indicator_nonneg
    (fun y _ => productPoissonPMF_nonneg hc0 y) x) (tsum_nonneg fun y => Set.indicator_nonneg
      (fun y _ => productPoissonPMF_nonneg hc0 y) y)
  have hπs : Summable π := by
    refine (Summable.of_nonneg_of_le (fun x => Set.indicator_nonneg
      (fun y _ => productPoissonPMF_nonneg hc0 y) x) (fun x => Set.indicator_le_self' (fun y _ => productPoissonPMF_nonneg hc0 y) x)
      (summable_of_sum_le (c := 1) (fun m => productPoissonPMF_nonneg hc0 m)
        (sum_productPoissonPMF_le_one hc0))).div_const _
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hl1
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hrow := N.hasSum_transition_one_of_complexBalanced κ hc hcb ht n
  have hs : Summable fun x => |N.transition κ t n x - π x| :=
    Summable.of_nonneg_of_le (fun x => abs_nonneg _) (fun x => (abs_sub _ _).trans (by
      rw [abs_of_nonneg (N.transition_nonneg κ ht n x), abs_of_nonneg (hπ0 x)]))
      (hrow.summable.add hπs)
  rw [Real.norm_eq_abs]
  exact hs.le_tsum m fun _ _ => abs_nonneg _

end Network
end CRNT
