import CRNT.Stochastic.ProductFormInvariance
import CRNT.Stochastic.MinimalSemigroupErgodic
import CRNT.Graph.WeakReversibility

/-!
# Convergence to the product form on irreducible classes of weakly reversible networks

* Positive-rate reachability supports the transition function: `P(t)(a, b) = 0` unless `b` is
  reachable from `a` through positive-rate jumps (`Pmin_eq_zero_of_not_reachPos`).
* For a weakly reversible network, positive-rate reachability of counts is symmetric
  (`Network.reachPos_symm`): a jump through `y → y'` from `b + y` is undone by lifting a reaction
  path `y' ⇝ y` by the base `b` (`Network.reachPos_add_of_reaches`).
* Hence for a weakly reversible network with a positive complex-balanced equilibrium `c`, on every
  finite closed irreducible class `K` of counts, `P(t)(a, b)` converges, for `a, b ∈ K`, to the
  normalized product form `π_c(b) / ∑_{x ∈ K} π_c(x)` (`tendsto_transition_productPoisson`): the
  normalized restriction is invariant on `K` (`tsum_productPoisson_mul_transition` and the
  support lemma) and the invariant probability on `K` is unique (`exists_ergodic_limit`).
* For a conservative weakly reversible network the counts reachable from `n` form a finite
  (`finite_reachPos_of_conservative`), closed, irreducible class `reachClass n`, so for every
  initial count `n`, `P(t)(n, m)` converges to `π_c(m) / ∑_{x ∈ reachClass n} π_c(x)` for `m`
  reachable from `n`, and is `0` otherwise
  (`tendsto_transition_productPoisson_of_conservative`, `transition_eq_zero_of_not_reachPos`).
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

theorem P_eq_zero_of_not_reachPos (k : ℕ) :
    ∀ t a b, ¬ J.ReachPos a b → J.P k t a b = 0 := by
  induction k with
  | zero =>
      intro t a b h
      have : a ≠ b := fun hab => h (hab ▸ Relation.ReflTransGen.refl)
      simp [P_zero, this]
  | succ k ih =>
      intro t a b h
      have hab : a ≠ b := fun hab => h (hab ▸ Relation.ReflTransGen.refl)
      rw [P_succ]
      have h0 : ∀ s, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.P k (t - s) (J.next i a) b
          = 0 := by
        intro s
        rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
        rcases (J.rate_nonneg i a).lt_or_eq with hr | hr
        · rw [ih _ _ _ fun h' => h (Relation.ReflTransGen.head ⟨i, hr, rfl⟩ h'), mul_zero]
        · rw [← hr, zero_mul]
      simp [h0, hab]

theorem Pmin_eq_zero_of_not_reachPos (t : ℝ) {a b : α} (h : ¬ J.ReachPos a b) :
    J.Pmin t a b = 0 := by
  simp [Pmin, J.P_eq_zero_of_not_reachPos _ t a b h]

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Lifting a reaction path by a base count gives positive-rate reachability. -/
theorem reachPos_add_of_reaches (N : Network S) (κ : RateConstants N) (b : S → ℕ)
    {c d : Complex S} (h : N.Reaches c d) : (N.jumpSystem κ).ReachPos (b + c) (b + d) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail e d _ hed ih =>
      obtain ⟨r, hsrc, htgt⟩ := hed
      refine ih.tail ⟨r, ?_, ?_⟩
      · show 0 < N.stochasticMassActionRate κ (b + e) r
        unfold stochasticMassActionRate
        refine mul_pos (κ.positive r) (Finset.prod_pos fun s _ => ?_)
        rw [hsrc]
        exact_mod_cast Nat.descFactorial_pos.mpr (by simp)
      · show b + d = N.jumpNextCount (b + e) r
        funext s
        simp only [jumpNextCount, Pi.add_apply, hsrc, htgt]
        omega

/-- **Reversibility of jumps** in a weakly reversible network. -/
theorem reachPos_symm (N : Network S) (κ : RateConstants N) (hWR : N.WeaklyReversible)
    {n m : S → ℕ} (h : (N.jumpSystem κ).ReachPos n m) : (N.jumpSystem κ).ReachPos m n := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih =>
      obtain ⟨r, hr, rfl⟩ := hcd
      have hen : N.Enabled c r := by
        by_contra hdis
        have := N.stochasticMassActionRate_eq_zero_of_not_enabled κ c r hdis
        exact (ne_of_gt hr) this
      have hb := N.reachPos_add_of_reaches κ (fun s => c s - (N.reaction r).source s) (hWR r)
      have e1 : ((fun s => c s - (N.reaction r).source s) + (N.reaction r).target) =
          N.jumpNextCount c r := by
        funext s; simp only [Pi.add_apply, jumpNextCount]
      have e2 : ((fun s => c s - (N.reaction r).source s) + (N.reaction r).source) = c := by
        funext s; simp only [Pi.add_apply]; have := hen s; omega
      rw [e1, e2] at hb
      exact hb.trans ih

omit [DecidableEq S] in
theorem productPoissonPMF_pos {c : Concentration S} (hc : c.Positive) (n : S → ℕ) :
    0 < productPoissonPMF c n :=
  Finset.prod_pos fun s _ => by
    have := hc s
    positivity

/-- **Convergence to the product form.** For a weakly reversible network with a positive
complex-balanced equilibrium `c`, on a finite closed irreducible class `K` of counts the
transition probabilities converge to the normalized product form. -/
theorem tendsto_transition_productPoisson (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) {c : Concentration S} (hc : c.Positive)
    (hcb : N.IsComplexBalanced κ c) {K : Finset (S → ℕ)} (hK : (N.jumpSystem κ).ClosedOn K)
    (hne : K.Nonempty) (hirr : ∀ a ∈ K, ∀ b ∈ K, (N.jumpSystem κ).ReachPos a b) :
    ∀ a ∈ K, ∀ b ∈ K, Tendsto (fun t => N.transition κ t a b) atTop
      (𝓝 (productPoissonPMF c b / ∑ x ∈ K, productPoissonPMF c x)) := by
  obtain ⟨π, hlim, -, -, huniq⟩ := (N.jumpSystem κ).exists_ergodic_limit hK hne hirr
  have hZ : 0 < ∑ x ∈ K, productPoissonPMF c x :=
    Finset.sum_pos (fun x _ => productPoissonPMF_pos hc x) hne
  have hc0 : c.Nonnegative := fun s => (hc s).le
  -- the product form restricted to `K` is invariant on `K`
  have hinvK : ∀ t, 0 ≤ t → ∀ b ∈ K,
      ∑ a ∈ K, productPoissonPMF c a * N.transition κ t a b = productPoissonPMF c b := by
    intro t ht b hb
    rw [← N.tsum_productPoisson_mul_transition κ hc0 hcb ht b]
    refine (tsum_eq_sum fun n hn => ?_).symm
    have : N.transition κ t n b = 0 := by
      refine (N.jumpSystem κ).Pmin_eq_zero_of_not_reachPos t fun h => hn ?_
      exact JumpSystem.mem_of_reachPos hK hb (N.reachPos_symm κ hWR h)
    rw [this, mul_zero]
  have hμ := huniq (fun x => productPoissonPMF c x / ∑ y ∈ K, productPoissonPMF c y)
    (by rw [← Finset.sum_div, div_self hZ.ne'])
    (fun t ht b hb => by
      simp only [div_mul_eq_mul_div, ← Finset.sum_div]
      rw [show (∑ i ∈ K, productPoissonPMF c i * (N.jumpSystem κ).Pmin t i b) =
        productPoissonPMF c b from hinvK t ht b hb])
  intro a ha b hb
  have := hlim a ha b hb
  rwa [← hμ b hb] at this


/-- In a conservative network only finitely many counts are reachable from a given count. -/
theorem finite_reachPos_of_conservative (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) (n₀ : S → ℕ) : {c | (N.jumpSystem κ).ReachPos n₀ c}.Finite := by
  obtain ⟨w, hwinv, hwpos⟩ := hcons
  set W := ∑ s, w s * (n₀ s : ℝ)
  have hW : ∀ c, (N.jumpSystem κ).ReachPos n₀ c → ∑ s, w s * (c s : ℝ) = W := by
    intro c hc
    induction hc with
    | refl => rfl
    | @tail x y _ hxy ih =>
        obtain ⟨r, hr, rfl⟩ := hxy
        exact (N.weight_jumpNextCount κ hwinv hr).trans ih
  obtain ⟨K, hK⟩ : ∃ K : ℕ, ∀ c : S → ℕ, ∑ s, w s * (c s : ℝ) = W → ∀ s, c s ≤ K := by
    refine ⟨⌈∑ s, W / w s⌉₊, fun c hc s => ?_⟩
    have h1 : w s * (c s : ℝ) ≤ W := by
      rw [← hc]
      exact Finset.single_le_sum (f := fun s => w s * (c s : ℝ))
        (fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)) (Finset.mem_univ s)
    have h2 : (c s : ℝ) ≤ W / w s := by rw [le_div_iff₀ (hwpos s)]; linarith
    have hW0 : 0 ≤ W := Finset.sum_nonneg fun s _ => mul_nonneg (hwpos s).le (Nat.cast_nonneg _)
    have h3 : W / w s ≤ ∑ s, W / w s :=
      Finset.single_le_sum (f := fun s => W / w s) (fun s _ => div_nonneg hW0 (hwpos s).le)
        (Finset.mem_univ s)
    exact_mod_cast (h2.trans h3).trans (Nat.le_ceil _)
  refine (Fintype.piFinset fun _ : S => Finset.range (K + 1)).finite_toSet.subset fun c hc => ?_
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  exact fun s => Finset.mem_range.mpr (Nat.lt_succ_of_le (hK c (hW c hc) s))

/-- The (finite) class of counts reachable from `n` in a conservative network. -/
noncomputable def reachClass (N : Network S) (κ : RateConstants N) (hcons : N.IsConservative)
    (n : S → ℕ) : Finset (S → ℕ) :=
  (N.finite_reachPos_of_conservative κ hcons n).toFinset

theorem mem_reachClass (N : Network S) (κ : RateConstants N) (hcons : N.IsConservative)
    {n m : S → ℕ} : m ∈ N.reachClass κ hcons n ↔ (N.jumpSystem κ).ReachPos n m := by
  simp [reachClass]

theorem transition_eq_zero_of_not_reachPos (N : Network S) (κ : RateConstants N) (t : ℝ)
    {n m : S → ℕ} (h : ¬ (N.jumpSystem κ).ReachPos n m) : N.transition κ t n m = 0 :=
  (N.jumpSystem κ).Pmin_eq_zero_of_not_reachPos t h

/-- **Convergence to the product form from every initial count.** For a conservative weakly
reversible network with a positive complex-balanced equilibrium `c`, for every initial count `n`
and every count `m` reachable from `n`, `P(t)(n, m) → π_c(m) / ∑_{x ∈ reachClass n} π_c(x)`. -/
theorem tendsto_transition_productPoisson_of_conservative (N : Network S) (κ : RateConstants N)
    (hWR : N.WeaklyReversible) (hcons : N.IsConservative) {c : Concentration S}
    (hc : c.Positive) (hcb : N.IsComplexBalanced κ c) {n m : S → ℕ}
    (hm : (N.jumpSystem κ).ReachPos n m) :
    Tendsto (fun t => N.transition κ t n m) atTop
      (𝓝 (productPoissonPMF c m / ∑ x ∈ N.reachClass κ hcons n, productPoissonPMF c x)) := by
  have hmem := fun x => N.mem_reachClass κ hcons (n := n) (m := x)
  refine N.tendsto_transition_productPoisson κ hWR hc hcb ?_ ⟨n, (hmem n).mpr
    Relation.ReflTransGen.refl⟩ ?_ n ((hmem n).mpr Relation.ReflTransGen.refl) m ((hmem m).mpr hm)
  · intro a ha i hr
    exact (hmem _).mpr (((hmem a).mp ha).tail ⟨i, hr, rfl⟩)
  · intro a ha b hb
    exact (N.reachPos_symm κ hWR ((hmem a).mp ha)).trans ((hmem b).mp hb)

end Network

end CRNT
