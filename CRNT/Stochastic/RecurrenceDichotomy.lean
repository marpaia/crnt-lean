import CRNT.Stochastic.ProductFormErgodic

/-!
# Positive recurrence and transience of counts in conservative networks

For stochastic mass action on a conservative network (finitely many counts reachable from each
count):

* if every count reachable from `b` reaches `b` back (`b` is recurrent in the jump graph), then
  `P(t)(b, b)` converges to a positive limit (`tendsto_transition_self_pos_of_recurrent`), the
  continuous-time criterion for positive recurrence;
* otherwise `P(t)(b, b) → 0` (`tendsto_transition_self_zero_of_not_recurrent`): `b` is transient.
-/

open Filter
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Recurrent counts are positive recurrent.** -/
theorem tendsto_transition_self_pos_of_recurrent (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) {b : S → ℕ}
    (hrec : ∀ m, (N.jumpSystem κ).ReachPos b m → (N.jumpSystem κ).ReachPos m b) :
    ∃ p : ℝ, 0 < p ∧ Tendsto (fun t => N.transition κ t b b) atTop (𝓝 p) := by
  set K := N.reachClass κ hcons b with hK
  have hmem := fun x => N.mem_reachClass κ hcons (n := b) (m := x)
  have hbK : b ∈ K := (hmem b).mpr Relation.ReflTransGen.refl
  have hclosed : (N.jumpSystem κ).ClosedOn K := fun a ha i hr =>
    (hmem _).mpr (((hmem a).mp ha).tail ⟨i, hr, rfl⟩)
  have hirr : ∀ a ∈ K, ∀ c ∈ K, (N.jumpSystem κ).ReachPos a c := fun a ha c hc =>
    (hrec a ((hmem a).mp ha)).trans ((hmem c).mp hc)
  obtain ⟨π, hlim, hsum, hinv, -⟩ := (N.jumpSystem κ).exists_ergodic_limit hclosed ⟨b, hbK⟩ hirr
  have hπ0 : ∀ a ∈ K, 0 ≤ π a := fun a ha =>
    ge_of_tendsto (hlim b hbK a ha) ((eventually_ge_atTop 0).mono fun t ht =>
      (N.jumpSystem κ).Pmin_nonneg t ht b a)
  obtain ⟨a, ha, hapos⟩ : ∃ a ∈ K, 0 < π a := by
    by_contra h
    push Not at h
    have : ∑ a ∈ K, π a ≤ 0 := Finset.sum_nonpos h
    linarith
  have hb := hinv 1 zero_le_one b hbK
  have hle : π a * (N.jumpSystem κ).Pmin 1 a b ≤ ∑ c ∈ K, π c * (N.jumpSystem κ).Pmin 1 c b :=
    Finset.single_le_sum (f := fun c => π c * (N.jumpSystem κ).Pmin 1 c b)
      (fun c hc => mul_nonneg (hπ0 c hc) ((N.jumpSystem κ).Pmin_nonneg 1 zero_le_one c b)) ha
  have hpos := mul_pos hapos ((N.jumpSystem κ).Pmin_pos_of_reachPos (hirr a ha b hbK) one_pos)
  exact ⟨π b, by linarith, hlim b hbK b hbK⟩

/-- **Non-recurrent counts are transient.** -/
theorem tendsto_transition_self_zero_of_not_recurrent (N : Network S) (κ : RateConstants N)
    (hcons : N.IsConservative) {b : S → ℕ}
    (hnrec : ∃ m, (N.jumpSystem κ).ReachPos b m ∧ ¬ (N.jumpSystem κ).ReachPos m b) :
    Tendsto (fun t => N.transition κ t b b) atTop (𝓝 0) := by
  classical
  obtain ⟨m, hbm, hmb⟩ := hnrec
  set J := N.jumpSystem κ with hJ
  set A := (N.reachClass κ hcons b).filter fun c => J.ReachPos c b with hA
  have hmemA : ∀ c, c ∈ A ↔ J.ReachPos b c ∧ J.ReachPos c b := fun c => by
    rw [hA, Finset.mem_filter, N.mem_reachClass]
  have hbA : b ∈ A := (hmemA b).mpr ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  have hmA : m ∉ A := fun h => hmb ((hmemA m).mp h).2
  -- Chapman–Kolmogorov restricted to `A`
  have hsplit : ∀ c ∈ A, ∀ d ∈ A, ∀ {s t : ℝ}, 0 ≤ s → 0 ≤ t →
      J.Pmin (s + t) c d = ∑ x ∈ A, J.Pmin s c x * J.Pmin t x d := by
    intro c hc d hd s t hs ht
    rw [J.Pmin_add hs ht c d]
    refine tsum_eq_sum fun x hx => ?_
    by_cases hcx : J.ReachPos c x
    · have hxd : ¬ J.ReachPos x d := fun h => hx ((hmemA x).mpr
        ⟨((hmemA c).mp hc).1.trans hcx, h.trans ((hmemA d).mp hd).2⟩)
      rw [J.Pmin_eq_zero_of_not_reachPos t hxd, mul_zero]
    · rw [J.Pmin_eq_zero_of_not_reachPos s hcx, zero_mul]
  -- the Doeblin constant toward `m`
  have hAne : A.Nonempty := ⟨b, hbA⟩
  set δ := A.inf' hAne fun c => J.Pmin 1 c m with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    intro c hc
    exact J.Pmin_pos_of_reachPos (((hmemA c).mp hc).2.trans hbm) one_pos
  have hδle : ∀ c ∈ A, δ ≤ J.Pmin 1 c m := fun c hc => Finset.inf'_le _ hc
  have hrow : ∀ c ∈ A, ∑ x ∈ A, J.Pmin 1 c x ≤ 1 - δ := by
    intro c hc
    have h := J.sum_Pmin_le_one 1 zero_le_one c (insert m A)
    rw [Finset.sum_insert hmA] at h
    linarith [hδle c hc]
  -- the mass remaining in `A`
  set G : ℕ → ℝ := fun n => A.sup' hAne fun c => ∑ x ∈ A, J.Pmin n c x with hG
  have hgle : ∀ (n : ℕ) c, c ∈ A → ∑ x ∈ A, J.Pmin n c x ≤ G n := fun n c hc =>
    Finset.le_sup' (fun c => ∑ x ∈ A, J.Pmin n c x) hc
  have hG0 : ∀ n : ℕ, 0 ≤ G n := fun n => (Finset.sum_nonneg fun x _ =>
    J.Pmin_nonneg _ (Nat.cast_nonneg n) b x).trans (hgle n b hbA)
  have hgeo : ∀ n : ℕ, G n ≤ (1 - δ) ^ n := by
    intro n
    induction n with
    | zero =>
        refine Finset.sup'_le _ _ fun c _ => ?_
        simpa using J.sum_Pmin_le_one 0 le_rfl c A
    | succ n ih =>
        refine Finset.sup'_le _ _ fun c hc => ?_
        have hn : ((n + 1 : ℕ) : ℝ) = 1 + n := by push_cast; ring
        calc ∑ x ∈ A, J.Pmin ((n + 1 : ℕ) : ℝ) c x
            = ∑ x ∈ A, ∑ y ∈ A, J.Pmin 1 c y * J.Pmin n y x := by
              refine Finset.sum_congr rfl fun x hx => ?_
              rw [hn]; exact hsplit c hc x hx zero_le_one (Nat.cast_nonneg n)
          _ = ∑ y ∈ A, J.Pmin 1 c y * ∑ x ∈ A, J.Pmin n y x := by
              rw [Finset.sum_comm]; simp only [Finset.mul_sum]
          _ ≤ ∑ y ∈ A, J.Pmin 1 c y * G n := Finset.sum_le_sum fun y hy =>
              mul_le_mul_of_nonneg_left (hgle n y hy) (J.Pmin_nonneg 1 zero_le_one c y)
          _ = (∑ y ∈ A, J.Pmin 1 c y) * G n := by rw [Finset.sum_mul]
          _ ≤ (1 - δ) * G n := mul_le_mul_of_nonneg_right (hrow c hc) (hG0 n)
          _ ≤ (1 - δ) * (1 - δ) ^ n := by
              have h1 : 0 ≤ 1 - δ := by
                have := hrow b hbA
                have := Finset.sum_nonneg fun x (_ : x ∈ A) => J.Pmin_nonneg 1 zero_le_one b x
                linarith
              exact mul_le_mul_of_nonneg_left ih h1
          _ = (1 - δ) ^ (n + 1) := by ring
  -- conclude
  have hδ1 : 1 - δ < 1 := by linarith
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hδ1
  refine ⟨n, fun t ht => ?_⟩
  have htn : (n : ℝ) ≤ t := ht
  have hP0 : 0 ≤ N.transition κ t b b := N.transition_nonneg κ (by linarith [Nat.cast_nonneg (α := ℝ) n]) b b
  have hbound : N.transition κ t b b ≤ G n := by
    have hsub : t = (t - n) + n := by ring
    have h1 : J.Pmin t b b = ∑ x ∈ A, J.Pmin (t - n) b x * J.Pmin n x b := by
      conv_lhs => rw [hsub]
      exact hsplit b hbA b hbA (by linarith) (Nat.cast_nonneg n)
    show J.Pmin t b b ≤ G n
    rw [h1]
    calc ∑ x ∈ A, J.Pmin (t - n) b x * J.Pmin n x b
        ≤ ∑ x ∈ A, J.Pmin (t - n) b x * G n := Finset.sum_le_sum fun x hx =>
          mul_le_mul_of_nonneg_left ((Finset.single_le_sum (f := fun y => J.Pmin n x y)
            (fun y _ => J.Pmin_nonneg _ (Nat.cast_nonneg n) x y) hbA).trans (hgle n x hx))
            (J.Pmin_nonneg _ (by linarith) b x)
      _ = (∑ x ∈ A, J.Pmin (t - n) b x) * G n := by rw [Finset.sum_mul]
      _ ≤ 1 * G n := mul_le_mul_of_nonneg_right (J.sum_Pmin_le_one _ (by linarith) b A) (hG0 n)
      _ = G n := one_mul _
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hP0]
  exact lt_of_le_of_lt (hbound.trans (hgeo n)) hn

end Network
end CRNT
