import CRNT.Stochastic.ProductFormErgodic
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Convergence to the stationary law on infinite irreducible classes

Let `E` be a set of states, closed under positive-rate jumps and irreducible, on which the minimal
transition function is stochastic (no explosion), and let `π` be an invariant probability supported
on `E`. Then for `a ∈ E` with `π(a) > 0`, `∑_b |P(t)(a, b) − π(b)| → 0` (`tendsto_l1_of_invariant`).

Proof, without coupling or compactness: the distance `D(t) = ∑_b |P(t)(a, b) − π(b)|` is
nonincreasing (`l1_step`); `P(t)(a, ·) ≤ π / π(a)`, so on the complement of a finite set `F ⊆ E`
both laws have uniformly small mass; on `F`, `P(1) ≥ δ > 0`, and the one-step estimate gives
`D(t + 1) ≤ (1 − δ|F|) D(t) + 2 δ |F| ε`, so `limsup D ≤ 2ε` for every `ε`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace CRNT

/-- **One-step ℓ¹ estimate.** `A` has nonnegative entries and stochastic rows on `E`; `ν` is
supported on `E` and dominated by a summable `B`. If `A ≥ δ ≥ 0` on `F × F`, then
`‖ν A‖₁ ≤ ‖ν‖₁ − 2 δ |F| min(∑_F ν⁺, ∑_F ν⁻)`. -/
theorem l1_step {α : Type*} {E : Set α} {A : α → α → ℝ} {ν B : α → ℝ}
    (hA0 : ∀ c b, 0 ≤ A c b) (hAs : ∀ c ∈ E, HasSum (A c) 1) (hνE : ∀ c, c ∉ E → ν c = 0)
    (hνB : ∀ c, |ν c| ≤ B c) (hB : Summable B) (F : Finset α) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : ∀ c ∈ F, ∀ b ∈ F, δ ≤ A c b) :
    ∑' b, |∑' c, ν c * A c b| ≤ ∑' c, |ν c| -
      2 * δ * F.card * min (∑ c ∈ F, max (ν c) 0) (∑ c ∈ F, max (-ν c) 0) := by
  classical
  set νp : α → ℝ := fun c => max (ν c) 0 with hνp
  set νm : α → ℝ := fun c => max (-ν c) 0 with hνm
  have hsplit : ∀ c, ν c = νp c - νm c := fun c => by
    simp only [hνp, hνm]; rcases le_total 0 (ν c) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h, max_eq_left (by linarith)]; ring
  have habs : ∀ c, |ν c| = νp c + νm c := fun c => by
    simp only [hνp, hνm]; rcases le_total 0 (ν c) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (by linarith)]; ring
  have hp0 : ∀ c, 0 ≤ νp c := fun c => le_max_right _ _
  have hm0 : ∀ c, 0 ≤ νm c := fun c => le_max_right _ _
  have hpB : ∀ c, νp c ≤ B c := fun c => by have := habs c; have := hνB c; linarith [hm0 c]
  have hmB : ∀ c, νm c ≤ B c := fun c => by have := habs c; have := hνB c; linarith [hp0 c]
  have hA1 : ∀ c ∈ E, ∀ b, A c b ≤ 1 := fun c hc b =>
    le_hasSum (hAs c hc) b fun b' _ => hA0 c b'
  -- every term `w c * A c b` with `0 ≤ w ≤ B`, `w` supported on `E` is bounded by `B c`
  have hterm : ∀ (w : α → ℝ), (∀ c, 0 ≤ w c) → (∀ c, w c ≤ B c) → (∀ c, c ∉ E → w c = 0) →
      ∀ b, Summable fun c => w c * A c b := by
    intro w hw0 hwB hwE b
    refine Summable.of_nonneg_of_le (fun c => mul_nonneg (hw0 c) (hA0 c b)) (fun c => ?_) hB
    by_cases hc : c ∈ E
    · exact (mul_le_of_le_one_right (hw0 c) (hA1 c hc b)).trans (hwB c)
    · rw [hwE c hc, zero_mul]; exact (abs_nonneg _).trans (hνB c)
  have hpE : ∀ c, c ∉ E → νp c = 0 := fun c hc => by simp [hνp, hνE c hc]
  have hmE : ∀ c, c ∉ E → νm c = 0 := fun c hc => by simp [hνm, hνE c hc]
  have hsp := hterm νp hp0 hpB hpE
  have hsm := hterm νm hm0 hmB hmE
  set X : α → ℝ := fun b => ∑' c, νp c * A c b with hX
  set Y : α → ℝ := fun b => ∑' c, νm c * A c b with hY
  have hX0 : ∀ b, 0 ≤ X b := fun b => tsum_nonneg fun c => mul_nonneg (hp0 c) (hA0 c b)
  have hY0 : ∀ b, 0 ≤ Y b := fun b => tsum_nonneg fun c => mul_nonneg (hm0 c) (hA0 c b)
  have hνA : ∀ b, ∑' c, ν c * A c b = X b - Y b := fun b => by
    show _ = (∑' c, νp c * A c b) - ∑' c, νm c * A c b
    rw [← (hsp b).tsum_sub (hsm b)]
    exact tsum_congr fun c => by rw [hsplit c]; ring
  -- the double series of `|ν c| A c b`
  set G : α → α → ℝ := fun c b => |ν c| * A c b with hG
  have hG0 : ∀ c b, 0 ≤ G c b := fun c b => mul_nonneg (abs_nonneg _) (hA0 c b)
  have hGrow : ∀ c, HasSum (G c) |ν c| := by
    intro c
    by_cases hc : c ∈ E
    · simpa [hG] using (hAs c hc).mul_left |ν c|
    · simp only [hG, hνE c hc, abs_zero, zero_mul]; exact hasSum_zero
  have hGsum : Summable (Function.uncurry G) := by
    refine (summable_prod_of_nonneg fun p => hG0 p.1 p.2).mpr ⟨fun c => (hGrow c).summable, ?_⟩
    simp only [Function.uncurry]
    refine Summable.of_nonneg_of_le (fun c => tsum_nonneg fun b => hG0 c b) (fun c => ?_) hB
    rw [(hGrow c).tsum_eq]; exact hνB c
  have hcolG : ∀ b, Summable fun c => G c b := hGsum.prod_symm.prod_factor
  have hswap : ∑' b, ∑' c, G c b = ∑' c, |ν c| := by
    rw [hGsum.tsum_comm]
    exact tsum_congr fun c => (hGrow c).tsum_eq
  have hXY : ∀ b, X b + Y b = ∑' c, G c b := fun b => by
    show (∑' c, νp c * A c b) + (∑' c, νm c * A c b) = _
    rw [← (hsp b).tsum_add (hsm b)]
    exact tsum_congr fun c => by
      show νp c * A c b + νm c * A c b = |ν c| * A c b
      rw [habs c]; ring
  have hsumG : Summable fun b => ∑' c, G c b := hGsum.prod_symm.prod
  -- the improvement on `F`
  set m := min (∑ c ∈ F, νp c) (∑ c ∈ F, νm c) with hm
  have hpointwise : ∀ b, |X b - Y b| ≤ ∑' c, G c b - (if b ∈ F then 2 * δ * m else 0) := by
    intro b
    rw [← hXY b]
    by_cases hb : b ∈ F
    · rw [if_pos hb]
      have hXF : δ * ∑ c ∈ F, νp c ≤ X b := by
        calc δ * ∑ c ∈ F, νp c = ∑ c ∈ F, νp c * δ := by rw [Finset.mul_sum]; simp [mul_comm]
          _ ≤ ∑ c ∈ F, νp c * A c b := Finset.sum_le_sum fun c hc =>
              mul_le_mul_of_nonneg_left (hδ c hc b hb) (hp0 c)
          _ ≤ X b := (hsp b).sum_le_tsum F fun c _ => mul_nonneg (hp0 c) (hA0 c b)
      have hYF : δ * ∑ c ∈ F, νm c ≤ Y b := by
        calc δ * ∑ c ∈ F, νm c = ∑ c ∈ F, νm c * δ := by rw [Finset.mul_sum]; simp [mul_comm]
          _ ≤ ∑ c ∈ F, νm c * A c b := Finset.sum_le_sum fun c hc =>
              mul_le_mul_of_nonneg_left (hδ c hc b hb) (hm0 c)
          _ ≤ Y b := (hsm b).sum_le_tsum F fun c _ => mul_nonneg (hm0 c) (hA0 c b)
      have hmin : δ * m ≤ min (X b) (Y b) := by
        rw [hm, mul_min_of_nonneg _ _ hδ0]
        exact min_le_min hXF hYF
      rcases le_total (X b) (Y b) with h | h
      · rw [abs_of_nonpos (by linarith), min_eq_left h] at *; linarith
      · rw [abs_of_nonneg (by linarith), min_eq_right h] at *; linarith
    · rw [if_neg hb, sub_zero]
      rcases le_total (X b) (Y b) with h | h
      · rw [abs_of_nonpos (by linarith)]; linarith [hX0 b]
      · rw [abs_of_nonneg (by linarith)]; linarith [hY0 b]
  have hind : Summable fun b => (if b ∈ F then 2 * δ * m else 0) :=
    summable_of_ne_finset_zero fun b hb => by rw [if_neg hb]
  have hindsum : ∑' b, (if b ∈ F then 2 * δ * m else 0) = 2 * δ * F.card * m := by
    rw [tsum_eq_sum (s := F) fun b hb => by rw [if_neg hb]]
    simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    ring
  have hle : ∑' b, |∑' c, ν c * A c b| ≤
      ∑' b, (∑' c, G c b - (if b ∈ F then 2 * δ * m else 0)) := by
    refine Summable.tsum_le_tsum (fun b => by rw [hνA b]; exact hpointwise b) ?_
      (hsumG.sub hind)
    refine Summable.of_nonneg_of_le (fun b => abs_nonneg _) (fun b => ?_) hsumG
    rw [hνA b, ← hXY b]
    exact (abs_sub _ _).trans (by rw [abs_of_nonneg (hX0 b), abs_of_nonneg (hY0 b)])
  rw [(hsumG.tsum_sub hind), hswap, hindsum] at hle
  exact hle

theorem tsum_split {α : Type*} [DecidableEq α] {f : α → ℝ} (hf : Summable f) (F : Finset α) :
    ∑' c, f c = ∑ c ∈ F, f c + ∑' c, (if c ∈ F then 0 else f c) := by
  have h1 : Summable fun c => (if c ∈ F then f c else 0) :=
    summable_of_ne_finset_zero fun c hc => by rw [if_neg hc]
  have h2 : Summable fun c => (if c ∈ F then 0 else f c) :=
    Summable.of_norm_bounded hf.norm fun c => by split_ifs <;> simp
  have hF : ∑' c, (if c ∈ F then f c else 0) = ∑ c ∈ F, f c := by
    rw [tsum_eq_sum (s := F) fun c hc => by rw [if_neg hc]]
    exact Finset.sum_congr rfl fun c hc => by rw [if_pos hc]
  rw [← hF, ← h1.tsum_add h2]
  exact tsum_congr fun c => by split_ifs <;> ring

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Convergence in total variation to an invariant law on an infinite irreducible class.** -/
theorem tendsto_l1_of_invariant {E : Set α}
    (hE : ∀ a ∈ E, ∀ i, 0 < J.rate i a → J.next i a ∈ E)
    (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b)
    (hstoch : ∀ t, 0 ≤ t → ∀ a ∈ E, HasSum (fun b => J.Pmin t a b) 1)
    {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπE : ∀ b, b ∉ E → π b = 0) (hπ1 : HasSum π 1)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b)
    {a : α} (ha : a ∈ E) (hπa : 0 < π a) :
    Tendsto (fun t => ∑' b, |J.Pmin t a b - π b|) atTop (𝓝 0) := by
  classical
  -- support in `E`
  have hmemE : ∀ {x c}, x ∈ E → J.ReachPos x c → c ∈ E := by
    intro x c hx h
    induction h with
    | refl => exact hx
    | tail _ hcd ih => obtain ⟨i, hr, rfl⟩ := hcd; exact hE _ ih i hr
  have hsupp : ∀ t {x c}, x ∈ E → c ∉ E → J.Pmin t x c = 0 := fun t x c hx hc =>
    J.Pmin_eq_zero_of_not_reachPos t fun h => hc (hmemE hx h)
  have hinvS : ∀ t, 0 ≤ t → ∀ b, HasSum (fun c => π c * J.Pmin t c b) (π b) := by
    intro t ht b
    have hs : Summable fun c => π c * J.Pmin t c b :=
      Summable.of_nonneg_of_le (fun c => mul_nonneg (hπ0 c) (J.Pmin_nonneg t ht c b))
        (fun c => mul_le_of_le_one_right (hπ0 c) (J.Pmin_le_one t ht c b)) hπ1.summable
    exact (hinv t ht b) ▸ hs.hasSum
  -- domination by `π / π(a)`
  set C : ℝ := 1 / π a + 1 with hC
  have hC0 : 0 < C := by positivity
  have hdom : ∀ t, 0 ≤ t → ∀ b, J.Pmin t a b ≤ π b / π a := by
    intro t ht b
    rw [le_div_iff₀ hπa, mul_comm]
    exact le_hasSum (hinvS t ht b) a fun c _ => mul_nonneg (hπ0 c) (J.Pmin_nonneg t ht c b)
  set ν : ℝ → α → ℝ := fun t b => J.Pmin t a b - π b with hν
  have hνB : ∀ t, 0 ≤ t → ∀ b, |ν t b| ≤ C * π b := by
    intro t ht b
    have h1 := hdom t ht b
    have h2 := J.Pmin_nonneg t ht a b
    have h3 := hπ0 b
    rw [abs_le]
    have : π b / π a = (1 / π a) * π b := by ring
    constructor <;> nlinarith
  have hνE : ∀ t c, c ∉ E → ν t c = 0 := fun t c hc => by simp [hν, hsupp t ha hc, hπE c hc]
  have hCπ : Summable fun b => C * π b := hπ1.summable.mul_left C
  have hνs : ∀ t, 0 ≤ t → Summable fun b => |ν t b| := fun t ht =>
    Summable.of_nonneg_of_le (fun b => abs_nonneg _) (hνB t ht) hCπ
  set D : ℝ → ℝ := fun t => ∑' b, |ν t b| with hD
  -- evolution of `ν`
  have hstep : ∀ t s, 0 ≤ t → 0 ≤ s → ∀ b, ν (t + s) b = ∑' c, ν t c * J.Pmin s c b := by
    intro t s ht hs b
    have h1 := J.hasSum_Pmin_add ht hs a b
    have h2 := hinvS s hs b
    refine ((h1.sub h2).congr_fun ?_).tsum_eq.symm ▸ rfl
    intro c; simp only [hν]; ring
  -- the one-step estimate in this setting
  have hone : ∀ t s, 0 ≤ t → 0 ≤ s → ∀ (F : Finset α) (δ : ℝ), 0 ≤ δ →
      (∀ c ∈ F, ∀ b ∈ F, δ ≤ J.Pmin s c b) →
      D (t + s) ≤ D t - 2 * δ * F.card *
        min (∑ c ∈ F, max (ν t c) 0) (∑ c ∈ F, max (-ν t c) 0) := by
    intro t s ht hs F δ hδ0 hδ
    have := l1_step (E := E) (A := fun c b => J.Pmin s c b) (ν := ν t) (B := fun b => C * π b)
      (fun c b => J.Pmin_nonneg s hs c b) (fun c hc => hstoch s hs c hc) (hνE t)
      (hνB t ht) hCπ F hδ0 hδ
    simp only [hD]
    rw [show (fun b => |ν (t + s) b|) = fun b => |∑' c, ν t c * J.Pmin s c b| from
      funext fun b => by rw [hstep t s ht hs b]]
    exact this
  have hmono : ∀ t s, 0 ≤ t → 0 ≤ s → D (t + s) ≤ D t := by
    intro t s ht hs
    have := hone t s ht hs ∅ 0 le_rfl (by simp)
    simpa using this
  have hD0 : ∀ t, 0 ≤ D t := fun t => tsum_nonneg fun b => abs_nonneg _
  have hD2 : ∀ t, 0 ≤ t → D t ≤ 2 := by
    intro t ht
    have hs : Summable fun b => J.Pmin t a b + π b :=
      (hstoch t ht a ha).summable.add hπ1.summable
    calc D t ≤ ∑' b, (J.Pmin t a b + π b) :=
          Summable.tsum_le_tsum (fun b => by
            simp only [hν]
            exact (abs_sub _ _).trans (by
              rw [abs_of_nonneg (J.Pmin_nonneg t ht a b), abs_of_nonneg (hπ0 b)])) (hνs t ht) hs
      _ = 2 := by rw [(hstoch t ht a ha).summable.tsum_add hπ1.summable,
          (hstoch t ht a ha).tsum_eq, hπ1.tsum_eq]; norm_num
  -- positive and negative parts each carry half of the distance
  have hhalf : ∀ t, 0 ≤ t → ∑' c, max (ν t c) 0 = D t / 2 ∧ ∑' c, max (-ν t c) 0 = D t / 2 := by
    intro t ht
    have hp : Summable fun c => max (ν t c) 0 :=
      Summable.of_nonneg_of_le (fun c => le_max_right _ _) (fun c => by
        rcases le_total 0 (ν t c) with h | h
        · rw [max_eq_left h, abs_of_nonneg h]
        · rw [max_eq_right h]; exact abs_nonneg _) (hνs t ht)
    have hm : Summable fun c => max (-ν t c) 0 :=
      Summable.of_nonneg_of_le (fun c => le_max_right _ _) (fun c => by
        rcases le_total 0 (ν t c) with h | h
        · rw [max_eq_right (by linarith)]; exact abs_nonneg _
        · rw [max_eq_left (by linarith), abs_of_nonpos h]) (hνs t ht)
    have hsum0 : ∑' c, ν t c = 0 := by
      simp only [hν]
      rw [(hstoch t ht a ha).summable.tsum_sub hπ1.summable, (hstoch t ht a ha).tsum_eq,
        hπ1.tsum_eq, sub_self]
    have e1 : ∑' c, max (ν t c) 0 - ∑' c, max (-ν t c) 0 = 0 := by
      rw [← hp.tsum_sub hm]
      calc ∑' c, (max (ν t c) 0 - max (-ν t c) 0) = ∑' c, ν t c := tsum_congr fun c => by
            rcases le_total 0 (ν t c) with h | h
            · rw [max_eq_left h, max_eq_right (by linarith)]; ring
            · rw [max_eq_right h, max_eq_left (by linarith)]; ring
        _ = 0 := hsum0
    have e2 : ∑' c, max (ν t c) 0 + ∑' c, max (-ν t c) 0 = D t := by
      rw [← hp.tsum_add hm]
      refine tsum_congr fun c => ?_
      rcases le_total 0 (ν t c) with h | h
      · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
      · rw [max_eq_right h, max_eq_left (by linarith), abs_of_nonpos h]; ring
    constructor <;> linarith
  refine Metric.tendsto_atTop.mpr fun ε' hε' => ?_
  set ε := ε' / 4 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨F0, hF0⟩ : ∃ F0 : Finset α, 1 - ε / C < ∑ c ∈ F0, π c :=
    (Filter.Tendsto.eventually hπ1 (lt_mem_nhds (by linarith [div_pos hε0 hC0]))).exists
  set F : Finset α := insert a (F0.filter (· ∈ E)) with hFdef
  have hFE : ∀ c ∈ F, c ∈ E := by
    intro c hc
    rw [hFdef, Finset.mem_insert, Finset.mem_filter] at hc
    rcases hc with rfl | ⟨_, h⟩
    · exact ha
    · exact h
  have hFsum : ∑ c ∈ F0, π c ≤ ∑ c ∈ F, π c := by
    calc ∑ c ∈ F0, π c = ∑ c ∈ F0.filter (· ∈ E), π c := by
          rw [Finset.sum_filter]
          exact Finset.sum_congr rfl fun c _ => by
            by_cases h : c ∈ E
            · rw [if_pos h]
            · rw [if_neg h, hπE c h]
      _ ≤ ∑ c ∈ F, π c := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _)
          fun c _ _ => hπ0 c
  have htr : ∀ {g : α → ℝ}, (∀ c, 0 ≤ g c) → Summable g →
      Summable fun c => (if c ∈ F then 0 else g c) := by
    intro g hg0 hg
    exact Summable.of_nonneg_of_le (fun c => by split_ifs; exacts [le_rfl, hg0 c])
      (fun c => by split_ifs; exacts [hg0 c, le_rfl]) hg
  have htail : ∑' c, (if c ∈ F then 0 else π c) < ε / C := by
    have := tsum_split hπ1.summable F
    rw [hπ1.tsum_eq] at this
    linarith
  have hνtail : ∀ t, 0 ≤ t → ∑' c, (if c ∈ F then 0 else |ν t c|) ≤ ε := by
    intro t ht
    calc ∑' c, (if c ∈ F then 0 else |ν t c|) ≤ ∑' c, (if c ∈ F then 0 else C * π c) :=
          Summable.tsum_le_tsum (fun c => by split_ifs; exacts [le_rfl, hνB t ht c])
            (htr (fun c => abs_nonneg _) (hνs t ht))
            (htr (fun c => mul_nonneg hC0.le (hπ0 c)) hCπ)
      _ = C * ∑' c, (if c ∈ F then 0 else π c) := by
          rw [← tsum_mul_left]; exact tsum_congr fun c => by split_ifs <;> ring
      _ ≤ C * (ε / C) := mul_le_mul_of_nonneg_left htail.le hC0.le
      _ = ε := by field_simp
  have hpart : ∀ t, 0 ≤ t → D t / 2 - ε ≤
      min (∑ c ∈ F, max (ν t c) 0) (∑ c ∈ F, max (-ν t c) 0) := by
    intro t ht
    obtain ⟨hp2, hm2⟩ := hhalf t ht
    have hle : ∀ (g : α → ℝ), (∀ c, 0 ≤ g c) → (∀ c, g c ≤ |ν t c|) →
        ∑' c, (if c ∈ F then 0 else g c) ≤ ε := fun g hg0 hgle =>
      (Summable.tsum_le_tsum (fun c => by split_ifs; exacts [le_rfl, hgle c])
        (htr hg0 (Summable.of_nonneg_of_le hg0 hgle (hνs t ht)))
        (htr (fun c => abs_nonneg _) (hνs t ht))).trans (hνtail t ht)
    have hgp : ∀ c, max (ν t c) 0 ≤ |ν t c| := fun c => max_le (le_abs_self _) (abs_nonneg _)
    have hgm : ∀ c, max (-ν t c) 0 ≤ |ν t c| := fun c => max_le (neg_le_abs _) (abs_nonneg _)
    have sp := tsum_split (Summable.of_nonneg_of_le (fun c => le_max_right _ _) hgp (hνs t ht)) F
    have sm := tsum_split (Summable.of_nonneg_of_le (fun c => le_max_right _ _) hgm (hνs t ht)) F
    have tp := hle _ (fun c => le_max_right _ _) hgp
    have tm := hle _ (fun c => le_max_right _ _) hgm
    exact le_min (by linarith) (by linarith)
  -- the Doeblin constant on `F`
  have hFne : F.Nonempty := ⟨a, Finset.mem_insert_self _ _⟩
  set δ := (F ×ˢ F).inf' (hFne.product hFne) (fun p => J.Pmin 1 p.1 p.2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    rintro ⟨x, y⟩ hp
    rw [Finset.mem_product] at hp
    exact J.Pmin_pos_of_reachPos (hirr x (hFE x hp.1) y (hFE y hp.2)) one_pos
  have hδle : ∀ x ∈ F, ∀ y ∈ F, δ ≤ J.Pmin 1 x y := fun x hx y hy => by
    rw [hδdef]
    exact Finset.inf'_le (fun p : α × α => J.Pmin 1 p.1 p.2) (Finset.mk_mem_product hx hy)
  set θ := δ * F.card with hθ
  have hθpos : 0 < θ := mul_pos hδpos (by exact_mod_cast Finset.card_pos.mpr hFne)
  have hθ1 : θ ≤ 1 := by
    calc θ = ∑ y ∈ F, δ := by simp [hθ, mul_comm]
      _ ≤ ∑ y ∈ F, J.Pmin 1 a y := Finset.sum_le_sum fun y hy =>
          hδle a (Finset.mem_insert_self _ _) y hy
      _ ≤ 1 := J.sum_Pmin_le_one 1 zero_le_one a F
  have hrec : ∀ t, 0 ≤ t → D (t + 1) ≤ (1 - θ) * D t + 2 * θ * ε := by
    intro t ht
    have h1 := hone t 1 ht zero_le_one F δ hδpos.le hδle
    have h2 := hpart t ht
    have h3 : 0 ≤ 2 * δ * F.card := by positivity
    have := mul_le_mul_of_nonneg_left h2 h3
    nlinarith
  have hgeo : ∀ n : ℕ, D n ≤ 2 * ε + 2 * (1 - θ) ^ n := by
    intro n
    induction n with
    | zero => simpa using (hD2 0 le_rfl).trans (by linarith)
    | succ n ih =>
        have h := hrec n (Nat.cast_nonneg n)
        rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by push_cast; ring, pow_succ]
        have h1θ : 0 ≤ 1 - θ := by linarith
        nlinarith [mul_le_mul_of_nonneg_left ih h1θ]
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one (show 0 < ε / 2 by positivity)
    (show 1 - θ < 1 by linarith)
  refine ⟨N, fun t ht => ?_⟩
  have htN : (N : ℝ) ≤ t := ht
  have hmon := hmono N (t - N) (Nat.cast_nonneg N) (by linarith)
  rw [add_sub_cancel] at hmon
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hD0 t)]
  have := hgeo N
  show D t < ε'
  linarith

/-- An invariant probability supported on an irreducible class charges every state of the class. -/
theorem invariant_pos {E : Set α} (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b)
    {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπE : ∀ b, b ∉ E → π b = 0) (hπ1 : HasSum π 1)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b) {a : α} (ha : a ∈ E) :
    0 < π a := by
  obtain ⟨c, hc⟩ : ∃ c, 0 < π c := by
    by_contra h
    push Not at h
    have : π = 0 := funext fun c => le_antisymm (h c) (hπ0 c)
    rw [this] at hπ1
    exact one_ne_zero (hasSum_zero.unique hπ1).symm
  have hcE : c ∈ E := by
    by_contra h
    rw [hπE c h] at hc
    exact lt_irrefl _ hc
  have hs : Summable fun x => π x * J.Pmin 1 x a :=
    Summable.of_nonneg_of_le (fun x => mul_nonneg (hπ0 x) (J.Pmin_nonneg 1 zero_le_one x a))
      (fun x => mul_le_of_le_one_right (hπ0 x) (J.Pmin_le_one 1 zero_le_one x a)) hπ1.summable
  have hle := le_hasSum ((hinv 1 zero_le_one a) ▸ hs.hasSum) c fun x _ =>
    mul_nonneg (hπ0 x) (J.Pmin_nonneg 1 zero_le_one x a)
  exact lt_of_lt_of_le (mul_pos hc (J.Pmin_pos_of_reachPos (hirr c hcE a ha) one_pos)) hle

/-- **Pointwise convergence and uniqueness of the invariant law** on an infinite irreducible
class: `P(t)(a, b) → π(b)` for `a ∈ E`, and every invariant probability supported on `E`
equals `π`. -/
theorem tendsto_Pmin_of_invariant {E : Set α}
    (hE : ∀ a ∈ E, ∀ i, 0 < J.rate i a → J.next i a ∈ E)
    (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b)
    (hstoch : ∀ t, 0 ≤ t → ∀ a ∈ E, HasSum (fun b => J.Pmin t a b) 1)
    {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπE : ∀ b, b ∉ E → π b = 0) (hπ1 : HasSum π 1)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b) {a : α} (ha : a ∈ E) (b : α) :
    Tendsto (fun t => J.Pmin t a b) atTop (𝓝 (π b)) := by
  have hl1 := J.tendsto_l1_of_invariant hE hirr hstoch hπ0 hπE hπ1 hinv ha
    (J.invariant_pos hirr hπ0 hπE hπ1 hinv ha)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun t => norm_nonneg _) ?_ hl1
  filter_upwards [eventually_ge_atTop 0] with t ht
  have hs : Summable fun x => |J.Pmin t a x - π x| :=
    Summable.of_nonneg_of_le (fun x => abs_nonneg _) (fun x => (abs_sub _ _).trans (by
      rw [abs_of_nonneg (J.Pmin_nonneg t ht a x), abs_of_nonneg (hπ0 x)]))
      ((hstoch t ht a ha).summable.add hπ1.summable)
  rw [Real.norm_eq_abs]
  exact hs.le_tsum b fun _ _ => abs_nonneg _

theorem invariant_unique {E : Set α}
    (hE : ∀ a ∈ E, ∀ i, 0 < J.rate i a → J.next i a ∈ E)
    (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b)
    (hstoch : ∀ t, 0 ≤ t → ∀ a ∈ E, HasSum (fun b => J.Pmin t a b) 1)
    {π : α → ℝ} (hπ0 : ∀ b, 0 ≤ π b) (hπE : ∀ b, b ∉ E → π b = 0) (hπ1 : HasSum π 1)
    (hinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, π c * J.Pmin t c b = π b)
    {μ : α → ℝ} (hμ0 : ∀ b, 0 ≤ μ b) (hμE : ∀ b, b ∉ E → μ b = 0) (hμ1 : HasSum μ 1)
    (hμinv : ∀ t, 0 ≤ t → ∀ b, ∑' c, μ c * J.Pmin t c b = μ b) (b : α) : μ b = π b := by
  have hlim : Tendsto (fun t => ∑' c, μ c * J.Pmin t c b) atTop (𝓝 (∑' c, μ c * π b)) := by
    refine tendsto_tsum_of_dominated_convergence (bound := μ) hμ1.summable (fun c => ?_) ?_
    · by_cases hc : c ∈ E
      · exact (J.tendsto_Pmin_of_invariant hE hirr hstoch hπ0 hπE hπ1 hinv hc b).const_mul _
      · simp only [hμE c hc, zero_mul]; exact tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop 0] with t ht
      intro c
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hμ0 c) (J.Pmin_nonneg t ht c b))]
      exact mul_le_of_le_one_right (hμ0 c) (J.Pmin_le_one t ht c b)
  have hconst : Tendsto (fun t => ∑' c, μ c * J.Pmin t c b) atTop (𝓝 (μ b)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop 0] with t ht
      exact (hμinv t ht b).symm)
  have := tendsto_nhds_unique hconst hlim
  rw [this, tsum_mul_right, hμ1.tsum_eq, one_mul]

end JumpSystem

end CRNT
