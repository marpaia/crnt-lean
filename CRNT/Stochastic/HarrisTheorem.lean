import CRNT.Stochastic.MinimalSemigroupMoments

/-!
# Harris's theorem (Hairer–Mattingly form) and geometric ergodicity

Let `A` be a stochastic kernel with the drift `∑_b A(x, b) V(b) ≤ γ V(x) + C` (`γ < 1`) and the
minorization `A(x, b₀) ≥ α` for `V(x) ≤ R`, with `R > 2C/(1 − γ)`. For
`β = α / (γ R + 2C + 1)` and `ᾱ = max (1 − α/2) ((2 + β γ₀ R)/(2 + β R))`, `γ₀ = γ + 2C/R`:

* pairs: `∑_b |A(x, b) − A(y, b)| (1 + βV(b)) ≤ ᾱ (2 + βV(x) + βV(y))` for `x ≠ y`
  (`harris_pair`);
* probabilities: `‖(μ − μ') A‖_β ≤ ᾱ ‖μ − μ'‖_β`, `‖ν‖_β = ∑_b |ν(b)| (1 + βV(b))`, via the product
  coupling of `ν⁺` and `ν⁻` (`harris_contraction`).

**Geometric ergodicity** of the minimal transition function (`JumpSystem.geometric_ergodic`): on a
countable irreducible state space, without explosion, under `QV ≤ −cV + K` with `V` having finite
sublevel sets, there are `β > 0`, `ρ < 1`, `C₀` with
`∑_b |P(t)(a, b) − π(b)| (1 + βV(b)) ≤ C₀ (1 + V(a)) ρ^{⌊t⌋}` (Meyn–Tweedie V-uniform ergodicity),
applying Harris's theorem to the skeleton kernel `P(1)`.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology ENNReal

namespace CRNT

namespace Harris

variable {α : Type*} [DecidableEq α]

/-- The data of Harris's theorem. -/
structure Hyp (A : α → α → ℝ) (V : α → ℝ) where
  γ : ℝ
  C : ℝ
  R : ℝ
  a : ℝ
  b₀ : α
  hA0 : ∀ x y, 0 ≤ A x y
  hA1 : ∀ x, HasSum (A x) 1
  hV0 : ∀ x, 0 ≤ V x
  hγ0 : 0 ≤ γ
  hγ1 : γ < 1
  hC : 0 ≤ C
  hR : 2 * C / (1 - γ) < R
  ha0 : 0 < a
  ha1 : a ≤ 1
  hdriftS : ∀ x, Summable fun y => A x y * V y
  hdrift : ∀ x, ∑' y, A x y * V y ≤ γ * V x + C
  hmin : ∀ x, V x ≤ R → a ≤ A x b₀

variable {A : α → α → ℝ} {V : α → ℝ} (H : Hyp A V)

namespace Hyp

theorem hR0 : 0 < H.R := lt_of_le_of_lt (div_nonneg (by linarith [H.hC]) (by linarith [H.hγ1])) H.hR

/-- `γ₀ = γ + 2C/R < 1`. -/
noncomputable def γ₀ : ℝ := H.γ + 2 * H.C / H.R

theorem γ₀_lt_one : H.γ₀ < 1 := by
  have h := H.hR
  have hR0 := H.hR0
  rw [div_lt_iff₀ (by linarith [H.hγ1])] at h
  unfold γ₀
  rw [← sub_pos]
  have : 1 - (H.γ + 2 * H.C / H.R) = ((1 - H.γ) * H.R - 2 * H.C) / H.R := by field_simp; ring
  rw [this]
  exact div_pos (by linarith) hR0

/-- The weight `β`. -/
noncomputable def β : ℝ := H.a / (H.γ * H.R + 2 * H.C + 1)

theorem β_pos : 0 < H.β := by
  unfold β
  have := H.hR0; have := H.hγ0; have := H.hC
  exact div_pos H.ha0 (by positivity)

theorem β_mul_le : H.β * (H.γ * H.R + 2 * H.C) ≤ H.a := by
  unfold β
  have := H.hR0; have := H.hγ0; have := H.hC
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
  nlinarith [H.ha0]

/-- The contraction rate. -/
noncomputable def rate : ℝ := max (1 - H.a / 2) ((2 + H.β * H.γ₀ * H.R) / (2 + H.β * H.R))

theorem rate_lt_one : H.rate < 1 := by
  unfold rate
  have hβ := H.β_pos; have hR := H.hR0; have hγ := H.γ₀_lt_one
  refine max_lt (by linarith [H.ha0]) ?_
  rw [div_lt_one (by positivity)]
  nlinarith [mul_pos hβ hR]

theorem rate_nonneg : 0 ≤ H.rate := le_trans (by linarith [H.ha1]) (le_max_left _ _)

theorem summable_row (x : α) : Summable fun y => A x y * (1 + H.β * V y) := by
  have := ((H.hA1 x).summable.add ((H.hdriftS x).mul_left H.β))
  exact this.congr fun y => by ring

theorem tsum_row (x : α) : ∑' y, A x y * (1 + H.β * V y) = 1 + H.β * ∑' y, A x y * V y := by
  rw [show (fun y => A x y * (1 + H.β * V y)) = fun y => A x y + H.β * (A x y * V y) from
    funext fun y => by ring, (H.hA1 x).summable.tsum_add ((H.hdriftS x).mul_left H.β),
    (H.hA1 x).tsum_eq, tsum_mul_left]

/-- **The pair estimate.** -/
theorem harris_pair (x y : α) :
    ∑' b, |A x b - A y b| * (1 + H.β * V b) ≤ H.rate * (2 + H.β * V x + H.β * V y) := by
  have hβ := H.β_pos
  have hs : Summable fun b => |A x b - A y b| * (1 + H.β * V b) :=
    Summable.of_nonneg_of_le (fun b => mul_nonneg (abs_nonneg _) (by have := H.hV0 b; positivity))
      (fun b => by
        have h1 : |A x b - A y b| ≤ A x b + A y b := (abs_sub _ _).trans (by
          rw [abs_of_nonneg (H.hA0 x b), abs_of_nonneg (H.hA0 y b)])
        have h2 : 0 ≤ 1 + H.β * V b := by have := H.hV0 b; positivity
        calc |A x b - A y b| * (1 + H.β * V b) ≤ (A x b + A y b) * (1 + H.β * V b) :=
              mul_le_mul_of_nonneg_right h1 h2
          _ = A x b * (1 + H.β * V b) + A y b * (1 + H.β * V b) := by ring)
      ((H.summable_row x).add (H.summable_row y))
  have hsum2 : ∑' b, (A x b * (1 + H.β * V b) + A y b * (1 + H.β * V b)) =
      2 + H.β * (∑' b, A x b * V b + ∑' b, A y b * V b) := by
    rw [(H.summable_row x).tsum_add (H.summable_row y), H.tsum_row, H.tsum_row]; ring
  have hDx := H.hdrift x
  have hDy := H.hdrift y
  have hVx := H.hV0 x
  have hVy := H.hV0 y
  by_cases hbig : H.R ≤ V x + V y
  · -- drift case
    have hle : ∑' b, |A x b - A y b| * (1 + H.β * V b) ≤ 2 + H.β * (H.γ * (V x + V y) + 2 * H.C) := by
      refine (Summable.tsum_le_tsum (fun b => ?_) hs
        ((H.summable_row x).add (H.summable_row y))).trans ?_
      · have h1 : |A x b - A y b| ≤ A x b + A y b := (abs_sub _ _).trans (by
          rw [abs_of_nonneg (H.hA0 x b), abs_of_nonneg (H.hA0 y b)])
        have h2 : 0 ≤ 1 + H.β * V b := by have := H.hV0 b; positivity
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]
      · rw [hsum2]
        have := mul_le_mul_of_nonneg_left (add_le_add hDx hDy) hβ.le
        linarith
    have hγ0 : 2 * H.C ≤ (H.γ₀ - H.γ) * (V x + V y) := by
      unfold γ₀
      have hR0 := H.hR0
      rw [add_sub_cancel_left, div_mul_eq_mul_div, le_div_iff₀ hR0]
      nlinarith [H.hC]
    have h3 : 2 + H.β * (H.γ * (V x + V y) + 2 * H.C) ≤ 2 + H.β * (H.γ₀ * (V x + V y)) := by
      nlinarith
    have h4 : 2 + H.β * (H.γ₀ * (V x + V y)) ≤
        (2 + H.β * H.γ₀ * H.R) / (2 + H.β * H.R) * (2 + H.β * V x + H.β * V y) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ (by have := H.hR0; positivity)]
      have h1 : 0 ≤ H.β * (1 - H.γ₀) * (V x + V y - H.R) :=
        mul_nonneg (mul_nonneg hβ.le (by linarith [H.γ₀_lt_one])) (by linarith)
      nlinarith [h1]
    calc _ ≤ 2 + H.β * (H.γ * (V x + V y) + 2 * H.C) := hle
      _ ≤ _ := h3.trans (h4.trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (by positivity)))
  · -- minorization case
    push Not at hbig
    have hxR : V x ≤ H.R := by linarith
    have hyR : V y ≤ H.R := by linarith
    have hmx := H.hmin x hxR
    have hmy := H.hmin y hyR
    have hpt : ∀ b, |A x b - A y b| * (1 + H.β * V b) ≤
        A x b * (1 + H.β * V b) + A y b * (1 + H.β * V b) -
          (if b = H.b₀ then 2 * H.a * (1 + H.β * V b) else 0) := by
      intro b
      have h2 : 0 ≤ 1 + H.β * V b := by have := H.hV0 b; positivity
      split_ifs with hb
      · subst hb
        have : |A x H.b₀ - A y H.b₀| ≤ A x H.b₀ + A y H.b₀ - 2 * H.a := by
          rw [abs_le]; constructor <;> linarith
        nlinarith [mul_le_mul_of_nonneg_right this h2]
      · have h1 : |A x b - A y b| ≤ A x b + A y b := (abs_sub _ _).trans (by
          rw [abs_of_nonneg (H.hA0 x b), abs_of_nonneg (H.hA0 y b)])
        nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    have hind : Summable fun b => (if b = H.b₀ then 2 * H.a * (1 + H.β * V b) else 0) :=
      summable_of_ne_finset_zero (s := {H.b₀}) fun b hb => by
        rw [Finset.mem_singleton] at hb; rw [if_neg hb]
    have hindsum : ∑' b, (if b = H.b₀ then 2 * H.a * (1 + H.β * V b) else 0) =
        2 * H.a * (1 + H.β * V H.b₀) := by
      rw [tsum_eq_single H.b₀ fun b hb => if_neg hb]; simp
    have hle := Summable.tsum_le_tsum hpt hs (((H.summable_row x).add (H.summable_row y)).sub hind)
    rw [(((H.summable_row x).add (H.summable_row y))).tsum_sub hind, hsum2, hindsum] at hle
    have hVb := H.hV0 H.b₀
    have h5 : H.β * (∑' b, A x b * V b + ∑' b, A y b * V b) ≤ H.a := by
      have h1 : ∑' b, A x b * V b + ∑' b, A y b * V b ≤ H.γ * H.R + 2 * H.C := by
        have := mul_le_mul_of_nonneg_left (show V x + V y ≤ H.R by linarith) H.hγ0
        linarith
      exact (mul_le_mul_of_nonneg_left h1 hβ.le).trans H.β_mul_le
    have h6 : 2 - H.a ≤ (1 - H.a / 2) * (2 + H.β * V x + H.β * V y) := by
      have := H.ha1
      nlinarith [mul_nonneg hβ.le hVx, mul_nonneg hβ.le hVy]
    calc _ ≤ 2 + H.β * (∑' b, A x b * V b + ∑' b, A y b * V b) - 2 * H.a * (1 + H.β * V H.b₀) := hle
      _ ≤ 2 - H.a := by
          have := mul_nonneg (mul_nonneg H.ha0.le hβ.le) hVb
          nlinarith
      _ ≤ _ := h6.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))

omit [DecidableEq α] in
theorem summable_prod_mul {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Summable f) (hg : Summable g) : Summable fun z : α × α => f z.1 * g z.2 :=
  summable_mul_of_summable_norm (hf.congr fun x => (Real.norm_of_nonneg (hf0 x)).symm)
    (hg.congr fun x => (Real.norm_of_nonneg (hg0 x)).symm)

omit [DecidableEq α] in
theorem tsum_prod_mul {f g : α → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf : Summable f) (hg : Summable g) :
    ∑' z : α × α, f z.1 * g z.2 = (∑' x, f x) * ∑' y, g y :=
  (tsum_mul_tsum_of_summable_norm (hf.congr fun x => (Real.norm_of_nonneg (hf0 x)).symm)
    (hg.congr fun x => (Real.norm_of_nonneg (hg0 x)).symm)).symm

/-- **Harris contraction** for differences of probabilities, through the product coupling. -/
theorem harris_contraction {μ μ' : α → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (hμ'0 : ∀ x, 0 ≤ μ' x)
    (hμ1 : HasSum μ 1) (hμ'1 : HasSum μ' 1) (hμV : Summable fun x => μ x * V x)
    (hμ'V : Summable fun x => μ' x * V x) :
    ∑' b, |∑' x, (μ x - μ' x) * A x b| * (1 + H.β * V b) ≤
      H.rate * ∑' x, |μ x - μ' x| * (1 + H.β * V x) := by
  have hβ := H.β_pos
  set p : α → ℝ := fun x => max (μ x - μ' x) 0 with hp
  set n : α → ℝ := fun x => max (μ' x - μ x) 0 with hn
  have hp0 : ∀ x, 0 ≤ p x := fun x => le_max_right _ _
  have hn0 : ∀ x, 0 ≤ n x := fun x => le_max_right _ _
  have hpμ : ∀ x, p x ≤ μ x := fun x => max_le (by linarith [hμ'0 x]) (hμ0 x)
  have hnμ : ∀ x, n x ≤ μ' x := fun x => max_le (by linarith [hμ0 x]) (hμ'0 x)
  have hsplit : ∀ x, μ x - μ' x = p x - n x := fun x => by
    simp only [hp, hn]; rcases le_total (μ x) (μ' x) with h | h
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have habs : ∀ x, |μ x - μ' x| = p x + n x := fun x => by
    simp only [hp, hn]; rcases le_total (μ x) (μ' x) with h | h
    · rw [abs_of_nonpos (by linarith), max_eq_right (by linarith), max_eq_left (by linarith)]; ring
    · rw [abs_of_nonneg (by linarith), max_eq_left (by linarith), max_eq_right (by linarith)]; ring
  have hps : Summable p := Summable.of_nonneg_of_le hp0 hpμ hμ1.summable
  have hns : Summable n := Summable.of_nonneg_of_le hn0 hnμ hμ'1.summable
  have hpV : Summable fun x => p x * V x := Summable.of_nonneg_of_le
    (fun x => mul_nonneg (hp0 x) (H.hV0 x)) (fun x => mul_le_mul_of_nonneg_right (hpμ x) (H.hV0 x)) hμV
  have hnV : Summable fun x => n x * V x := Summable.of_nonneg_of_le
    (fun x => mul_nonneg (hn0 x) (H.hV0 x)) (fun x => mul_le_mul_of_nonneg_right (hnμ x) (H.hV0 x))
    hμ'V
  set m := ∑' x, p x with hm
  have hmn : ∑' x, n x = m := by
    have h := (hμ1.sub hμ'1).tsum_eq
    rw [sub_self] at h
    have : ∑' x, (p x - n x) = 0 := by rw [← h]; exact tsum_congr fun x => (hsplit x).symm
    rw [hps.tsum_sub hns] at this
    linarith
  -- the right-hand side
  have hRHS : ∑' x, |μ x - μ' x| * (1 + H.β * V x) =
      2 * m + H.β * (∑' x, p x * V x + ∑' x, n x * V x) := by
    have e : (fun x => |μ x - μ' x| * (1 + H.β * V x)) =
        fun x => (p x + n x) + H.β * (p x * V x + n x * V x) := funext fun x => by rw [habs]; ring
    rw [e, (hps.add hns).tsum_add ((hpV.add hnV).mul_left _), tsum_mul_left, hps.tsum_add hns,
      hpV.tsum_add hnV, hmn]
    ring
  by_cases hm0 : m = 0
  · -- `μ = μ'`
    have hpz : ∀ x, p x = 0 := by
      have h : HasSum p 0 := hm0 ▸ hps.hasSum
      exact fun x => congrFun ((hasSum_zero_iff_of_nonneg hp0).mp h) x
    have hnz : ∀ x, n x = 0 := by
      have h : HasSum n 0 := (hmn.trans hm0) ▸ hns.hasSum
      exact fun x => congrFun ((hasSum_zero_iff_of_nonneg hn0).mp h) x
    have hz : ∀ x, μ x - μ' x = 0 := fun x => by rw [hsplit, hpz, hnz, sub_zero]
    have hL : ∑' b, |∑' x, (μ x - μ' x) * A x b| * (1 + H.β * V b) = 0 := by simp [hz]
    rw [hL]
    exact mul_nonneg H.rate_nonneg (tsum_nonneg fun x =>
      mul_nonneg (abs_nonneg _) (by have := H.hV0 x; positivity))
  have hmpos : 0 < m := lt_of_le_of_ne (tsum_nonneg hp0) (Ne.symm hm0)
  -- the coupling
  set W : α × α → ℝ := fun z => p z.1 * n z.2 / m with hW
  have hW0 : ∀ z, 0 ≤ W z := fun z => div_nonneg (mul_nonneg (hp0 _) (hn0 _)) hmpos.le
  have hWs : Summable W := (summable_prod_mul hp0 hn0 hps hns).div_const m
  have hA1 : ∀ x b, A x b ≤ 1 := fun x b => le_hasSum (H.hA1 x) b fun b' _ => H.hA0 x b'
  -- marginals of the coupling against `A`
  have hpA : ∀ b, ∑' x, p x * A x b = ∑' z, W z * A z.1 b := by
    intro b
    have hs : Summable fun x => p x * A x b := Summable.of_nonneg_of_le
      (fun x => mul_nonneg (hp0 x) (H.hA0 x b)) (fun x => mul_le_of_le_one_right (hp0 x) (hA1 x b))
      hps
    have h := tsum_prod_mul (fun x => mul_nonneg (hp0 x) (H.hA0 x b)) hn0 hs hns
    rw [hmn] at h
    have e : (fun z : α × α => W z * A z.1 b) = fun z => p z.1 * A z.1 b * n z.2 / m :=
      funext fun z => by simp only [hW]; ring
    rw [e, tsum_div_const, h, mul_div_assoc, div_self hm0, mul_one]
  have hnA : ∀ b, ∑' y, n y * A y b = ∑' z, W z * A z.2 b := by
    intro b
    have hs : Summable fun x => n x * A x b := Summable.of_nonneg_of_le
      (fun x => mul_nonneg (hn0 x) (H.hA0 x b)) (fun x => mul_le_of_le_one_right (hn0 x) (hA1 x b))
      hns
    have h := tsum_prod_mul hp0 (fun x => mul_nonneg (hn0 x) (H.hA0 x b)) hps hs
    have e : (fun z : α × α => W z * A z.2 b) = fun z => p z.1 * (n z.2 * A z.2 b) / m :=
      funext fun z => by simp only [hW]; ring
    rw [e, tsum_div_const, h, ← hm, mul_comm, mul_div_assoc, div_self hm0, mul_one]
  have hW1 : ∀ b, Summable fun z => W z * A z.1 b := fun b => Summable.of_nonneg_of_le
    (fun z => mul_nonneg (hW0 z) (H.hA0 _ _)) (fun z => mul_le_of_le_one_right (hW0 z) (hA1 _ _)) hWs
  have hW2 : ∀ b, Summable fun z => W z * A z.2 b := fun b => Summable.of_nonneg_of_le
    (fun z => mul_nonneg (hW0 z) (H.hA0 _ _)) (fun z => mul_le_of_le_one_right (hW0 z) (hA1 _ _)) hWs
  have hWAs : ∀ b, Summable fun z => W z * |A z.1 b - A z.2 b| := fun b =>
    Summable.of_nonneg_of_le (fun z => mul_nonneg (hW0 z) (abs_nonneg _)) (fun z => by
      have : |A z.1 b - A z.2 b| ≤ 1 := abs_sub_le_iff.mpr
        ⟨by linarith [hA1 z.1 b, H.hA0 z.2 b], by linarith [hA1 z.2 b, H.hA0 z.1 b]⟩
      exact mul_le_of_le_one_right (hW0 z) this) hWs
  -- the coupling bound at each `b`
  have hνA : ∀ b, |∑' x, (μ x - μ' x) * A x b| ≤ ∑' z, W z * |A z.1 b - A z.2 b| := by
    intro b
    have hs1 : Summable fun x => p x * A x b := Summable.of_nonneg_of_le
      (fun x => mul_nonneg (hp0 x) (H.hA0 x b)) (fun x => mul_le_of_le_one_right (hp0 x) (hA1 x b))
      hps
    have hs2 : Summable fun x => n x * A x b := Summable.of_nonneg_of_le
      (fun x => mul_nonneg (hn0 x) (H.hA0 x b)) (fun x => mul_le_of_le_one_right (hn0 x) (hA1 x b))
      hns
    have e : ∑' x, (μ x - μ' x) * A x b = ∑' z, W z * (A z.1 b - A z.2 b) := by
      rw [show (fun x => (μ x - μ' x) * A x b) = fun x => p x * A x b - n x * A x b from
        funext fun x => by rw [hsplit]; ring, hs1.tsum_sub hs2, hpA, hnA,
        ← (hW1 b).tsum_sub (hW2 b)]
      exact tsum_congr fun z => by ring
    rw [e]
    have hn : Summable fun z => ‖W z * (A z.1 b - A z.2 b)‖ := (hWAs b).congr fun z => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 z)]
    have := norm_tsum_le_tsum_norm hn
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq (tsum_congr fun z => ?_))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 z)]
  -- the triple sum
  set G : α × α → α → ℝ := fun z b => W z * (|A z.1 b - A z.2 b| * (1 + H.β * V b)) with hG
  have hwt : ∀ b, 0 ≤ 1 + H.β * V b := fun b => by have := H.hV0 b; positivity
  have hG0 : ∀ z b, 0 ≤ G z b := fun z b =>
    mul_nonneg (hW0 z) (mul_nonneg (abs_nonneg _) (hwt b))
  have hGrow : ∀ z, Summable (G z) := fun z =>
    Summable.of_nonneg_of_le (hG0 z) (fun b => by
      have h1 : |A z.1 b - A z.2 b| ≤ A z.1 b + A z.2 b := (abs_sub _ _).trans (by
        rw [abs_of_nonneg (H.hA0 _ b), abs_of_nonneg (H.hA0 _ b)])
      have h2 := mul_le_mul_of_nonneg_right h1 (hwt b)
      have h3 := mul_le_mul_of_nonneg_left h2 (hW0 z)
      calc G z b ≤ W z * ((A z.1 b + A z.2 b) * (1 + H.β * V b)) := h3
        _ = W z * (A z.1 b * (1 + H.β * V b) + A z.2 b * (1 + H.β * V b)) := by ring)
      (((H.summable_row z.1).add (H.summable_row z.2)).mul_left (W z))
  have hGbound : ∀ z, ∑' b, G z b ≤ W z * (H.rate * (2 + H.β * V z.1 + H.β * V z.2)) := by
    intro z
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (H.harris_pair z.1 z.2) (hW0 z)
  have hWV1 : Summable fun z => W z * V z.1 :=
    ((summable_prod_mul (fun x => mul_nonneg (hp0 x) (H.hV0 x)) hn0 hpV hns).div_const m).congr
      fun z => by simp only [hW]; ring
  have hWV2 : Summable fun z => W z * V z.2 :=
    ((summable_prod_mul hp0 (fun x => mul_nonneg (hn0 x) (H.hV0 x)) hps hnV).div_const m).congr
      fun z => by simp only [hW]; ring
  have hWV : Summable fun z => W z * (H.rate * (2 + H.β * V z.1 + H.β * V z.2)) :=
    ((hWs.mul_left 2).add ((hWV1.mul_left H.β).add (hWV2.mul_left H.β))).mul_left H.rate |>.congr
      fun z => by ring
  have hGsum : Summable (Function.uncurry G) :=
    (summable_prod_of_nonneg fun q => hG0 q.1 q.2).mpr ⟨fun z => hGrow z,
      Summable.of_nonneg_of_le (fun z => tsum_nonneg (hG0 z)) hGbound hWV⟩
  have hcol : Summable fun b => ∑' z, G z b := hGsum.prod_symm.prod
  have hLb : ∀ b, |∑' x, (μ x - μ' x) * A x b| * (1 + H.β * V b) ≤ ∑' z, G z b := by
    intro b
    calc |∑' x, (μ x - μ' x) * A x b| * (1 + H.β * V b)
        ≤ (∑' z, W z * |A z.1 b - A z.2 b|) * (1 + H.β * V b) :=
          mul_le_mul_of_nonneg_right (hνA b) (hwt b)
      _ = ∑' z, G z b := by rw [← tsum_mul_right]; exact tsum_congr fun z => by simp only [hG]; ring
  have hLs : Summable fun b => |∑' x, (μ x - μ' x) * A x b| * (1 + H.β * V b) :=
    Summable.of_nonneg_of_le (fun b => mul_nonneg (abs_nonneg _) (hwt b)) hLb hcol
  have e1 : ∑' z, W z = m := by
    rw [show (∑' z, W z) = ∑' z : α × α, p z.1 * n z.2 / m from rfl, tsum_div_const,
      tsum_prod_mul hp0 hn0 hps hns, hmn, ← hm]
    field_simp
  have e2 : ∑' z, W z * V z.1 = ∑' x, p x * V x := by
    rw [show (fun z : α × α => W z * V z.1) = fun z => (p z.1 * V z.1) * n z.2 / m from
      funext fun z => by simp only [hW]; ring, tsum_div_const,
      tsum_prod_mul (fun x => mul_nonneg (hp0 x) (H.hV0 x)) hn0 hpV hns, hmn]
    field_simp
  have e3 : ∑' z, W z * V z.2 = ∑' x, n x * V x := by
    rw [show (fun z : α × α => W z * V z.2) = fun z => p z.1 * (n z.2 * V z.2) / m from
      funext fun z => by simp only [hW]; ring, tsum_div_const,
      tsum_prod_mul hp0 (fun x => mul_nonneg (hn0 x) (H.hV0 x)) hps hnV, ← hm]
    field_simp
  have e4 : ∑' z, W z * (H.rate * (2 + H.β * V z.1 + H.β * V z.2)) =
      H.rate * (2 * m + H.β * (∑' x, p x * V x + ∑' x, n x * V x)) := by
    rw [show (fun z => W z * (H.rate * (2 + H.β * V z.1 + H.β * V z.2))) =
      fun z => H.rate * (2 * W z + (H.β * (W z * V z.1) + H.β * (W z * V z.2))) from
      funext fun z => by ring, tsum_mul_left,
      (hWs.mul_left 2).tsum_add ((hWV1.mul_left H.β).add (hWV2.mul_left H.β)),
      (hWV1.mul_left H.β).tsum_add (hWV2.mul_left H.β), tsum_mul_left, tsum_mul_left,
      tsum_mul_left, e1, e2, e3]
    ring
  calc ∑' b, |∑' x, (μ x - μ' x) * A x b| * (1 + H.β * V b)
      ≤ ∑' b, ∑' z, G z b := Summable.tsum_le_tsum hLb hLs hcol
    _ = ∑' z, ∑' b, G z b := hGsum.tsum_comm
    _ ≤ ∑' z, W z * (H.rate * (2 + H.β * V z.1 + H.β * V z.2)) :=
        Summable.tsum_le_tsum hGbound hGsum.prod hWV
    _ = H.rate * ∑' x, |μ x - μ' x| * (1 + H.β * V x) := by rw [e4, hRHS]

end Hyp

end Harris


namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- **Geometric (V-uniform) ergodicity.** -/
theorem geometric_ergodic [Countable α] [Nonempty α] (V : α → ℝ) (hV0 : ∀ x, 0 ≤ V x)
    (hfinV : ∀ R : ℝ, {x | V x ≤ R}.Finite) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K)
    (hdrift : ∀ x, J.drift V x ≤ -c * V x + K)
    (hstoch : ∀ t, 0 ≤ t → ∀ x, HasSum (fun b => J.Pmin t x b) 1)
    (hirr : ∀ a b, J.ReachPos a b) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * J.Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |J.Pmin t a b - π b| * (1 + β * V b) ≤ C₀ * (1 + V a) * ρ ^ ⌊t⌋₊ := by
  classical
  obtain ⟨a₀⟩ := ‹Nonempty α›
  have hdr : ∀ x, J.drift V x ≤ -(c * V x) + K := fun x => by linarith [hdrift x]
  have hfin' : ∀ R : ℝ, {x | c * V x ≤ R}.Finite := fun R =>
    (hfinV (R / c)).subset fun x hx => by
      simp only [Set.mem_ofPred_eq] at hx ⊢
      rw [le_div_iff₀ hc]; linarith
  obtain ⟨π, hπ0, hπ1, hinv, hπE, -, -, -⟩ := J.foster_lyapunov_ergodic V (fun x => c * V x)
    hV0 (fun x => mul_nonneg hc.le (hV0 x)) hfin' hK hdr hstoch (E := Set.univ)
    (fun _ _ _ _ => Set.mem_univ _) (fun a _ b _ => hirr a b) (Set.mem_univ a₀)
  have hst : ∀ t, 0 ≤ t → ∀ a ∈ (Set.univ : Set α), HasSum (fun b => J.Pmin t a b) 1 :=
    fun t ht a _ => hstoch t ht a
  -- moments
  have hmomP : ∀ a, ∀ t, 0 ≤ t → ∀ F : Finset α, ∑ b ∈ F, J.Pmin t a b * V b ≤ V a + K / c := by
    intro a t ht F
    have h := J.sum_Pmin_mul_le_contract V hV0 hc hK hdrift ht a F
    have he1 : Real.exp (-(c * t)) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    have h1 : Real.exp (-(c * t)) * V a ≤ V a := mul_le_of_le_one_left (hV0 a) he1
    have h2 : K / c * (1 - Real.exp (-(c * t))) ≤ K / c :=
      mul_le_of_le_one_right (div_nonneg hK hc.le) (by linarith [Real.exp_pos (-(c * t))])
    linarith
  have hsPV : ∀ a, ∀ t, 0 ≤ t → Summable fun b => J.Pmin t a b * V b := fun a t ht =>
    summable_of_sum_le (fun b => mul_nonneg (J.Pmin_nonneg t ht a b) (hV0 b)) (hmomP a t ht)
  have hpt : ∀ b, Tendsto (fun t => J.Pmin t a₀ b) atTop (𝓝 (π b)) := fun b =>
    J.tendsto_Pmin_of_invariant (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
      (fun a _ b _ => hirr a b) hst hπ0 hπE hπ1 hinv (Set.mem_univ a₀) b
  have hmomπ : ∀ F : Finset α, ∑ b ∈ F, π b * V b ≤ V a₀ + K / c := fun F =>
    le_of_tendsto (tendsto_finsetSum _ fun b _ => (hpt b).mul_const _)
      ((eventually_ge_atTop 0).mono fun t ht => hmomP a₀ t ht F)
  have hπV : Summable fun b => π b * V b :=
    summable_of_sum_le (fun b => mul_nonneg (hπ0 b) (hV0 b)) hmomπ
  set M := ∑' b, π b * V b with hM
  have hM0 : 0 ≤ M := tsum_nonneg fun b => mul_nonneg (hπ0 b) (hV0 b)
  -- the skeleton kernel
  set γ := Real.exp (-c) with hγ
  set C := K / c * (1 - Real.exp (-c)) with hC
  have hγ1 : γ < 1 := by rw [hγ]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hγ0 : 0 ≤ γ := (Real.exp_pos _).le
  have hC0 : 0 ≤ C := mul_nonneg (div_nonneg hK hc.le) (by linarith)
  set R := 2 * C / (1 - γ) + 1 with hR
  set FR := (hfinV R).toFinset with hFR
  have hFR' : ∀ x, x ∈ FR ↔ V x ≤ R := fun x => by simp [hFR]
  set a : ℝ := if h : FR.Nonempty then FR.inf' h (fun x => J.Pmin 1 x a₀) else 1 with ha
  have ha0 : 0 < a := by
    rw [ha]; split_ifs with h
    · rw [Finset.lt_inf'_iff]
      exact fun x _ => J.Pmin_pos_of_reachPos (hirr x a₀) one_pos
    · exact one_pos
  have ha1 : a ≤ 1 := by
    rw [ha]; split_ifs with h
    · obtain ⟨x, hx⟩ := h
      exact (Finset.inf'_le _ hx).trans (J.Pmin_le_one 1 zero_le_one x a₀)
    · exact le_rfl
  have hmin : ∀ x, V x ≤ R → a ≤ J.Pmin 1 x a₀ := by
    intro x hx
    have hxF : x ∈ FR := (hFR' x).mpr hx
    rw [ha, dif_pos ⟨x, hxF⟩]
    exact Finset.inf'_le _ hxF
  let H : Harris.Hyp (fun x y => J.Pmin 1 x y) V :=
    { γ := γ, C := C, R := R, a := a, b₀ := a₀
      hA0 := fun x y => J.Pmin_nonneg 1 zero_le_one x y
      hA1 := fun x => hstoch 1 zero_le_one x
      hV0 := hV0, hγ0 := hγ0, hγ1 := hγ1, hC := hC0
      hR := by rw [hR]; linarith
      ha0 := ha0, ha1 := ha1
      hdriftS := fun x => hsPV x 1 zero_le_one
      hdrift := fun x => by
        have h := (hsPV x 1 zero_le_one).tsum_le_of_sum_le
          (J.sum_Pmin_mul_le_contract V hV0 hc hK hdrift zero_le_one x)
        simpa [hγ, hC, mul_one] using h
      hmin := hmin }
  set β := H.β with hβ
  set ρ := H.rate with hρ
  have hβ0 : 0 < β := H.β_pos
  -- one step
  set D : α → ℝ → ℝ := fun x t => ∑' b, |J.Pmin t x b - π b| * (1 + β * V b) with hD
  have hstep : ∀ x, ∀ s, 0 ≤ s → D x (s + 1) ≤ ρ * D x s := by
    intro x s hs
    have h := H.harris_contraction (μ := fun y => J.Pmin s x y) (μ' := π)
      (fun y => J.Pmin_nonneg s hs x y) hπ0 (hstoch s hs x) hπ1 (hsPV x s hs) hπV
    have hev : ∀ b, ∑' y, (J.Pmin s x y - π y) * J.Pmin 1 y b = J.Pmin (s + 1) x b - π b := by
      intro b
      have h1 := J.hasSum_Pmin_add hs zero_le_one x b
      have h2 : Summable fun y => π y * J.Pmin 1 y b := Summable.of_nonneg_of_le
        (fun y => mul_nonneg (hπ0 y) (J.Pmin_nonneg 1 zero_le_one y b))
        (fun y => mul_le_of_le_one_right (hπ0 y) (J.Pmin_le_one 1 zero_le_one y b)) hπ1.summable
      rw [show (fun y => (J.Pmin s x y - π y) * J.Pmin 1 y b) =
        fun y => J.Pmin s x y * J.Pmin 1 y b - π y * J.Pmin 1 y b from funext fun y => by ring,
        h1.summable.tsum_sub h2, h1.tsum_eq, hinv 1 zero_le_one b]
    simp only [hev] at h
    exact h
  -- a uniform bound
  have hbound : ∀ x, ∀ s, 0 ≤ s → D x s ≤ 2 + β * (V x + K / c) + β * M := by
    intro x s hs
    have hs1 : Summable fun b => (J.Pmin s x b + π b) * (1 + β * V b) := by
      have := ((hstoch s hs x).summable.add hπ1.summable).add
        (((hsPV x s hs).add hπV).mul_left β)
      exact this.congr fun b => by ring
    have hle : ∀ b, |J.Pmin s x b - π b| * (1 + β * V b) ≤ (J.Pmin s x b + π b) * (1 + β * V b) :=
      fun b => mul_le_mul_of_nonneg_right ((abs_sub _ _).trans (by
        rw [abs_of_nonneg (J.Pmin_nonneg s hs x b), abs_of_nonneg (hπ0 b)]))
        (by have := hV0 b; positivity)
    have hval : ∑' b, (J.Pmin s x b + π b) * (1 + β * V b) =
        2 + β * (∑' b, J.Pmin s x b * V b + M) := by
      rw [show (fun b => (J.Pmin s x b + π b) * (1 + β * V b)) =
        fun b => (J.Pmin s x b + π b) + β * (J.Pmin s x b * V b + π b * V b) from
        funext fun b => by ring, ((hstoch s hs x).summable.add hπ1.summable).tsum_add
        (((hsPV x s hs).add hπV).mul_left β), tsum_mul_left,
        (hstoch s hs x).summable.tsum_add hπ1.summable, (hsPV x s hs).tsum_add hπV,
        (hstoch s hs x).tsum_eq, hπ1.tsum_eq]
      ring
    have hPV : ∑' b, J.Pmin s x b * V b ≤ V x + K / c :=
      (hsPV x s hs).tsum_le_of_sum_le (hmomP x s hs)
    calc D x s ≤ ∑' b, (J.Pmin s x b + π b) * (1 + β * V b) :=
          Summable.tsum_le_tsum hle (Summable.of_nonneg_of_le
            (fun b => mul_nonneg (abs_nonneg _) (by have := hV0 b; positivity)) hle hs1) hs1
      _ = 2 + β * (∑' b, J.Pmin s x b * V b + M) := hval
      _ ≤ 2 + β * (V x + K / c) + β * M := by nlinarith
  refine ⟨π, hπ0, hπ1, hinv, β, hβ0, ρ, H.rate_nonneg, H.rate_lt_one,
    2 + β * (K / c + M) + β, fun x t ht => ?_⟩
  have hiter : ∀ (k : ℕ) (s : ℝ), 0 ≤ s → D x (s + k) ≤ ρ ^ k * D x s := by
    intro k
    induction k with
    | zero => intro s hs; simp
    | succ k ih =>
        intro s hs
        have h1 := hstep x (s + k) (by positivity)
        have h2 := ih s hs
        rw [show s + ((k + 1 : ℕ) : ℝ) = (s + k) + 1 by push_cast; ring, pow_succ]
        calc D x ((s + k) + 1) ≤ ρ * D x (s + k) := h1
          _ ≤ ρ * (ρ ^ k * D x s) := mul_le_mul_of_nonneg_left h2 H.rate_nonneg
          _ = ρ ^ k * ρ * D x s := by ring
  set n := ⌊t⌋₊ with hn
  have hsn : 0 ≤ t - n := by rw [hn]; linarith [Nat.floor_le ht]
  have h1 := hiter n (t - n) hsn
  rw [sub_add_cancel] at h1
  have h2 := hbound x (t - n) hsn
  have hρn : 0 ≤ ρ ^ n := pow_nonneg H.rate_nonneg n
  have h3 : 2 + β * (V x + K / c) + β * M ≤ (2 + β * (K / c + M) + β) * (1 + V x) := by
    have := hV0 x
    have := mul_nonneg hβ0.le (hV0 x)
    have : 0 ≤ β * (K / c + M) := mul_nonneg hβ0.le (add_nonneg (div_nonneg hK hc.le) hM0)
    nlinarith
  show D x t ≤ _
  calc D x t ≤ ρ ^ n * D x (t - n) := h1
    _ ≤ ρ ^ n * ((2 + β * (K / c + M) + β) * (1 + V x)) :=
        mul_le_mul_of_nonneg_left (h2.trans h3) hρn
    _ = _ := by ring

/-- **Geometric ergodicity under the drift `QV ≤ −cV + K 1_C`** with `C` finite (Meyn–Tweedie
condition (CD4) with a finite, hence petite, set). The drift on `C` is bounded, so this reduces to
the global form. -/
theorem geometric_ergodic_of_drift_on [Countable α] [Nonempty α] (V : α → ℝ) (hV0 : ∀ x, 0 ≤ V x)
    (hfinV : ∀ R : ℝ, {x | V x ≤ R}.Finite) {c K : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (C : Set α)
    (hdrift : ∀ x, J.drift V x ≤ -c * V x + K * C.indicator 1 x)
    (hstoch : ∀ t, 0 ≤ t → ∀ x, HasSum (fun b => J.Pmin t x b) 1)
    (hirr : ∀ a b, J.ReachPos a b) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * J.Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |J.Pmin t a b - π b| * (1 + β * V b) ≤ C₀ * (1 + V a) * ρ ^ ⌊t⌋₊ := by
  refine J.geometric_ergodic V hV0 hfinV hc hK (fun x => ?_) hstoch hirr
  have h := hdrift x
  have hi : C.indicator (1 : α → ℝ) x ≤ 1 := by
    by_cases hx : x ∈ C <;> simp [Set.indicator, hx]
  nlinarith

end JumpSystem

end CRNT
