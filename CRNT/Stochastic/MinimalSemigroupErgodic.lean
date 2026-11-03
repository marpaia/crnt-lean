import CRNT.Stochastic.MinimalSemigroupChapmanKolmogorov

/-!
# Exponential ergodicity of the minimal transition function on a finite closed class

Let `K` be a finite set of states that is closed (positive-rate jumps from `K` stay in `K`,
`ClosedOn`) and irreducible (every state of `K` reaches every other through positive-rate jumps).
Then:

* rows starting in `K` are stochastic and supported on `K` (`sum_Pmin_closedOn`,
  `Pmin_eq_zero_of_closedOn`);
* `P(t)(a, b) > 0` for `t > 0`, `a, b ∈ K` (`Pmin_pos_of_reachPos`);
* there are `ρ < 1` and `π` with `|P(t)(a, b) − π(b)| ≤ ρⁿ` for all `a, b ∈ K` and `t ≥ n`
  (`exists_geometric_ergodic`). `π` is a probability on `K`, invariant, and the only invariant
  law on `K` (`ergodic_limit_sum_eq_one`, `ergodic_limit_invariant`, `invariant_eq_ergodic_limit`).

Proof (Doeblin): `δ = min_{a,b ∈ K} P(1)(a, b) > 0`; by Chapman–Kolmogorov
`P(1 + t)(a, b) = ∑_{c ∈ K} P(1)(a, c) P(t)(c, b)`, which contracts the oscillation of the
column `P(t)(·, b)` over `K` by the factor `1 − |K| δ` (`doeblin_sub_le`); the maximum of the
column is nonincreasing and the minimum nondecreasing in `t`.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- Positive-rate jumps from `K` stay in `K`. -/
def ClosedOn (K : Finset α) : Prop := ∀ a ∈ K, ∀ i, 0 < J.rate i a → J.next i a ∈ K

variable {J}

omit [DecidableEq α] in
theorem mem_of_reachPos {K : Finset α} (hK : J.ClosedOn K) {a c : α} (ha : a ∈ K)
    (h : J.ReachPos a c) : c ∈ K := by
  induction h with
  | refl => exact ha
  | tail _ hcd ih =>
      obtain ⟨i, hr, rfl⟩ := hcd
      exact hK _ ih i hr

theorem P_eq_zero_of_closedOn {K : Finset α} (hK : J.ClosedOn K) (k : ℕ) :
    ∀ t a, a ∈ K → ∀ c, c ∉ K → J.P k t a c = 0 := by
  induction k with
  | zero =>
      intro t a ha c hc
      have : a ≠ c := fun h => hc (h ▸ ha)
      simp [P_zero, this]
  | succ k ih =>
      intro t a ha c hc
      have hac : a ≠ c := fun h => hc (h ▸ ha)
      rw [P_succ]
      have h0 : ∀ s, Real.exp (-(J.q a * s)) * ∑ i, J.rate i a * J.P k (t - s) (J.next i a) c
          = 0 := by
        intro s
        rw [Finset.sum_eq_zero fun i _ => ?_, mul_zero]
        rcases (J.rate_nonneg i a).lt_or_eq with hr | hr
        · rw [ih _ _ (hK a ha i hr) c hc, mul_zero]
        · rw [← hr, zero_mul]
      simp [h0, hac]

theorem Pmin_eq_zero_of_closedOn {K : Finset α} (hK : J.ClosedOn K) (t : ℝ) {a : α}
    (ha : a ∈ K) {c : α} (hc : c ∉ K) : J.Pmin t a c = 0 := by
  simp [Pmin, P_eq_zero_of_closedOn hK _ t a ha c hc]

/-- Rows starting in a finite closed class are stochastic on the class. -/
theorem sum_Pmin_closedOn {K : Finset α} (hK : J.ClosedOn K) {t : ℝ} (ht : 0 ≤ t) {a : α}
    (ha : a ∈ K) : ∑ b ∈ K, J.Pmin t a b = 1 := by
  have h := J.hasSum_Pmin_one (Λ := ∑ c ∈ K, J.q c) (a := a)
    (fun c hc => Finset.single_le_sum (f := J.q) (fun c _ => J.q_nonneg c)
      (mem_of_reachPos hK ha hc)) ht
  have h2 : HasSum (fun b => J.Pmin t a b) (∑ b ∈ K, J.Pmin t a b) :=
    hasSum_sum_of_ne_finset_zero fun b hb => Pmin_eq_zero_of_closedOn hK t ha hb
  exact h2.unique h

/-- Chapman–Kolmogorov inside a closed class, as a finite sum. -/
theorem Pmin_add_closedOn {K : Finset α} (hK : J.ClosedOn K) {s t : ℝ} (hs : 0 ≤ s)
    (ht : 0 ≤ t) {a : α} (ha : a ∈ K) (b : α) :
    J.Pmin (s + t) a b = ∑ c ∈ K, J.Pmin s a c * J.Pmin t c b := by
  have h := J.hasSum_Pmin_add hs ht a b
  have h2 : HasSum (fun c => J.Pmin s a c * J.Pmin t c b) (∑ c ∈ K, J.Pmin s a c * J.Pmin t c b) :=
    hasSum_sum_of_ne_finset_zero fun c hc => by rw [Pmin_eq_zero_of_closedOn hK s ha hc, zero_mul]
  exact h.unique h2

variable (J)

theorem P_le_Pmin (k : ℕ) {t : ℝ} (ht : 0 ≤ t) (a b : α) : J.P k t a b ≤ J.Pmin t a b :=
  (monotone_nat_of_le_succ fun j => J.P_mono j t ht a b).ge_of_tendsto (J.tendsto_P t ht a b) k

theorem Pmin_self_pos {t : ℝ} (ht : 0 ≤ t) (a : α) : 0 < J.Pmin t a a :=
  lt_of_lt_of_le (by simp [P_zero, Real.exp_pos]) (J.P_le_Pmin 0 ht a a)

/-- One positive-rate jump has positive probability at every positive time. -/
theorem P_one_pos {c : α} {i : J.ι} (hr : 0 < J.rate i c) {t : ℝ} (ht : 0 < t) :
    0 < J.P 1 t c (J.next i c) := by
  rw [P_succ]
  have hint : 0 < ∫ s in (0 : ℝ)..t, Real.exp (-(J.q c * s)) *
      ∑ j, J.rate j c * J.P 0 (t - s) (J.next j c) (J.next i c) := by
    refine intervalIntegral.intervalIntegral_pos_of_pos_on (J.integrable_term 0 t c _)
      (fun s hs => ?_) ht
    refine mul_pos (Real.exp_pos _) ?_
    have hle : J.rate i c * J.P 0 (t - s) (J.next i c) (J.next i c) ≤
        ∑ j, J.rate j c * J.P 0 (t - s) (J.next j c) (J.next i c) :=
      Finset.single_le_sum (f := fun j => J.rate j c * J.P 0 (t - s) (J.next j c) (J.next i c))
        (fun j _ => mul_nonneg (J.rate_nonneg j c) (J.P_nonneg 0 _ (by linarith [hs.2]) _ _))
        (Finset.mem_univ i)
    have hp : 0 < J.P 0 (t - s) (J.next i c) (J.next i c) := by simp [P_zero, Real.exp_pos]
    exact lt_of_lt_of_le (mul_pos hr hp) hle
  have h0 : 0 ≤ Real.exp (-(J.q c * t)) * (if c = J.next i c then 1 else 0) := by
    split_ifs <;> positivity
  linarith

/-- **Positivity along reachability.** -/
theorem Pmin_pos_of_reachPos {a b : α} (h : J.ReachPos a b) : ∀ {t : ℝ}, 0 < t →
    0 < J.Pmin t a b := by
  induction h with
  | refl => intro t ht; exact J.Pmin_self_pos ht.le a
  | @tail c d _ hcd ih =>
      obtain ⟨i, hr, rfl⟩ := hcd
      intro t ht
      have h2 : 0 < t / 2 := by linarith
      have hck := J.hasSum_Pmin_add h2.le h2.le a (J.next i c)
      have hle := le_hasSum hck c fun x _ =>
        mul_nonneg (J.Pmin_nonneg _ h2.le a x) (J.Pmin_nonneg _ h2.le x _)
      rw [add_halves] at hle
      exact lt_of_lt_of_le (mul_pos (ih h2)
        (lt_of_lt_of_le (J.P_one_pos hr h2) (J.P_le_Pmin 1 h2.le _ _))) hle

omit [DecidableEq α] in
/-- **Doeblin's contraction.** Rows `a, a'` summing to one on `K` with entries at least `δ`
move a vector with values in `[m, M]` on `K` by at most `(1 − |K| δ)(M − m)`. -/
theorem doeblin_sub_le {K : Finset α} {A : α → α → ℝ} {x : α → ℝ} {δ m M : ℝ} {a a' : α}
    (hA : ∀ c ∈ K, δ ≤ A a c) (hA' : ∀ c ∈ K, δ ≤ A a' c)
    (hs : ∑ c ∈ K, A a c = 1) (hs' : ∑ c ∈ K, A a' c = 1)
    (hx : ∀ c ∈ K, m ≤ x c ∧ x c ≤ M) :
    ∑ c ∈ K, A a c * x c - ∑ c ∈ K, A a' c * x c ≤ (1 - K.card * δ) * (M - m) := by
  have h1 : ∑ c ∈ K, A a c * x c ≤ ∑ c ∈ K, ((A a c - δ) * M + δ * x c) :=
    Finset.sum_le_sum fun c hc => by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hA c hc)) (sub_nonneg.mpr (hx c hc).2)]
  have h2 : ∑ c ∈ K, ((A a' c - δ) * m + δ * x c) ≤ ∑ c ∈ K, A a' c * x c :=
    Finset.sum_le_sum fun c hc => by
      nlinarith [mul_nonneg (sub_nonneg.mpr (hA' c hc)) (sub_nonneg.mpr (hx c hc).1)]
  have e1 : ∑ c ∈ K, ((A a c - δ) * M + δ * x c) =
      (1 - K.card * δ) * M + δ * ∑ c ∈ K, x c := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hs, ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
  have e2 : ∑ c ∈ K, ((A a' c - δ) * m + δ * x c) =
      (1 - K.card * δ) * m + δ * ∑ c ∈ K, x c := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib, hs', ← Finset.mul_sum]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [e1] at h1
  rw [e2] at h2
  nlinarith

/-- **Exponential ergodicity on a finite closed irreducible class.** There are `ρ < 1` and a
law `π` with `|P(t)(a, b) − π(b)| ≤ ρⁿ` for all `a, b ∈ K` and all `t ≥ n`. -/
theorem exists_geometric_ergodic {K : Finset α} (hK : J.ClosedOn K) (hne : K.Nonempty)
    (hirr : ∀ a ∈ K, ∀ b ∈ K, J.ReachPos a b) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ π : α → ℝ, ∀ a ∈ K, ∀ b ∈ K, ∀ (n : ℕ) (t : ℝ),
      (n : ℝ) ≤ t → |J.Pmin t a b - π b| ≤ ρ ^ n := by
  have hKK : (K ×ˢ K).Nonempty := hne.product hne
  set δ := (K ×ˢ K).inf' hKK (fun p => J.Pmin 1 p.1 p.2) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef, Finset.lt_inf'_iff]
    rintro ⟨a, b⟩ hp
    rw [Finset.mem_product] at hp
    exact J.Pmin_pos_of_reachPos (hirr a hp.1 b hp.2) one_pos
  have hδle : ∀ a ∈ K, ∀ c ∈ K, δ ≤ J.Pmin 1 a c := fun a ha c hc => by
    rw [hδdef]
    exact Finset.inf'_le (fun p : α × α => J.Pmin 1 p.1 p.2) (Finset.mk_mem_product ha hc)
  obtain ⟨a₀, ha₀⟩ := hne
  have hcardδ : (K.card : ℝ) * δ ≤ 1 := by
    calc (K.card : ℝ) * δ = ∑ c ∈ K, δ := by simp
      _ ≤ ∑ c ∈ K, J.Pmin 1 a₀ c := Finset.sum_le_sum fun c hc => hδle a₀ ha₀ c hc
      _ = 1 := sum_Pmin_closedOn hK zero_le_one ha₀
  have hcard_pos : (0 : ℝ) < K.card := by exact_mod_cast Finset.card_pos.mpr ⟨a₀, ha₀⟩
  refine ⟨1 - K.card * δ, by linarith, by nlinarith [mul_pos hcard_pos hδpos], ?_⟩
  set ρ := 1 - (K.card : ℝ) * δ with hρdef
  have hρ0 : 0 ≤ ρ := by linarith
  -- column maximum and minimum over `K`
  let Mx : α → ℝ → ℝ := fun b t => K.sup' ⟨a₀, ha₀⟩ fun a => J.Pmin t a b
  let mn : α → ℝ → ℝ := fun b t => K.inf' ⟨a₀, ha₀⟩ fun a => J.Pmin t a b
  have hF1 : ∀ b t a, a ∈ K → mn b t ≤ J.Pmin t a b ∧ J.Pmin t a b ≤ Mx b t := fun b t a ha =>
    ⟨Finset.inf'_le (fun a => J.Pmin t a b) ha, Finset.le_sup' (fun a => J.Pmin t a b) ha⟩
  have hF2 : ∀ b s t, 0 ≤ s → 0 ≤ t → Mx b (s + t) ≤ Mx b t ∧ mn b t ≤ mn b (s + t) := by
    intro b s t hs ht
    constructor
    · refine Finset.sup'_le _ _ fun a ha => ?_
      rw [Pmin_add_closedOn hK hs ht ha]
      calc ∑ c ∈ K, J.Pmin s a c * J.Pmin t c b ≤ ∑ c ∈ K, J.Pmin s a c * Mx b t :=
            Finset.sum_le_sum fun c hc =>
              mul_le_mul_of_nonneg_left (hF1 b t c hc).2 (J.Pmin_nonneg s hs a c)
        _ = Mx b t := by rw [← Finset.sum_mul, sum_Pmin_closedOn hK hs ha, one_mul]
    · refine Finset.le_inf' _ _ fun a ha => ?_
      rw [Pmin_add_closedOn hK hs ht ha]
      calc mn b t = ∑ c ∈ K, J.Pmin s a c * mn b t := by
            rw [← Finset.sum_mul, sum_Pmin_closedOn hK hs ha, one_mul]
        _ ≤ ∑ c ∈ K, J.Pmin s a c * J.Pmin t c b :=
            Finset.sum_le_sum fun c hc =>
              mul_le_mul_of_nonneg_left (hF1 b t c hc).1 (J.Pmin_nonneg s hs a c)
  have hF3 : ∀ b t, 0 ≤ t → Mx b (1 + t) - mn b (1 + t) ≤ ρ * (Mx b t - mn b t) := by
    intro b t ht
    obtain ⟨a1, ha1, h1⟩ := Finset.exists_mem_eq_sup' ⟨a₀, ha₀⟩ fun a => J.Pmin (1 + t) a b
    obtain ⟨a2, ha2, h2⟩ := Finset.exists_mem_eq_inf' ⟨a₀, ha₀⟩ fun a => J.Pmin (1 + t) a b
    show K.sup' _ _ - K.inf' _ _ ≤ _
    rw [h1, h2, Pmin_add_closedOn hK zero_le_one ht ha1,
      Pmin_add_closedOn hK zero_le_one ht ha2]
    exact doeblin_sub_le (hδle a1 ha1) (hδle a2 ha2) (sum_Pmin_closedOn hK zero_le_one ha1)
      (sum_Pmin_closedOn hK zero_le_one ha2) fun c hc => hF1 b t c hc
  have hosc1 : ∀ b t, 0 ≤ t → Mx b t - mn b t ≤ 1 := by
    intro b t ht
    have h1 := (hF1 b t a₀ ha₀).1
    have h2 : Mx b t ≤ 1 := Finset.sup'_le _ _ fun a _ => J.Pmin_le_one t ht a b
    have h3 : 0 ≤ mn b t := Finset.le_inf' _ _ fun a _ => J.Pmin_nonneg t ht a b
    linarith
  have hF4 : ∀ b (n : ℕ), Mx b n - mn b n ≤ ρ ^ n := by
    intro b n
    induction n with
    | zero => simpa using hosc1 b 0 le_rfl
    | succ n ih =>
        have h := hF3 b n (Nat.cast_nonneg n)
        rw [show ((n + 1 : ℕ) : ℝ) = 1 + n by push_cast; ring, pow_succ]
        nlinarith
  have hF5 : ∀ b (n : ℕ) (t : ℝ), (n : ℝ) ≤ t → Mx b t ≤ Mx b n ∧ mn b n ≤ mn b t := by
    intro b n t hnt
    have := hF2 b (t - n) n (by linarith) (Nat.cast_nonneg n)
    rwa [sub_add_cancel] at this
  refine ⟨fun b => ⨅ k : ℕ, Mx b k, fun a ha b hb n t hnt => ?_⟩
  have hbdd : BddBelow (Set.range fun k : ℕ => Mx b k) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨k, rfl⟩
    exact (J.Pmin_nonneg _ (Nat.cast_nonneg k) a₀ b).trans (hF1 b k a₀ ha₀).2
  have hπle : (⨅ k : ℕ, Mx b k) ≤ Mx b n := ciInf_le hbdd n
  have hπge : mn b n ≤ ⨅ k : ℕ, Mx b k := by
    refine le_ciInf fun k => ?_
    have h1 := (hF5 b n (max n k) (by exact_mod_cast le_max_left n k)).2
    have h2 := (hF5 b k (max n k) (by exact_mod_cast le_max_right n k)).1
    have h3 := hF1 b (max n k : ℕ) a₀ ha₀
    push_cast at h1 h2 h3
    linarith [h3.1, h3.2]
  have hP := hF1 b t a ha
  have h5 := hF5 b n t hnt
  have h4 := hF4 b n
  rw [abs_sub_le_iff]
  constructor <;> linarith [hP.1, hP.2, h5.1, h5.2]

omit [DecidableEq α] in
theorem tendsto_of_geometric {f : ℝ → ℝ} {p ρ : ℝ} (hρ1 : ρ < 1)
    (h : ∀ (n : ℕ) (t : ℝ), (n : ℝ) ≤ t → |f t - p| ≤ ρ ^ n) : Tendsto f atTop (𝓝 p) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hρ1
  exact ⟨n, fun t ht => by rw [Real.dist_eq]; exact lt_of_le_of_lt (h n t ht) hn⟩

/-- **Ergodic theorem on a finite closed irreducible class.** The rows converge to a common
law `π` on `K`; `π` is a probability on `K`, invariant, and the only invariant probability
on `K`. -/
theorem exists_ergodic_limit {K : Finset α} (hK : J.ClosedOn K) (hne : K.Nonempty)
    (hirr : ∀ a ∈ K, ∀ b ∈ K, J.ReachPos a b) :
    ∃ π : α → ℝ, (∀ a ∈ K, ∀ b ∈ K, Tendsto (fun t => J.Pmin t a b) atTop (𝓝 (π b))) ∧
      ∑ b ∈ K, π b = 1 ∧
      (∀ t, 0 ≤ t → ∀ b ∈ K, ∑ a ∈ K, π a * J.Pmin t a b = π b) ∧
      ∀ μ : α → ℝ, ∑ a ∈ K, μ a = 1 →
        (∀ t, 0 ≤ t → ∀ b ∈ K, ∑ a ∈ K, μ a * J.Pmin t a b = μ b) → ∀ b ∈ K, μ b = π b := by
  obtain ⟨ρ, -, hρ1, π, hπ⟩ := J.exists_geometric_ergodic hK hne hirr
  have hlim : ∀ a ∈ K, ∀ b ∈ K, Tendsto (fun t => J.Pmin t a b) atTop (𝓝 (π b)) :=
    fun a ha b hb => tendsto_of_geometric hρ1 (hπ a ha b hb)
  obtain ⟨a₀, ha₀⟩ := hne
  refine ⟨π, hlim, ?_, ?_, ?_⟩
  · have h1 : Tendsto (fun t => ∑ b ∈ K, J.Pmin t a₀ b) atTop (𝓝 (∑ b ∈ K, π b)) :=
      tendsto_finsetSum _ fun b hb => hlim a₀ ha₀ b hb
    have h2 : Tendsto (fun t => ∑ b ∈ K, J.Pmin t a₀ b) atTop (𝓝 1) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 0] with t ht
        exact (sum_Pmin_closedOn hK ht ha₀).symm)
    exact tendsto_nhds_unique h1 h2
  · intro t ht b hb
    have h1 : Tendsto (fun s => J.Pmin (s + t) a₀ b) atTop (𝓝 (π b)) :=
      (hlim a₀ ha₀ b hb).comp (tendsto_atTop_add_const_right _ t tendsto_id)
    have h2 : Tendsto (fun s => ∑ c ∈ K, J.Pmin s a₀ c * J.Pmin t c b) atTop
        (𝓝 (∑ c ∈ K, π c * J.Pmin t c b)) :=
      tendsto_finsetSum _ fun c hc => (hlim a₀ ha₀ c hc).mul_const _
    have h3 : Tendsto (fun s => J.Pmin (s + t) a₀ b) atTop (𝓝 (∑ c ∈ K, π c * J.Pmin t c b)) :=
      h2.congr' (by
        filter_upwards [eventually_ge_atTop 0] with s hs
        exact (Pmin_add_closedOn hK hs ht ha₀ b).symm)
    exact tendsto_nhds_unique h3 h1
  · intro μ hμ hinv b hb
    have h1 : Tendsto (fun t => ∑ a ∈ K, μ a * J.Pmin t a b) atTop (𝓝 (∑ a ∈ K, μ a * π b)) :=
      tendsto_finsetSum _ fun a ha => (hlim a ha b hb).const_mul _
    rw [← Finset.sum_mul, hμ, one_mul] at h1
    have h2 : Tendsto (fun t => ∑ a ∈ K, μ a * J.Pmin t a b) atTop (𝓝 (μ b)) :=
      tendsto_const_nhds.congr' (by
        filter_upwards [eventually_ge_atTop 0] with t ht
        exact (hinv t ht b hb).symm)
    exact tendsto_nhds_unique h2 h1

end JumpSystem

end CRNT
