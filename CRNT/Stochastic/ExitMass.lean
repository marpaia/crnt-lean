import CRNT.Stochastic.KurtzPathwise

open MeasureTheory Set Filter
open scoped BigOperators ENNReal

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

noncomputable def exitMass (K : Finset α) (c : α) (h : ℝ) : ℝ :=
  ∑' b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b)

theorem exitMass_nonneg (K : Finset α) (c : α) {h : ℝ} (ht : 0 ≤ h) :
    J.exitMass K c h ≥ 0 := by
  refine tsum_nonneg fun b => ?_
  by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b]

theorem exitMass_le_one (K : Finset α) (c : α) {h : ℝ} (ht : 0 ≤ h) :
    J.exitMass K c h ≤ 1 := by
  have hPs : Summable fun b => (J.stopOutside K).Pmin h c b :=
    ((J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x) (fun c' _ => J.stopOutside_q_le K c') ht).summable
  have hle : ∀ b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b) ≤ (J.stopOutside K).Pmin h c b := by
    intro b
    by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b]
  have hsum : Summable fun b => (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b) :=
    Summable.of_nonneg_of_le (fun b => by by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b]) hle hPs
  have htsum : ∑' b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b) ≤ ∑' b, (J.stopOutside K).Pmin h c b :=
    hsum.tsum_le_tsum hle hPs
  have hone : ∑' b, (J.stopOutside K).Pmin h c b = 1 :=
    ((J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x) (fun c' _ => J.stopOutside_q_le K c') ht).tsum_eq
  exact htsum.trans (le_of_eq hone)

theorem exitMass_zero_of_mem (K : Finset α) (c : α) (hc : c ∈ K) :
    J.exitMass K c 0 = 0 := by
  have hP0 : ∀ b, (J.stopOutside K).Pmin 0 c b = if c = b then 1 else 0 := fun b => (J.stopOutside K).Pmin_zero c b
  have heq : J.exitMass K c 0 = ∑' b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin 0 c b) := rfl
  rw [heq, funext hP0]
  have hzero : ∀ b, (if b ∈ K then (0 : ℝ) else if c = b then (1 : ℝ) else 0) = 0 := by
    intro b
    by_cases hb : b ∈ K
    · simp [hb]
    · by_cases hcb : c = b
      · subst hcb; exact (hb hc).elim
      · simp [hcb]
  rw [funext hzero, tsum_zero]

/-! ### The exit mass in `ℝ≥0∞`

The exit mass is the mass of the chain *frozen outside* `K` that lies outside `K`; the
following `ℝ≥0∞`-valued versions exist because Fubini for infinite sums is unconditional
there, which is what the semigroup law below needs. -/

/-- The indicator of `K`, as a `ℝ≥0∞`. -/
noncomputable def indicator (K : Finset α) (b : α) : ℝ≥0∞ :=
  if b ∈ K then 1 else 0

/-- The mass of the frozen chain that is still inside `K` at time `h`, in `ℝ≥0∞`. -/
noncomputable def insideMassENN (K : Finset α) (c : α) (h : ℝ) : ℝ≥0∞ :=
  ∑' b, indicator K b * ENNReal.ofReal ((J.stopOutside K).Pmin h c b)

/-- The mass of the frozen chain that is outside `K` at time `h`, in `ℝ≥0∞`. -/
noncomputable def outsideMassENN (K : Finset α) (c : α) (h : ℝ) : ℝ≥0∞ :=
  ∑' b, (1 - indicator K b) * ENNReal.ofReal ((J.stopOutside K).Pmin h c b)

theorem indicator_mem (K : Finset α) {b : α} (hb : b ∈ K) : indicator K b = 1 := by
  simp [indicator, hb]

theorem indicator_not_mem (K : Finset α) {b : α} (hb : b ∉ K) : indicator K b = 0 := by
  simp [indicator, hb]

/-- The inside and outside masses of the frozen chain add up to the total mass `1`. -/
theorem insideMassENN_add_outsideMassENN (K : Finset α) (c : α) {h : ℝ} (ht : 0 ≤ h) :
    J.insideMassENN K c h + J.outsideMassENN K c h = 1 := by
  have hsum : HasSum (fun b => (J.stopOutside K).Pmin h c b) 1 :=
    (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x)
      (fun c' _ => J.stopOutside_q_le K c') ht
  have hconv : (∑' b, ENNReal.ofReal ((J.stopOutside K).Pmin h c b)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun b => (J.stopOutside K).Pmin_nonneg h ht c b)
      hsum.summable, hsum.tsum_eq, ENNReal.ofReal_one]
  have hsplit : (∑' b, ENNReal.ofReal ((J.stopOutside K).Pmin h c b) *
      (indicator K b + (1 - indicator K b))) = 1 := by
    have hpoint : ∀ b, indicator K b + (1 - indicator K b) = 1 := by
      intro b
      by_cases hb : b ∈ K <;> simp [indicator, hb]
    simp_rw [hpoint]
    simpa using hconv
  calc J.insideMassENN K c h + J.outsideMassENN K c h
      = ∑' b, ENNReal.ofReal ((J.stopOutside K).Pmin h c b) *
          (indicator K b + (1 - indicator K b)) := by
        simp only [insideMassENN, outsideMassENN]
        rw [← ENNReal.tsum_add]
        have hdist : ∀ b : α, (indicator K b * ENNReal.ofReal ((J.stopOutside K).Pmin h c b) +
            (1 - indicator K b) * ENNReal.ofReal ((J.stopOutside K).Pmin h c b))
            = ENNReal.ofReal ((J.stopOutside K).Pmin h c b) * (indicator K b + (1 - indicator K b)) := by
          intro b
          rw [mul_comm (indicator K b) (ENNReal.ofReal ((J.stopOutside K).Pmin h c b)),
            mul_comm (1 - indicator K b) (ENNReal.ofReal ((J.stopOutside K).Pmin h c b)),
            ← mul_add]
        simp_rw [hdist]
    _ = 1 := hsplit

/-- **The exit-mass factorization (the union-bound mechanism), in `ℝ≥0∞`.** The mass of the
frozen chain that is outside `K` at time `h₁ + h₂` splits into the mass that was already
outside at time `h₁` and the mass that was still inside at `h₁` and left during the next
`h₂`.  Equivalently, the exit mass obeys the semigroup law with respect to the transition
function of the frozen chain. -/
theorem outsideMassENN_factor (K : Finset α) (c : α) {h₁ h₂ : ℝ} (ht₁ : 0 ≤ h₁) (ht₂ : 0 ≤ h₂) :
    J.outsideMassENN K c (h₁ + h₂)
      = ∑' c', ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') * J.outsideMassENN K c' h₂ := by
  have hCK : ∀ b, (J.stopOutside K).Pmin (h₁ + h₂) c b
      = ∑' c', (J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b :=
    fun b => (J.stopOutside K).Pmin_add ht₁ ht₂ c b
  have hnonneg : ∀ c' b, 0 ≤ (J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b :=
    fun c' b => mul_nonneg ((J.stopOutside K).Pmin_nonneg h₁ ht₁ c c')
      ((J.stopOutside K).Pmin_nonneg h₂ ht₂ c' b)
  have hsum_b : ∀ b, Summable
      (fun c' => (J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b) := by
    intro b
    refine Summable.of_nonneg_of_le (f := fun c' => (J.stopOutside K).Pmin h₁ c c')
      (fun c' => hnonneg c' b) (fun c' => ?_) ?_
    · simpa using mul_le_mul_of_nonneg_left ((J.stopOutside K).Pmin_le_one h₂ ht₂ c' b)
        ((J.stopOutside K).Pmin_nonneg h₁ ht₁ c c')
    · exact (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x)
        (fun c' _ => J.stopOutside_q_le K c') ht₁ |>.summable
  have hoftsum : ∀ b, ENNReal.ofReal ((J.stopOutside K).Pmin (h₁ + h₂) c b)
      = ∑' c', ENNReal.ofReal
          ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b) := by
    intro b
    rw [hCK, ENNReal.ofReal_tsum_of_nonneg (fun c' => hnonneg c' b) (hsum_b b)]
  have hcomm : (∑' b, ∑' c', (1 - indicator K b) *
        ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b))
      = ∑' c', ∑' b, (1 - indicator K b) *
        ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b) :=
    ENNReal.tsum_comm
  have hinner : ∀ c', (∑' b, (1 - indicator K b) *
        ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b))
      = ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') * J.outsideMassENN K c' h₂ := by
    intro c'
    have hmul : ∀ b, ENNReal.ofReal
          ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b)
        = ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c')
          * ENNReal.ofReal ((J.stopOutside K).Pmin h₂ c' b) := by
      intro b
      exact ENNReal.ofReal_mul ((J.stopOutside K).Pmin_nonneg h₁ ht₁ c c')
    simp only [hmul]
    calc (∑' b, (1 - indicator K b) *
          (ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c')
            * ENNReal.ofReal ((J.stopOutside K).Pmin h₂ c' b)))
        = ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') *
          ∑' b, (1 - indicator K b) * ENNReal.ofReal ((J.stopOutside K).Pmin h₂ c' b) := by
          rw [show (fun b => (1 - indicator K b) *
              (ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c')
                * ENNReal.ofReal ((J.stopOutside K).Pmin h₂ c' b)))
              = (fun b => ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') *
                  ((1 - indicator K b) * ENNReal.ofReal ((J.stopOutside K).Pmin h₂ c' b))) by
                funext b; ac_rfl]
          exact ENNReal.tsum_mul_left
    _ = ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') * J.outsideMassENN K c' h₂ := rfl
  calc J.outsideMassENN K c (h₁ + h₂)
      = ∑' b, (1 - indicator K b) * ENNReal.ofReal ((J.stopOutside K).Pmin (h₁ + h₂) c b) := rfl
    _ = ∑' b, (1 - indicator K b) *
        ∑' c', ENNReal.ofReal
          ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b) := by
        simp only [hoftsum]
    _ = ∑' b, ∑' c', (1 - indicator K b) *
        ENNReal.ofReal
          ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b) := by
        refine tsum_congr (fun b => ?_)
        rw [ENNReal.tsum_mul_left]
    _ = ∑' c', ∑' b, (1 - indicator K b) *
        ENNReal.ofReal
          ((J.stopOutside K).Pmin h₁ c c' * (J.stopOutside K).Pmin h₂ c' b) := hcomm
    _ = ∑' c', ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') * J.outsideMassENN K c' h₂ := by
        refine tsum_congr (fun c' => ?_)
        rw [hinner c']

/-- The `ℝ≥0∞` exit mass is the `ofReal` of the `ℝ` exit mass. -/
theorem outsideMassENN_eq_ofReal (K : Finset α) (c : α) {h : ℝ} (ht : 0 ≤ h) :
    J.outsideMassENN K c h = ENNReal.ofReal (J.exitMass K c h) := by
  have hsum : HasSum (fun b => (J.stopOutside K).Pmin h c b) 1 :=
    (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x)
      (fun c' _ => J.stopOutside_q_le K c') ht
  have hpoint : ∀ b, (1 - indicator K b) * ENNReal.ofReal ((J.stopOutside K).Pmin h c b)
      = ENNReal.ofReal (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pmin h c b) := by
    intro b
    by_cases hb : b ∈ K
    · simp [indicator, hb]
    · simp [indicator, hb]
  simp only [outsideMassENN]
  rw [funext hpoint]
  symm
  exact ENNReal.ofReal_tsum_of_nonneg
    (fun b => by by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b])
    (Summable.of_nonneg_of_le
      (fun b => by by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b])
      (fun b => by by_cases hb : b ∈ K <;> simp [hb, (J.stopOutside K).Pmin_nonneg h ht c b])
      hsum.summable)

/-- **The exit-mass factorization, in `ℝ`.** The mass of the frozen chain that is outside `K`
at time `h₁ + h₂` is the mass that is inside `K` at time `h₁` (weighted by the frozen
transition function) times the exit mass of the window of length `h₂`.  This is the
union-bound mechanism of the sample-path reading of Kurtz's law of large numbers: the
probability of leaving a set during a window is the exit mass of the chain started at the
state occupied at the beginning of that window. -/
theorem exitMass_factor (K : Finset α) (c : α) {h₁ h₂ : ℝ} (ht₁ : 0 ≤ h₁) (ht₂ : 0 ≤ h₂) :
    J.exitMass K c (h₁ + h₂)
      = ∑' c', (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂ := by
  have hENN : J.outsideMassENN K c (h₁ + h₂)
      = ∑' c', ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c') * J.outsideMassENN K c' h₂ :=
    J.outsideMassENN_factor K c ht₁ ht₂
  have hENN' : J.outsideMassENN K c (h₁ + h₂)
      = ∑' c', ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c')
          * ENNReal.ofReal (J.exitMass K c' h₂) := by
    rw [hENN]
    refine tsum_congr (fun c' => ?_)
    rw [J.outsideMassENN_eq_ofReal K c' ht₂]
  have hprod : ∀ c', ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c')
        * ENNReal.ofReal (J.exitMass K c' h₂)
      = ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂) := by
    intro c'
    exact (ENNReal.ofReal_mul (p := (J.stopOutside K).Pmin h₁ c c') (q := J.exitMass K c' h₂)
      ((J.stopOutside K).Pmin_nonneg h₁ ht₁ c c')).symm
  simp only [hprod] at hENN'
  have hsum : Summable
      (fun c' => (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂) := by
    refine Summable.of_nonneg_of_le (f := fun c' => (J.stopOutside K).Pmin h₁ c c')
      (fun c' => mul_nonneg ((J.stopOutside K).Pmin_nonneg h₁ ht₁ c c')
        (J.exitMass_nonneg K c' ht₂)) (fun c' => ?_) ?_
    · simpa using mul_le_mul_of_nonneg_left (J.exitMass_le_one K c' ht₂)
        ((J.stopOutside K).Pmin_nonneg h₁ ht₁ c c')
    · exact (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x)
        (fun c' _ => J.stopOutside_q_le K c') ht₁ |>.summable
  have hnonneg : ∀ c', 0 ≤ (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂ :=
    fun c' => mul_nonneg ((J.stopOutside K).Pmin_nonneg h₁ ht₁ c c')
      (J.exitMass_nonneg K c' ht₂)
  have htoReal : ENNReal.toReal (∑' c', ENNReal.ofReal
      ((J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂))
      = ∑' c', (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg hsum]
    exact ENNReal.toReal_ofReal (tsum_nonneg fun c' => hnonneg c')
  have hLHS : ENNReal.ofReal (J.exitMass K c (h₁ + h₂)) = J.outsideMassENN K c (h₁ + h₂) :=
    (J.outsideMassENN_eq_ofReal K c (add_nonneg ht₁ ht₂)).symm
  have hRHS : ENNReal.ofReal (∑' c', (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂)
      = ∑' c', ENNReal.ofReal ((J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂) :=
    ENNReal.ofReal_tsum_of_nonneg hnonneg hsum
  have : ENNReal.ofReal (J.exitMass K c (h₁ + h₂))
      = ENNReal.ofReal (∑' c', (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂) := by
    rw [hLHS, hENN', hRHS]
  have h' : ENNReal.toReal (ENNReal.ofReal (J.exitMass K c (h₁ + h₂)))
      = ENNReal.toReal (ENNReal.ofReal (∑' c',
        (J.stopOutside K).Pmin h₁ c c' * J.exitMass K c' h₂)) := congrArg ENNReal.toReal this
  rw [ENNReal.toReal_ofReal (J.exitMass_nonneg K c (add_nonneg ht₁ ht₂)),
    ENNReal.toReal_ofReal (tsum_nonneg fun c' => hnonneg c')] at h'
  exact h'

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

theorem three_halves_step (δ : ℝ) (hδ : 0 ≤ δ) {ι : Type*} [Fintype ι]
    (u v : ι → ℝ) (hu : ∑ i, u i ^ 2 ≤ δ ^ 2)
    (hv : ∑ i, v i ^ 2 ≤ δ ^ 2 / 4) :
    ∑ i, (u i + v i) ^ 2 ≤ (3 * δ / 2) ^ 2 := by
  have hcross : ∑ i, u i * v i ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) :=
    Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset ι) u v
  have hsqrtu : Real.sqrt (∑ i, u i ^ 2) ≤ δ := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hδ
    · nlinarith [hu]
  have hsqrtv : Real.sqrt (∑ i, v i ^ 2) ≤ δ / 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith [hδ]
    · nlinarith [hv, hδ]
  have heq : ∑ i, (u i + v i) ^ 2 = ∑ i, u i ^ 2 + 2 * ∑ i, u i * v i + ∑ i, v i ^ 2 := by
    calc ∑ i, (u i + v i) ^ 2
        = ∑ i, (u i ^ 2 + 2 * (u i * v i) + v i ^ 2) := by refine Finset.sum_congr rfl fun i _ => by ring
      _ = ∑ i, u i ^ 2 + 2 * ∑ i, u i * v i + ∑ i, v i ^ 2 := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hle : ∑ i, u i ^ 2 + 2 * ∑ i, u i * v i + ∑ i, v i ^ 2 ≤ δ ^ 2 + δ ^ 2 + δ ^ 2 / 4 := by
    nlinarith [hu, hv, hcross, hsqrtu, hsqrtv, mul_le_mul hsqrtu hsqrtv (Real.sqrt_nonneg (∑ i, v i ^ 2)) (le_trans (Real.sqrt_nonneg (∑ i, u i ^ 2)) hsqrtu)]
  rw [heq]
  exact hle.trans (le_of_eq (by ring))

end Network

end CRNT
