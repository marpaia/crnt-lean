import CRNT.Stochastic.MinimalSemigroupKrylovBogoliubov

/-!
# Countable-state Foster criteria under explicit drift hypotheses

Finite-sublevel Lyapunov functions and supplied negative drift bounds yield the
stated hitting-time and recurrence conclusions. Constructing these data is a
separate task. Universal stochastic recurrence/non-explosion from several-species
strong endotacticity is false; restricted count-tier and Lyapunov classes are
handled elsewhere.
-/

open MeasureTheory intervalIntegral Set Filter
open scoped BigOperators Topology

namespace CRNT

/-- A **countable-state Foster--Lyapunov drift certificate**: a Lyapunov function `V` with
nonnegative values and finite sublevel sets, and a *constant* negative drift `-c` (`c > 0`)
outside a finite set `C`.  This is the drift condition of Anderson--Cappelletti–Kim–Nguyen
and of Meyn–Tweedie (Theorem 11.3.4) for continuous time.

The drift condition is stated per jump: at every state outside the exceptional set, *every*
enabled jump lowers the Lyapunov function by at least `c`. -/
structure CountableFosterDrift (α : Type*) [Countable α] (J : JumpSystem α) where
  /-- The Lyapunov function. -/
  V : α → ℝ
  /-- Nonnegativity. -/
  hV : ∀ a, 0 ≤ V a
  /-- Finite sublevel sets. -/
  hfin : ∀ R : ℝ, {a | V a ≤ R}.Finite
  /-- The drift rate. -/
  c : ℝ
  /-- Positivity of the drift rate. -/
  hc : 0 < c
  /-- The exceptional set. -/
  C : Set α
  /-- Finiteness of the exceptional set. -/
  hC : C.Finite
  /-- The drift inequality: every enabled jump lowers `V` by at least `c`. -/
  hdrift : ∀ a, a ∉ C → ∀ i, 0 < J.rate i a →
      V (J.next i a) - V a ≤ -c

namespace CountableFosterDrift

variable {α : Type*} [Countable α] {J : JumpSystem α}

/-- The aggregate drift bound implied by the certificate: the drift of the generator is at most
`-c` times the total exit rate.  This is the Anderson--Cappelletti--Kim–Nguyen drift condition
`Q V ≤ −c` in the rate-normalized form. -/
theorem drift_le_mul_q (D : CountableFosterDrift α J) {a : α} (ha : a ∉ D.C) :
    J.drift D.V a ≤ -D.c * J.q a := by
  have hsum : (∑ i, J.rate i a * (D.V (J.next i a) - D.V a))
      ≤ ∑ i, (-D.c * J.rate i a) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hzero : J.rate i a = 0
    · simp [hzero]
    · have hpos : 0 < J.rate i a := lt_of_le_of_ne (J.rate_nonneg i a) (Ne.symm hzero)
      have hd := D.hdrift a ha i hpos
      calc J.rate i a * (D.V (J.next i a) - D.V a)
          ≤ J.rate i a * (-D.c) := mul_le_mul_of_nonneg_left hd (J.rate_nonneg i a)
        _ = -D.c * J.rate i a := by ring
  calc J.drift D.V a = ∑ i, J.rate i a * (D.V (J.next i a) - D.V a) := rfl
    _ ≤ ∑ i, (-D.c * J.rate i a) := hsum
    _ = (-D.c) * ∑ i, J.rate i a := by rw [Finset.mul_sum]
    _ = -D.c * J.q a := by rfl

/-- The **constant (generator-level) drift** implied by the certificate, when the total exit rate
is at least `1` outside the exceptional set: `Q V (a) ≤ −c` for `a ∉ C`. -/
theorem drift_le (D : CountableFosterDrift α J) (hq : ∀ a, a ∉ D.C → 1 ≤ J.q a) {a : α} (ha : a ∉ D.C) :
    J.drift D.V a ≤ -D.c := by
  have h1 := D.drift_le_mul_q ha
  have h2 := hq a ha
  have h3 : 0 ≤ D.c * (J.q a - 1) := mul_nonneg D.hc.le (by linarith)
  linarith

/-- The drift of the **squared** Lyapunov function: it is at most `-c V q`, i.e. it is
proportional to the Lyapunov function itself.  This is the step that turns a constant drift into a
multiplicative one. -/
theorem drift_sq_le_mul_q (D : CountableFosterDrift α J) {a : α} (ha : a ∉ D.C) :
    J.drift (fun x => D.V x ^ 2) a ≤ -D.c * D.V a * J.q a := by
  have hsum : (∑ i, J.rate i a * ((D.V (J.next i a)) ^ 2 - (D.V a) ^ 2))
      ≤ ∑ i, (-D.c * D.V a * J.rate i a) := by
    refine Finset.sum_le_sum fun i _ => ?_
    by_cases hzero : J.rate i a = 0
    · simp [hzero]
    · have hpos : 0 < J.rate i a := lt_of_le_of_ne (J.rate_nonneg i a) (Ne.symm hzero)
      have hd := D.hdrift a ha i hpos
      have hxy : 0 ≤ D.V (J.next i a) + D.V a := add_nonneg (D.hV _) (D.hV a)
      have h1 : J.rate i a * (D.V (J.next i a) - D.V a) * (D.V (J.next i a) + D.V a)
          ≤ J.rate i a * (-D.c) * (D.V (J.next i a) + D.V a) := by
        calc J.rate i a * (D.V (J.next i a) - D.V a) * (D.V (J.next i a) + D.V a)
            = (D.V (J.next i a) - D.V a) * (J.rate i a * (D.V (J.next i a) + D.V a)) := by ring
          _ ≤ (-D.c) * (J.rate i a * (D.V (J.next i a) + D.V a)) :=
              mul_le_mul_of_nonneg_right hd (mul_nonneg (J.rate_nonneg i a) hxy)
          _ = J.rate i a * (-D.c) * (D.V (J.next i a) + D.V a) := by ring
      have h2 : J.rate i a * (-D.c) * (D.V (J.next i a) + D.V a)
          ≤ J.rate i a * (-D.c) * D.V a := by
        have hneg : J.rate i a * (-D.c) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (J.rate_nonneg i a) (neg_nonpos.mpr D.hc.le)
        have hxy' : D.V a ≤ D.V (J.next i a) + D.V a := by
          linarith [D.hV (J.next i a)]
        calc J.rate i a * (-D.c) * (D.V (J.next i a) + D.V a)
            = (D.V (J.next i a) + D.V a) * (J.rate i a * (-D.c)) := by ring
          _ ≤ D.V a * (J.rate i a * (-D.c)) := mul_le_mul_of_nonpos_right hxy' hneg
          _ = J.rate i a * (-D.c) * D.V a := by ring
      calc J.rate i a * ((D.V (J.next i a)) ^ 2 - (D.V a) ^ 2)
          = J.rate i a * (D.V (J.next i a) - D.V a) * (D.V (J.next i a) + D.V a) := by ring
        _ ≤ J.rate i a * (-D.c) * (D.V (J.next i a) + D.V a) := h1
        _ ≤ J.rate i a * (-D.c) * D.V a := h2
        _ = -D.c * D.V a * J.rate i a := by ring
  calc J.drift (fun x => D.V x ^ 2) a
      = ∑ i, J.rate i a * ((D.V (J.next i a)) ^ 2 - (D.V a) ^ 2) := rfl
    _ ≤ ∑ i, (-D.c * D.V a * J.rate i a) := hsum
    _ = (-D.c * D.V a) * ∑ i, J.rate i a := by rw [Finset.mul_sum]
    _ = -D.c * D.V a * J.q a := by rfl

/-- The drift of the **squared** Lyapunov function under the constant drift hypothesis:
`Q V² (a) ≤ −c V (a)` for `a ∉ C`, a *multiplicative* Foster drift for the squared Lyapunov
function. -/
theorem drift_sq_le (D : CountableFosterDrift α J) (hq : ∀ a, a ∉ D.C → 1 ≤ J.q a) {a : α} (ha : a ∉ D.C) :
    J.drift (fun x => D.V x ^ 2) a ≤ -D.c * D.V a := by
  have h1 := D.drift_sq_le_mul_q ha
  have h2 := hq a ha
  have h3 : 0 ≤ D.c * D.V a * (J.q a - 1) :=
    mul_nonneg (mul_nonneg D.hc.le (D.hV a)) (by linarith)
  linarith

/-- **The reachable class of a drift certificate is finite.**  Under the certificate of
`CRNT.CountableFosterDrift` the set of states reachable from a given state is finite: outside the
finite exceptional set the Lyapunov function decreases strictly at every jump, and the exceptional
set has only finitely many jump targets.  Consequently the positive-recurrence theorem
`CRNT.foster_lyapunov_ergodic_of_constant_drift` is non-vacuous for *finite* classes only: the
per-jump constant drift is strictly stronger than the Anderson--Cappelletti--Kim--Nguyen condition
`Q V ≤ −c`, which allows an infinite irreducible class. -/
theorem reachable_finite (D : CountableFosterDrift α J) [DecidableEq α] (a : α) :
    {b | J.ReachPos a b}.Finite := by
  classical
  set C' : Finset α :=
    D.hC.toFinset.biUnion fun c => (Finset.univ : Finset J.ι).image fun i => J.next i c with hC'def
  set M : ℝ := D.V a + ∑ x ∈ C', |D.V x| with hMdef
  have hmem : ∀ {x y : α}, J.ReachPos x y →
      (x ∈ D.C ∨ (∃ c ∈ D.C, ∃ i, x = J.next i c) ∨ D.V x ≤ M) →
      (y ∈ D.C ∨ (∃ c ∈ D.C, ∃ i, y = J.next i c) ∨ D.V y ≤ M) := by
    intro x y h
    refine Relation.ReflTransGen.trans_induction_on h
      (motive := fun {x y : α} _ =>
        (x ∈ D.C ∨ (∃ c ∈ D.C, ∃ i, x = J.next i c) ∨ D.V x ≤ M) →
        (y ∈ D.C ∨ (∃ c ∈ D.C, ∃ i, y = J.next i c) ∨ D.V y ≤ M)) ?_ ?_ ?_
    · -- the trivial path
      intro a ha
      exact ha
    · -- one jump
      intro a b hab ha
      obtain ⟨i, hr, rfl⟩ := hab
      have hc0 : 0 ≤ D.c := D.hc.le
      rcases ha with hC | hC' | hV
      · exact Or.inr (Or.inl ⟨a, hC, i, rfl⟩)
      · by_cases hC0 : a ∈ D.C
        · exact Or.inr (Or.inl ⟨a, hC0, i, rfl⟩)
        · obtain ⟨c, hc, i0, haeq⟩ := hC'
          subst a
          have hVa : D.V (J.next i0 c) ≤ M := by
            have h1 : |D.V (J.next i0 c)| ≤ ∑ x ∈ C', |D.V x| := by
              refine Finset.single_le_sum (f := fun x => |D.V x|) (fun x _ => abs_nonneg _) ?_
              rw [hC'def]
              exact Finset.mem_biUnion.mpr
                ⟨c, (Set.Finite.mem_toFinset D.hC).mpr hc,
                  Finset.mem_image_of_mem _ (Finset.mem_univ i0)⟩
            have hV0 : 0 ≤ D.V a := D.hV a
            have habs : D.V (J.next i0 c) ≤ |D.V (J.next i0 c)| := le_abs_self _
            rw [hMdef]
            linarith
          have hdrop := D.hdrift (J.next i0 c) hC0 i hr
          exact Or.inr (Or.inr (by linarith))
      · by_cases hC0 : a ∈ D.C
        · exact Or.inr (Or.inl ⟨a, hC0, i, rfl⟩)
        · have hdrop := D.hdrift a hC0 i hr
          exact Or.inr (Or.inr (by linarith))
    · -- concatenation
      intro a b c h1 h2 h1' h2' ha
      exact h2' (h1' ha)
  have hsub : {b | J.ReachPos a b} ⊆ D.C ∪ (↑C' : Set α) ∪ {x | D.V x ≤ M} := by
    intro b hb
    have hVa : D.V a ≤ M := by
      have hS : 0 ≤ ∑ x ∈ C', |D.V x| := Finset.sum_nonneg fun x _ => abs_nonneg _
      rw [hMdef]
      linarith
    rcases hmem hb (Or.inr (Or.inr hVa)) with hC | hC' | hV
    · exact Set.mem_union_left _ (Set.mem_union_left _ hC)
    · obtain ⟨c, hc, i, rfl⟩ := hC'
      refine Set.mem_union_left _ (Set.mem_union_right _ ?_)
      rw [hC'def]
      exact Finset.mem_biUnion.mpr
        ⟨c, (Set.Finite.mem_toFinset D.hC).mpr hc, Finset.mem_image_of_mem _ (Finset.mem_univ i)⟩
    · exact Set.mem_union_right _ hV
  exact (D.hC.union (C'.finite_toSet)).union (D.hfin M) |>.subset hsub

end CountableFosterDrift

/-- **The hitting-time estimate under a constant drift.**  If the drift of the generator is at most
`-c` (`c > 0`) outside a finite set `C`, then the expected time of reaching `C` is at most
`V a / c`: the integral of the survival probability over `[0, T]` is at most `V a / c`, the
probability of not having reached `C` by time `T > 0` is at most `V a / (c T)`, and `C` is reached
with probability one.

This is the continuous-time Foster criterion (Foster 1951; Meyn–Tweedie 1993, Theorem 11.3.4) in
the form needed by the Anderson–Cappelletti–Kim–Nguyen conclusion. -/
theorem foster_hitting_time_of_constant_drift {α : Type*} [DecidableEq α] (J : JumpSystem α)
    (C : Finset α) (V : α → ℝ) (hV : ∀ a, 0 ≤ V a) (hfin : ∀ R : ℝ, {a | V a ≤ R}.Finite)
    {c : ℝ} (hc : 0 < c) (hdrift : ∀ a, a ∉ C → J.drift V a ≤ -c)
    {T : ℝ} (hT : 0 ≤ T) (a : α) :
    (∫ t in (0 : ℝ)..T, (1 - ∑ b ∈ C, (J.stopOn C).Pmin t a b) ≤ V a / c) ∧
      (∀ t, 0 < t → 1 - ∑ b ∈ C, (J.stopOn C).Pmin t a b ≤ V a / (c * t)) ∧
      (Tendsto (fun t => ∑ b ∈ C, (J.stopOn C).Pmin t a b) atTop (𝓝 1)) := by
  refine ⟨J.integral_notAbsorbed_le C V hV hfin hc hdrift hT a, fun t ht => ?_,
    J.tendsto_absorbed_one C V hV hfin hc hdrift a⟩
  exact J.notAbsorbed_le C V hV hfin hc hdrift ht a

/-- **The hitting-time estimate read off a drift certificate.**  A `CRNT.CountableFosterDrift`
certificate (with the total exit rate at least `1` outside the exceptional set) yields the
constant drift `Q V ≤ −c` off `C`, hence the Foster hitting-time estimate of
`CRNT.foster_hitting_time_of_constant_drift`. -/
theorem foster_hitting_time_of_certificate {α : Type*} [Countable α] [DecidableEq α]
    (J : JumpSystem α) (D : CountableFosterDrift α J)
    (hq : ∀ a, a ∉ D.C → 1 ≤ J.q a) {T : ℝ} (hT : 0 ≤ T) (a : α) :
    (∫ t in (0 : ℝ)..T, (1 - ∑ b ∈ D.hC.toFinset, (J.stopOn D.hC.toFinset).Pmin t a b)
        ≤ D.V a / D.c) ∧
      (∀ t, 0 < t →
        1 - ∑ b ∈ D.hC.toFinset, (J.stopOn D.hC.toFinset).Pmin t a b
          ≤ D.V a / (D.c * t)) ∧
      (Tendsto (fun t => ∑ b ∈ D.hC.toFinset, (J.stopOn D.hC.toFinset).Pmin t a b)
        atTop (𝓝 1)) := by
  have hdrift : ∀ x, x ∉ D.hC.toFinset → J.drift D.V x ≤ -D.c := by
    intro x hx
    refine D.drift_le hq (a := x) ?_
    intro hmem
    exact hx ((Set.Finite.mem_toFinset D.hC).mpr hmem)
  exact foster_hitting_time_of_constant_drift J D.hC.toFinset D.V D.hV D.hfin D.hc hdrift hT a

/-- **Positive recurrence from a constant Foster drift.**  Under a `CountableFosterDrift`
certificate (with the total exit rate at least `1` outside the exceptional set), and assuming the
chain is stochastic (no explosion) and the embedded jump chain is irreducible on the reachable
class, the chain has an invariant probability `π` supported on the class, `π` is strictly positive
on the class, the law of the chain converges to `π` in total variation from every state of the
class, and `π` is the unique such invariant probability.

The proof passes through the **squaring step** (`CRNT.CountableFosterDrift.drift_sq_le`): the
constant drift `Q V ≤ −c` off `C` becomes the *multiplicative* drift `Q V² ≤ −c V` off `C`, which
is the hypothesis of `CRNT.JumpSystem.foster_lyapunov_ergodic` with the reward function
`f = c · V`. -/
theorem foster_lyapunov_ergodic_of_constant_drift {α : Type*} [Countable α] [DecidableEq α]
    (J : JumpSystem α) (D : CountableFosterDrift α J)
    (hq : ∀ a, a ∉ D.C → 1 ≤ J.q a)
    (hstoch : ∀ t, 0 ≤ t → ∀ a, HasSum (fun b => J.Pmin t a b) 1)
    {a₀ : α} (E : Set α)
    (hE : ∀ a ∈ E, ∀ i, 0 < J.rate i a → J.next i a ∈ E)
    (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b) (ha₀ : a₀ ∈ E) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b = π b) ∧
      (∀ b, b ∉ E → π b = 0) ∧ (∀ b ∈ E, 0 < π b) ∧
      (∀ a ∈ E, Tendsto (fun t => ∑' b, |J.Pmin t a b - π b|) atTop (𝓝 0)) ∧
      (∀ μ : α → ℝ, (∀ b, 0 ≤ μ b) → (∀ b, b ∉ E → μ b = 0) → HasSum μ 1 →
        (∀ s, 0 ≤ s → ∀ b, ∑' c, μ c * J.Pmin s c b = μ b) → μ = π) := by
  classical
  -- the squared Lyapunov function and the reward function `f = c · V`
  set V2 : α → ℝ := fun a => (D.V a) ^ 2 with hV2def
  set f : α → ℝ := fun a => D.c * D.V a with hfdef
  have hV2 : ∀ a, 0 ≤ V2 a := fun a => sq_nonneg _
  have hf : ∀ a, 0 ≤ f a := fun a => mul_nonneg D.hc.le (D.hV a)
  have hfinf : ∀ R : ℝ, {a | f a ≤ R}.Finite := by
    intro R
    refine (D.hfin (R / D.c)).subset fun a ha => ?_
    simp only [hfdef, Set.mem_ofPred_eq] at ha
    simp only [Set.mem_ofPred_eq]
    exact (le_div_iff₀ D.hc).mpr (by simpa [mul_comm] using ha)
  -- the constant absorbing the drift on the finite exceptional set
  set K : ℝ := ∑ c ∈ D.hC.toFinset, (|J.drift V2 c| + f c) with hKdef
  have hK : 0 ≤ K := by
    rw [hKdef]
    exact Finset.sum_nonneg fun c _ => add_nonneg (abs_nonneg _) (hf c)
  have hdrift2 : ∀ a, J.drift V2 a ≤ -f a + K := by
    intro a
    by_cases ha : a ∈ D.C
    · -- on the exceptional set the drift is absorbed by `K`
      have hmem : a ∈ D.hC.toFinset := (Set.Finite.mem_toFinset D.hC).mpr ha
      have h1 : |J.drift V2 a| + f a ≤ K := by
        rw [hKdef]
        exact Finset.single_le_sum (fun c _ => add_nonneg (abs_nonneg _) (hf c)) hmem
      have h2 : J.drift V2 a ≤ |J.drift V2 a| := le_abs_self _
      linarith
    · -- off the exceptional set the squared drift is at most `-c V`
      have h1 : J.drift V2 a ≤ -D.c * D.V a := by
        rw [hV2def]
        exact D.drift_sq_le hq ha
      have h2 : -f a ≤ -f a + K := by linarith
      linarith
  obtain ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, huniq⟩ :=
    J.foster_lyapunov_ergodic V2 f hV2 hf hfinf hK hdrift2 hstoch (E := E) (a₀ := a₀)
      hE hirr ha₀
  exact ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, huniq⟩

/-- **Existence of an invariant probability from a constant Foster drift.**  Under a
`CountableFosterDrift` certificate (with the total exit rate at least `1` outside the exceptional
set) and the stochasticity hypothesis, the chain has an invariant probability supported on the
recurrent class. -/
theorem exists_invariant_of_constant_drift {α : Type*} [Countable α] [DecidableEq α]
    (J : JumpSystem α) (D : CountableFosterDrift α J)
    (hq : ∀ a, a ∉ D.C → 1 ≤ J.q a)
    (hstoch : ∀ t, 0 ≤ t → ∀ a, HasSum (fun b => J.Pmin t a b) 1)
    {a₀ : α} (E : Set α)
    (hE : ∀ a ∈ E, ∀ i, 0 < J.rate i a → J.next i a ∈ E)
    (hirr : ∀ a ∈ E, ∀ b ∈ E, J.ReachPos a b) (ha₀ : a₀ ∈ E) :
    ∃ π : α → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' c, π c * J.Pmin s c b = π b) := by
  obtain ⟨π, hπ0, hπ1, hπinv, -⟩ :=
    foster_lyapunov_ergodic_of_constant_drift J D hq hstoch E hE hirr ha₀
  exact ⟨π, hπ0, hπ1, hπinv⟩

/-! ## An instance: the pure death chain -/

namespace Examples

namespace PureDeath

/-- The **pure death chain** `n → n − 1` at rate `n`: from the count `n` the chain jumps to
`n − 1` at rate `n`. -/
noncomputable def chain : JumpSystem ℕ where
  ι := Fin 1
  rate i n := (n : ℝ)
  rate_nonneg := by
    intro i n
    exact Nat.cast_nonneg n
  next i n := n - 1

/-- The Lyapunov function of the pure death chain: the count itself. -/
def lyap : ℕ → ℝ := fun n => (n : ℝ)

theorem lyap_nonneg (n : ℕ) : 0 ≤ lyap n := Nat.cast_nonneg n

theorem lyap_finiteSublevel (R : ℝ) : {n | lyap n ≤ R}.Finite := by
  by_cases hR : R < 0
  · refine ((Finset.range 0 : Finset ℕ).finite_toSet).subset ?_
    intro (n : ℕ) hn
    simp only [Set.mem_ofPred_eq, lyap] at hn
    have hnn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    exfalso
    linarith
  · have h0 : 0 ≤ R := le_of_not_gt hR
    refine (Finset.range (Nat.floor R + 1)).finite_toSet.subset ?_
    intro n hn
    simp only [Set.mem_ofPred_eq, lyap] at hn
    have hlt : (n : ℝ) < (Nat.floor R : ℝ) + 1 := by
      have := Nat.lt_floor_add_one R
      linarith
    have h3 : n < Nat.floor R + 1 := by exact_mod_cast hlt
    show n ∈ Finset.range (Nat.floor R + 1)
    exact Finset.mem_range.mpr h3

/-- The exit rate of the pure death chain. -/
theorem q_eq (n : ℕ) : chain.q n = (n : ℝ) := by
  show (∑ i : chain.ι, chain.rate i n) = (n : ℝ)
  have h1 : (∑ i : chain.ι, chain.rate i n) = chain.rate (0 : Fin 1) n := Fin.sum_univ_one _
  rw [h1]
  simp [chain]

/-- The drift of the Lyapunov function of the pure death chain. -/
theorem drift_eq (n : ℕ) : chain.drift lyap n = -(n : ℝ) := by
  show (∑ i : chain.ι, (chain.rate i n) * (lyap (chain.next i n) - lyap n)) = -(n : ℝ)
  have h1 : (∑ i : chain.ι, (chain.rate i n) * (lyap (chain.next i n) - lyap n))
      = (chain.rate (0 : Fin 1) n) * (lyap (chain.next (0 : Fin 1) n) - lyap n) :=
    Fin.sum_univ_one _
  rw [h1]
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [chain, lyap, h]
  · have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      ring
    simp only [chain, lyap]
    rw [hcast]
    ring

/-- **The constant drift of the pure death chain.**  Outside `{0}` the drift of the count is
`−n ≤ −1`: the pure death chain satisfies the Anderson--Cappelletti--Kim--Nguyen drift condition
with `c = 1` and `C = {0}`. -/
theorem drift_le_one {n : ℕ} (hn : n ≠ 0) : chain.drift lyap n ≤ -(1 : ℝ) := by
  have h1 := PureDeath.drift_eq n
  have hn1 : 1 ≤ n := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    omega
  have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  linarith

/-- **The drift certificate of the pure death chain.** -/
def certificate : CountableFosterDrift ℕ chain where
  V := lyap
  hV := lyap_nonneg
  hfin := lyap_finiteSublevel
  c := 1
  hc := one_pos
  C := {0}
  hC := by simp
  hdrift := by
    intro n hn i hpos
    have hn1 : 1 ≤ n := by
      have : 0 < n := Nat.pos_of_ne_zero hn
      omega
    have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      ring
    have hdiff : lyap (chain.next i n) - lyap n = -1 := by
      simp [chain, lyap, hcast]
    rw [hdiff]

/-- **The rate hypothesis of the pure death chain**: the total exit rate is at least `1` outside
the exceptional set `{0}`. -/
theorem rate_ge_one {n : ℕ} (hn : n ≠ 0) : 1 ≤ chain.q n := by
  have h1 := PureDeath.q_eq n
  have hn1 : 1 ≤ n := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    omega
  have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  linarith

/-- **The pure death chain does not explode.** -/
theorem stoch {t : ℝ} (ht : 0 ≤ t) (n : ℕ) : HasSum (fun b => chain.Pmin t n b) 1 := by
  refine chain.hasSum_Pmin_one_of_drift_affine lyap lyap_nonneg lyap_finiteSublevel
    (le_refl 0) (le_refl 0) (fun m => ?_) ht n
  rw [drift_eq]
  have hnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  linarith

/-- **The positive recurrence of the pure death chain.**  The chain is absorbed at `{0}`, its
minimal transition function is stochastic, and the unique invariant probability is the point mass
at `0`; the theorem `CRNT.foster_lyapunov_ergodic_of_constant_drift` produces it. -/
theorem positiveRecurrence :
    ∃ π : ℕ → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' c, π c * chain.Pmin s c b = π b) ∧
      (∀ b, b ∉ ({0} : Set ℕ) → π b = 0) ∧ (∀ b ∈ ({0} : Set ℕ), 0 < π b) ∧
      (∀ a ∈ ({0} : Set ℕ),
        Tendsto (fun t => ∑' b, |chain.Pmin t a b - π b|) atTop (𝓝 0)) ∧
      (∀ μ : ℕ → ℝ, (∀ b, 0 ≤ μ b) → (∀ b, b ∉ ({0} : Set ℕ) → μ b = 0) → HasSum μ 1 →
        (∀ s, 0 ≤ s → ∀ b, ∑' c, μ c * chain.Pmin s c b = μ b) → μ = π) := by
  obtain ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, huniq⟩ :=
    foster_lyapunov_ergodic_of_constant_drift chain certificate
      (fun a ha => rate_ge_one (by
        have : a ≠ 0 := fun h => ha (by simp [certificate, h])
        exact this))
      (fun t ht a => stoch ht a) (E := {0}) (a₀ := 0)
      (fun a ha i hi => by
        have ha0 : a = 0 := by simpa using ha
        subst ha0
        exact absurd hi (by simp [chain]))
      (fun a ha b hb => by subst a; subst b; exact Relation.ReflTransGen.refl)
      (by simp)
  exact ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, huniq⟩

end PureDeath

end Examples

#print axioms CRNT.CountableFosterDrift
#print axioms CRNT.CountableFosterDrift.drift_le_mul_q
#print axioms CRNT.CountableFosterDrift.drift_le
#print axioms CRNT.CountableFosterDrift.drift_sq_le_mul_q
#print axioms CRNT.CountableFosterDrift.drift_sq_le
#print axioms CRNT.CountableFosterDrift.reachable_finite
#print axioms CRNT.foster_hitting_time_of_constant_drift
#print axioms CRNT.foster_hitting_time_of_certificate
#print axioms CRNT.foster_lyapunov_ergodic_of_constant_drift
#print axioms CRNT.exists_invariant_of_constant_drift
#print axioms CRNT.Examples.PureDeath.certificate
#print axioms CRNT.Examples.PureDeath.positiveRecurrence

end CRNT
