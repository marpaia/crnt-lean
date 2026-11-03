import CRNT.Stochastic.PathExitEvent

/-!
# The identification of the exit mass with the exit-exact kernel

This module closes the algebraic gap left open by `CRNT/Stochastic/PathExitEvent.lean` in
leaf **P8 (Kurtz's law of large numbers)**: it identifies the *exit mass* of the chain
frozen outside a set `K` with the *exit-exact kernel* `CRNT.JumpSystem.Pexit`, and derives
the set-level union bound and the Markov step of the sample-path reading from it.

## 1. The two kernels

For a finite set `K` of states, the library has

* `CRNT.JumpSystem.Pexit K k t a b`: the probability that the chain started at `a` makes its
  `k`-th jump by time `t`, that this jump is the *first* jump leaving `K`, and that it lands
  at `b` (`CRNT.Stochastic.PathExitEvent`);
* `CRNT.JumpSystem.exitMass K c h`: the mass of the chain *frozen* outside `K`
  (`CRNT.JumpSystem.stopOutside K`), started at `c`, that is outside `K` at time `h`
  (`CRNT.Stochastic.ExitMass`).

The two are computed by completely different recursions: `Pexit` integrates the *original*
rates, while `exitMass` integrates the *frozen* transition function.  The bridge is the
observation that the original chain and the chain frozen outside `K` **coincide as long as
they are inside `K`** (they have the same rates, the same exit rate and the same successor
there), and that the frozen chain **does not move once it has left `K`**.

This is proved here, in the shape of the parallel recursion of `Pexit`:

* `CRNT.JumpSystem.Pexact_stopOutside_eq_zero_of_not_mem`: outside `K` the frozen chain
  makes no further jump;
* `CRNT.JumpSystem.Pexit_eq_zero_of_mem`: the exit-exact kernel lands outside `K`;
* `CRNT.JumpSystem.PexactOutside_eq_Pexit`: **the frozen recursion** — for `a ∈ K`, `k ≥ 1`
  and `b ∉ K`,
  `(J.stopOutside K).Pexact k t a b = J.Pexit K k t a b`.

The last statement is the "parallel recursion" that the previous session could not complete.
The elaboration mismatch between `J.ι` and `(J.stopOutside K).ι` is avoided by writing the
recursion of the frozen system directly in terms of `J.stopOutside K`: the two systems have
the same `ι` (`JumpSystem.stopOutside` sets `ι := J.ι`), the same `next`
(`JumpSystem.stopOutside_next`) and the same rates on `K` (`JumpSystem.stopOutside_rate`),
so the two recursions have exactly the same shape.

## 2. The identification (★)

`CRNT.JumpSystem.exitMass_eq_tsum_PexitSum` and
`CRNT.JumpSystem.exitMass_eq_tsum_Pexit` state the identification:

`J.exitMass K c h = ∑_k ∑_b J.Pexit K k h c b`  (for `c ∈ K` and `h ≥ 0`)

Both sides measure the same event, "the chain started at `c` leaves `K` during the window
`[0, h]`": the left-hand side is the mass of the frozen chain that is outside `K` at time
`h`; the right-hand side counts the *first* jump leaving `K` exactly, by its index and by
its landing state.  The two agree because of §1.

The proof needs the summability of the series, which is proved here
(`CRNT.JumpSystem.summable_exitRowMass`, `CRNT.JumpSystem.summable_exit_exact`,
`CRNT.JumpSystem.summable_PexitSum`): the exit-exact masses form a genuine series, and the
interchange of the sum over the jump index with the sum over the landing state is justified
by `Summable.tsum_comm`.

## 3. The set-level union bound (★★)

`CRNT.JumpSystem.exitMass_union_le`: if `A k` is the measurable event "the `k`-th jump of
the chain started at `c` is the first jump leaving `K` and happens by time `h`", and
`μ (A k) ≤ ENNReal.ofReal (J.PexitSum K k h c)`, then

`μ (⋃ k, A k) ≤ ENNReal.ofReal (J.exitMass K c h)`.

This is the union bound of the sample-path reading, with the exit mass as the bound: the
measure of the exit event is at most the exit mass.

## 4. The Markov step (★★★)

`CRNT.Network.grid_exitMass_ge_window`: the `i`-th window of the grid exit mass
`CRNT.Network.grid_exitMass` is at least the exit mass of the same window started from the
*frozen* chain at time `t i`,

`∑_c P(t i)(n,c) · exitMass_{B_i}(c) ≥ ∑_{c ∈ B_i} Pmin^{B_i}(t i)(n,c) · exitMass_{B_i}(c)`,

because the original chain dominates the frozen chain on `B_i`
(`CRNT.JumpSystem.Pmin_stopOutside_le`) and the exit mass is non-negative.
`CRNT.Network.grid_exitMass_ge` is the corresponding statement for the whole grid.

## 5. Relation to leaf P8, and what is still missing

Leaf **P8 (Kurtz's law of large numbers)** is proved in the *path-free* "exit-mass" form
(`CRNT.Network.kurtz_lln_uniform`, `CRNT.Network.exit_mass_le`).  The present module
supplies the missing *algebraic* link between the exit mass and the literal path event:

* the exit mass is now *exactly* the sum over the exit-exact kernel, i.e. the measure of the
  event "the chain leaves `K` during the window", counted by the index of the first
  exit jump and by its landing state;
* the union bound over that event is proved at the level of sets and measures.

**What is still missing** is a *probability measure on the path space* `CRNT.Network.JumpPath`:
the library has no i.i.d.-exponential (or Poisson-clock) measure on the holding times, and
no strong Markov property.  Without them the events "the chain leaves `B_i` during the
`i`-th window" cannot be *identified* with the exit mass `exitMass_{B_i}(c)`; the present
module shows only that the exit mass is the right *bound* for such an event, and that it is
the exact measure of the corresponding exit-exact event.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped BigOperators ENNReal Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/-- The frozen chain does not move once it is outside `K`. -/
theorem Pexact_stopOutside_eq_zero_of_not_mem (K : Finset α) :
    ∀ (k : ℕ) (t : ℝ) (a b : α), a ∉ K → 1 ≤ k → (J.stopOutside K).Pexact k t a b = 0 := by
  intro k
  induction k with
  | zero =>
      intro t a b ha hk
      omega
  | succ k ih =>
      intro t a b ha hk
      rw [(J.stopOutside K).Pexact_succ]
      have hsum : ∀ s : ℝ, (∑ i, (J.stopOutside K).rate i a *
          (J.stopOutside K).Pexact k (t - s) ((J.stopOutside K).next i a) b) = 0 := by
        intro s
        rw [J.sum_stopOutside_rate_mul_of_not_mem ha]
      simp [hsum]

/-- **The exit-exact kernel lands outside `K`.**  If `b ∈ K` then `J.Pexit K k t a b = 0`: the
exit-exact kernel only counts jumps that *leave* `K`. -/
theorem Pexit_eq_zero_of_mem (K : Finset α) :
    ∀ (k : ℕ) (t : ℝ) (a b : α), b ∈ K → J.Pexit K k t a b = 0 := by
  intro k
  induction k with
  | zero =>
      intro t a b hb
      rw [Pexit_zero]
  | succ k ih =>
      intro t a b hb
      rw [J.Pexit_succ]
      by_cases ha : a ∉ K
      · simp [ha]
      · rw [ite_eq_right ha]
        have hsum : ∀ s : ℝ, (∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
            (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
             else if k = 0 ∧ J.next i a = b then 1 else 0)) = 0 := by
          intro s
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : J.next i a ∈ K
          · have h1 : (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                else if k = 0 ∧ J.next i a = b then 1 else 0) = 0 := by
                rw [ite_eq_left hi]
                exact ih (t - s) (J.next i a) b hb
            rw [h1, mul_zero]
          · have h1 : (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                else if k = 0 ∧ J.next i a = b then 1 else 0) = 0 := by
                rw [ite_eq_right hi]
                by_cases hk0 : k = 0 ∧ J.next i a = b
                · rw [ite_eq_left hk0]
                  exact absurd (hk0.2 ▸ hb) hi
                · rw [ite_eq_right hk0]
            rw [h1, mul_zero]
        have hEq : (fun s : ℝ => ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
              (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
               else if k = 0 ∧ J.next i a = b then 1 else 0))
            = fun _ : ℝ => (0 : ℝ) := by
          funext s; rw [hsum s]
        calc
          (∫ s in (0 : ℝ)..t, ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then 1 else 0))
              = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
                rw [intervalIntegral.integral_congr (E := ℝ)
                  (f := fun s : ℝ => ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                    (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                     else if k = 0 ∧ J.next i a = b then 1 else 0))
                  (g := fun _ : ℝ => (0 : ℝ)) (fun s _ => congrFun hEq s)]
          _ = 0 := intervalIntegral.integral_zero

/-- **The frozen chain's exact-jump kernel is the exit-exact kernel.**  For `a ∈ K`, `k ≥ 1`
and `b ∉ K`, the probability that the chain frozen outside `K`, started at `a`, has made
exactly `k` jumps by time `t` and is at `b` equals the probability that the `k`-th jump of
the original chain is the first jump leaving `K`, happens by time `t`, and lands at `b`.

This is the algebraic core of the identification: the original chain and the chain frozen
outside `K` agree as long as they are inside `K`, and the frozen chain does not move once it
has left `K`. -/
theorem PexactOutside_eq_Pexit (K : Finset α) :
    ∀ (k : ℕ) (a : α), a ∈ K → 1 ≤ k → ∀ (t : ℝ) (b : α), b ∉ K →
      (J.stopOutside K).Pexact k t a b = J.Pexit K k t a b := by
  intro k
  induction k with
  | zero =>
      intro a ha hk t b hb
      omega
  | succ k ih =>
      intro a ha hk t b hb
      by_cases hk0 : k = 0
      · -- the first jump leaves `K`
        have hk1 : k + 1 = 1 := by omega
        rw [hk1]
        rw [(J.stopOutside K).Pexact_succ 0 t a b]
        rw [J.Pexit_succ K 0 t a b, ite_eq_right (fun h => h ha)]
        have hterm : ∀ (s : ℝ) (i : J.ι),
            (J.stopOutside K).rate i a *
                (J.stopOutside K).Pexact 0 (t - s) ((J.stopOutside K).next i a) b
            = J.rate i a *
                (if J.next i a ∈ K then J.Pexit K 0 (t - s) (J.next i a) b
                 else if 0 = 0 ∧ J.next i a = b then 1 else 0) := by
          intro s i
          rw [J.stopOutside_rate, ite_eq_left ha, J.stopOutside_next]
          rw [(J.stopOutside K).Pexact_zero]
          by_cases hi : J.next i a ∈ K
          · have hq : (J.stopOutside K).q (J.next i a) = J.q (J.next i a) :=
              J.stopOutside_q_of_mem hi
            have hne : J.next i a ≠ b := by
              intro h
              rw [h] at hi
              exact hb hi
            rw [hq]
            simp only [ite_eq_right hne, mul_zero]
            rw [J.Pexit_zero, ite_eq_left hi]
            simp
          · have hq : (J.stopOutside K).q (J.next i a) = 0 := J.stopOutside_q_of_not_mem hi
            rw [hq]
            simp only [zero_mul, neg_zero, Real.exp_zero]
            rw [ite_eq_right hi]
            by_cases hne : J.next i a = b
            · rw [ite_eq_left hne, ite_eq_left (by simp [hne])]
              simp
            · rw [ite_eq_right hne, ite_eq_right (by simp [hne])]
              simp
        have hconv : ∀ s : ℝ,
            Real.exp (-((J.stopOutside K).q a * s)) *
                ∑ i, (J.stopOutside K).rate i a *
                  (J.stopOutside K).Pexact 0 (t - s) ((J.stopOutside K).next i a) b
            =
            ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K 0 (t - s) (J.next i a) b
                 else if 0 = 0 ∧ J.next i a = b then 1 else 0) := by
          intro s
          rw [J.stopOutside_q_of_mem ha, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hterm s i]
          ring
        refine intervalIntegral.integral_congr (E := ℝ)
          (f := fun s : ℝ => Real.exp (-((J.stopOutside K).q a * s)) *
            ∑ i, (J.stopOutside K).rate i a *
              (J.stopOutside K).Pexact 0 (t - s) ((J.stopOutside K).next i a) b)
          (g := fun s : ℝ => ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
            (if J.next i a ∈ K then J.Pexit K 0 (t - s) (J.next i a) b
             else if 0 = 0 ∧ J.next i a = b then 1 else 0))
          (fun s _ => hconv s)
      · -- the `k`-th jump is the first exit
        have hk1 : 1 ≤ k := by omega
        rw [(J.stopOutside K).Pexact_succ k t a b]
        rw [J.Pexit_succ K k t a b, ite_eq_right (fun h => h ha)]
        have hterm : ∀ (s : ℝ) (i : J.ι),
            (J.stopOutside K).rate i a *
                (J.stopOutside K).Pexact k (t - s) ((J.stopOutside K).next i a) b
            = J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then 1 else 0) := by
          intro s i
          rw [J.stopOutside_rate, ite_eq_left ha, J.stopOutside_next]
          by_cases hi : J.next i a ∈ K
          · rw [ih (J.next i a) hi hk1 (t - s) b hb, ite_eq_left hi]
          · rw [J.Pexact_stopOutside_eq_zero_of_not_mem K k (t - s) (J.next i a) b hi hk1]
            rw [ite_eq_right hi, ite_eq_right (fun h => hk0 h.1)]
        have hconv : ∀ s : ℝ,
            Real.exp (-((J.stopOutside K).q a * s)) *
                ∑ i, (J.stopOutside K).rate i a *
                  (J.stopOutside K).Pexact k (t - s) ((J.stopOutside K).next i a) b
            =
            ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then 1 else 0) := by
          intro s
          rw [J.stopOutside_q_of_mem ha, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hterm s i]
          ring
        refine intervalIntegral.integral_congr (E := ℝ)
          (f := fun s : ℝ => Real.exp (-((J.stopOutside K).q a * s)) *
            ∑ i, (J.stopOutside K).rate i a *
              (J.stopOutside K).Pexact k (t - s) ((J.stopOutside K).next i a) b)
          (g := fun s : ℝ => ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
            (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
             else if k = 0 ∧ J.next i a = b then 1 else 0))
          (fun s _ => hconv s)

/-- **The row mass of the frozen chain.**  The mass of the chain frozen outside `K` that is
outside `K` after *exactly* `k` jumps by time `h`; this is the mass of the event "the `k`-th
jump is the first jump leaving `K`". -/
noncomputable def exitRowMass (K : Finset α) (c : α) (k : ℕ) (h : ℝ) : ℝ :=
  ∑' b, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0)

/-- The row mass is non-negative. -/
theorem exitRowMass_nonneg (K : Finset α) (c : α) (k : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ J.exitRowMass K c k h := by
  refine tsum_nonneg fun b => ?_
  by_cases hb : b ∉ K
  · rw [ite_eq_left hb]
    exact (J.stopOutside K).Pexact_nonneg k h hh c b
  · simp only [ite_eq_right hb]
    exact le_rfl

set_option linter.unusedVariables false in
/-- **The row masses of the frozen chain are summable in `k`.**  This is the summability
that makes the exit mass the sum of a genuine series. -/
theorem summable_exitRowMass (K : Finset α) (c : α) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h) :
    Summable fun k => J.exitRowMass K c k h := by
  refine summable_of_sum_le (c := 1) (fun k => J.exitRowMass_nonneg K c k hh) ?_
  intro F
  have hfinite : ∀ k ∈ F, J.exitRowMass K c k h =
      ∑ b ∈ (J.stopOutside K).reachK k c,
        (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
    intro k hk
    rw [exitRowMass, tsum_eq_sum (s := (J.stopOutside K).reachK k c) (fun b hb => by
      by_cases hb2 : b ∉ K
      · simp only [ite_eq_left hb2]
        exact (J.stopOutside K).Pexact_eq_zero_of_not_mem k h c b hb
      · simp only [ite_eq_right hb2])]
  set BF : Finset α := F.biUnion fun k => (J.stopOutside K).reachK k c with hBF
  have hsub : ∀ k ∈ F, (J.stopOutside K).reachK k c ⊆ BF := by
    intro k hk b hb
    rw [hBF]
    exact Finset.mem_biUnion.mpr ⟨k, hk, hb⟩
  have hPminHasSum : HasSum (fun b => (J.stopOutside K).Pmin h c b) 1 :=
    (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x)
      (fun c' _ => J.stopOutside_q_le K c') hh
  have hPmin : Summable fun b => (J.stopOutside K).Pmin h c b := hPminHasSum.summable
  calc
    (∑ k ∈ F, J.exitRowMass K c k h) = ∑ k ∈ F, ∑ b ∈ (J.stopOutside K).reachK k c,
        (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
      rw [Finset.sum_congr rfl fun k hk => hfinite k hk]
    _ ≤ ∑ k ∈ F, ∑ b ∈ BF, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
      refine Finset.sum_le_sum fun k hk => ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg (hsub k hk) ?_
      intro b _ _
      by_cases hb : b ∉ K
      · simp only [ite_eq_left hb]
        exact (J.stopOutside K).Pexact_nonneg k h hh c b
      · simp only [ite_eq_right hb]
        exact le_rfl
    _ = ∑ b ∈ BF, ∑ k ∈ F, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ b ∈ BF, ∑' k, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
      refine Finset.sum_le_sum fun b _ => ?_
      have hsb : Summable fun k => (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
        refine Summable.of_nonneg_of_le
          (f := fun k => (J.stopOutside K).Pexact k h c b)
          (g := fun k => (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0)) ?_ ?_ ?_
        · intro k
          by_cases hb : b ∉ K
          · simp only [ite_eq_left hb]
            exact (J.stopOutside K).Pexact_nonneg k h hh c b
          · simp only [ite_eq_right hb]
            exact le_rfl
        · intro k
          by_cases hb : b ∉ K
          · simp only [ite_eq_left hb]
            exact le_rfl
          · simp only [ite_eq_right hb]
            exact (J.stopOutside K).Pexact_nonneg k h hh c b
        · exact ((J.stopOutside K).hasSum_Pexact h hh c b).summable
      exact Summable.sum_le_tsum F (fun k _ => by
        by_cases hb : b ∉ K
        · simp only [ite_eq_left hb]
          exact (J.stopOutside K).Pexact_nonneg k h hh c b
        · simp only [ite_eq_right hb]
          exact le_rfl) hsb
    _ = ∑ b ∈ BF, (if b ∉ K then (J.stopOutside K).Pmin h c b else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b ∉ K
      · simp only [ite_eq_left hb]
        exact ((J.stopOutside K).hasSum_Pexact h hh c b).tsum_eq
      · simp only [ite_eq_right hb]
        exact tsum_zero
    _ ≤ ∑ b ∈ BF, (J.stopOutside K).Pmin h c b := by
      refine Finset.sum_le_sum fun b _ => ?_
      by_cases hb : b ∉ K
      · simp only [ite_eq_left hb]
        exact le_rfl
      · simp only [ite_eq_right hb]
        exact (J.stopOutside K).Pmin_nonneg h hh c b
    _ ≤ ∑' b, (J.stopOutside K).Pmin h c b :=
      Summable.sum_le_tsum BF (fun b _ => (J.stopOutside K).Pmin_nonneg h hh c b) hPmin
    _ = 1 := hPminHasSum.tsum_eq

set_option linter.unusedVariables false in
/-- **The double series of the exit-exact kernel is summable.**  This is the summability
that allows the interchange of the sum over the jump index and the sum over the landing
state (`Summable.tsum_comm`). -/
theorem summable_exit_exact (K : Finset α) (c : α) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h) :
    Summable (fun p : ℕ × α => (if p.2 ∉ K then (J.stopOutside K).Pexact p.1 h c p.2 else 0)) := by
  refine summable_of_sum_le (c := 1) (fun p => by
    by_cases hb : p.2 ∉ K
    · rw [ite_eq_left hb]
      exact (J.stopOutside K).Pexact_nonneg p.1 h hh c p.2
    · simp only [ite_eq_right hb]
      exact le_rfl) ?_
  intro s
  set Ks : Finset ℕ := s.image Prod.fst with hKs
  set Bs : Finset α := s.image Prod.snd with hBs
  have hsub : s ⊆ Ks ×ˢ Bs := by
    intro p hp
    rw [Finset.mem_product]
    exact ⟨Finset.mem_image.2 ⟨p, hp, rfl⟩, Finset.mem_image.2 ⟨p, hp, rfl⟩⟩
  have hnonneg : ∀ p : ℕ × α,
      0 ≤ (if p.2 ∉ K then (J.stopOutside K).Pexact p.1 h c p.2 else 0) := by
    intro p
    by_cases hb : p.2 ∉ K
    · rw [ite_eq_left hb]
      exact (J.stopOutside K).Pexact_nonneg p.1 h hh c p.2
    · simp only [ite_eq_right hb]
      exact le_rfl
  have hPminHasSum : HasSum (fun b => (J.stopOutside K).Pmin h c b) 1 :=
    (J.stopOutside K).hasSum_Pmin_one (Λ := ∑ x ∈ K, J.q x)
      (fun c' _ => J.stopOutside_q_le K c') hh
  have hPmin : Summable fun b => (J.stopOutside K).Pmin h c b := hPminHasSum.summable
  calc
    (∑ p ∈ s, (if p.2 ∉ K then (J.stopOutside K).Pexact p.1 h c p.2 else 0))
        ≤ ∑ p ∈ Ks ×ˢ Bs, (if p.2 ∉ K then (J.stopOutside K).Pexact p.1 h c p.2 else 0) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => hnonneg p)
    _ = ∑ k ∈ Ks, ∑ b ∈ Bs, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
      rw [Finset.sum_product]
    _ = ∑ b ∈ Bs, ∑ k ∈ Ks, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
      rw [Finset.sum_comm]
    _ ≤ ∑ b ∈ Bs, ∑' k, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
      refine Finset.sum_le_sum fun b _ => ?_
      have hsb : Summable fun k => (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
        refine Summable.of_nonneg_of_le
          (f := fun k => (J.stopOutside K).Pexact k h c b)
          (g := fun k => (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0)) ?_ ?_ ?_
        · intro k
          by_cases hb : b ∉ K
          · simp only [ite_eq_left hb]
            exact (J.stopOutside K).Pexact_nonneg k h hh c b
          · simp only [ite_eq_right hb]
            exact le_rfl
        · intro k
          by_cases hb : b ∉ K
          · simp only [ite_eq_left hb]
            exact le_rfl
          · simp only [ite_eq_right hb]
            exact (J.stopOutside K).Pexact_nonneg k h hh c b
        · exact ((J.stopOutside K).hasSum_Pexact h hh c b).summable
      exact Summable.sum_le_tsum Ks (fun k _ => by
        by_cases hb : b ∉ K
        · simp only [ite_eq_left hb]
          exact (J.stopOutside K).Pexact_nonneg k h hh c b
        · simp only [ite_eq_right hb]
          exact le_rfl) hsb
    _ = ∑ b ∈ Bs, (if b ∉ K then (J.stopOutside K).Pmin h c b else 0) := by
      refine Finset.sum_congr rfl fun b _ => ?_
      by_cases hb : b ∉ K
      · simp only [ite_eq_left hb]
        exact ((J.stopOutside K).hasSum_Pexact h hh c b).tsum_eq
      · simp only [ite_eq_right hb]
        exact tsum_zero
    _ ≤ ∑ b ∈ Bs, (J.stopOutside K).Pmin h c b := by
      refine Finset.sum_le_sum fun b _ => ?_
      by_cases hb : b ∉ K
      · simp only [ite_eq_left hb]
        exact le_rfl
      · simp only [ite_eq_right hb]
        exact (J.stopOutside K).Pmin_nonneg h hh c b
    _ ≤ ∑' b, (J.stopOutside K).Pmin h c b :=
      Summable.sum_le_tsum Bs (fun b _ => (J.stopOutside K).Pmin_nonneg h hh c b) hPmin
    _ = 1 := hPminHasSum.tsum_eq

set_option linter.unusedVariables false in
/-- **The `k`-th-jump exit mass is the `k`-th row mass of the frozen chain.**  For `c ∈ K`,
the mass of the event "the `k`-th jump of the chain started at `c` is the first jump leaving
`K`, and happens by time `h`" equals the mass of the frozen chain being outside `K` after
exactly `k` jumps. -/
theorem PexitSum_eq_exitRowMass (K : Finset α) (c : α) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h)
    (k : ℕ) : J.PexitSum K k h c = J.exitRowMass K c k h := by
  by_cases hk0 : k = 0
  · rw [hk0]
    have hz : ∀ b, (if b ∉ K then (J.stopOutside K).Pexact 0 h c b else 0) = 0 := by
      intro b
      by_cases hb : b ∉ K
      · rw [ite_eq_left hb]
        have hne : c ≠ b := fun h => hb (h ▸ hc)
        rw [(J.stopOutside K).Pexact_zero, ite_eq_right hne, mul_zero]
      · rw [ite_eq_right hb]
    rw [exitRowMass, tsum_eq_sum (s := (∅ : Finset α)) (fun b _ => hz b)]
    simp [PexitSum, J.Pexit_zero]
  · have hk1 : 1 ≤ k := by omega
    rw [exitRowMass]
    refine tsum_congr fun b => ?_
    by_cases hb : b ∈ K
    · rw [ite_eq_right (fun h => h hb)]
      exact J.Pexit_eq_zero_of_mem K k h c b hb
    · rw [ite_eq_left hb]
      exact (J.PexactOutside_eq_Pexit K k c hc hk1 h b hb).symm

/-- The exit-exact masses form a summable series. -/
theorem summable_PexitSum (K : Finset α) (c : α) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h) :
    Summable fun k => J.PexitSum K k h c := by
  have h : (fun k => J.PexitSum K k h c) = fun k => J.exitRowMass K c k h := by
    funext k
    exact J.PexitSum_eq_exitRowMass K c hc hh k
  rw [h]
  exact J.summable_exitRowMass K c hc hh

/--
**The identification (★).**

The exit mass of the chain frozen outside `K`, started at `c ∈ K`, equals the sum over the
jump index `k` of the exit-exact mass `J.PexitSum K k h c`; equivalently, it is the sum over
`k` and over the landing state `b` of the exit-exact kernel `J.Pexit K k h c b`.

Both sides measure the same event: "the chain started at `c` leaves `K` during the window
`[0, h]`".  The left-hand side is the mass of the frozen chain that is outside `K` at time
`h`; the right-hand side counts the *first* jump leaving `K` exactly, by its index and its
landing state.  The two agree because the original chain and the chain frozen outside `K`
coincide as long as they are inside `K` (`JumpSystem.PexactOutside_eq_Pexit`).
-/
theorem exitMass_eq_tsum_PexitSum (K : Finset α) (c : α) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h) :
    J.exitMass K c h = ∑' k, J.PexitSum K k h c := by
  have h1 : J.exitMass K c h = ∑' b, (if b ∉ K then (J.stopOutside K).Pmin h c b else 0) := by
    rw [exitMass]
    refine tsum_congr fun b => ?_
    by_cases hb : b ∈ K
    · rw [ite_eq_left hb, ite_eq_right (fun h => h hb)]
    · rw [ite_eq_right hb, ite_eq_left hb]
  have h2 : ∀ b, (if b ∉ K then (J.stopOutside K).Pmin h c b else 0)
      = ∑' k, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
    intro b
    by_cases hb : b ∉ K
    · simp only [ite_eq_left hb]
      exact ((J.stopOutside K).hasSum_Pexact h hh c b).tsum_eq.symm
    · simp only [ite_eq_right hb]
      exact tsum_zero.symm
  have h3 : (∑' b, ∑' k, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0))
      = ∑' k, ∑' b, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
    exact Summable.tsum_comm
      (f := fun k b => (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0))
      (J.summable_exit_exact K c hc hh)
  calc
    J.exitMass K c h
      = ∑' b, (if b ∉ K then (J.stopOutside K).Pmin h c b else 0) := h1
    _ = ∑' b, ∑' k, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := by
        refine tsum_congr fun b => ?_
        rw [h2 b]
    _ = ∑' k, ∑' b, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0) := h3
    _ = ∑' k, J.exitRowMass K c k h := by
        refine tsum_congr fun k => ?_
        exact (rfl : (∑' b, (if b ∉ K then (J.stopOutside K).Pexact k h c b else 0))
          = J.exitRowMass K c k h)
    _ = ∑' k, J.PexitSum K k h c := by
        refine tsum_congr fun k => ?_
        exact (J.PexitSum_eq_exitRowMass K c hc hh k).symm

/--
**The identification (★), in the explicit double-sum form.**

`J.exitMass K c h = ∑_k ∑_b J.Pexit K k h c b`: the exit mass of the frozen chain equals
the sum over the jump index and the landing state of the exit-exact kernel.
-/
theorem exitMass_eq_tsum_Pexit (K : Finset α) (c : α) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h) :
    J.exitMass K c h = ∑' k, ∑' b, J.Pexit K k h c b := by
  rw [J.exitMass_eq_tsum_PexitSum K c hc hh]
  refine tsum_congr fun k => ?_
  exact (rfl : (∑' b, J.Pexit K k h c b) = J.PexitSum K k h c)


/--
**The set-level union bound (★★).**

The measure of the event "the chain started at `c` leaves `K` during the window `[0, h]`"
is at most the exit mass.

Formally: let `A k` be the measurable event "the `k`-th jump of the chain started at `c` is
the first jump leaving `K` and happens by time `h`".  If the measure of `A k` is at most the
`k`-th exit-exact mass `J.PexitSum K k h c` (which is what the path measure would give),
then the measure of the union of these events — the exit event — is at most the exit mass
`J.exitMass K c h`, by the identification (★) `J.exitMass_eq_tsum_PexitSum`.

This is the step that turns the exit mass into a bound for a *probability*; the library
still has no path measure, so the measure `μ` and the events `A k` are abstract.
-/
theorem exitMass_union_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (K : Finset α)
    (c : α) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h) (A : ℕ → Set Ω)
    (hA : ∀ k, μ (A k) ≤ ENNReal.ofReal (J.PexitSum K k h c)) :
    μ (⋃ k, A k) ≤ ENNReal.ofReal (J.exitMass K c h) := by
  have hnonneg : ∀ k, 0 ≤ J.PexitSum K k h c := by
    intro k
    refine tsum_nonneg fun b => ?_
    exact J.Pexit_nonneg K k h hh c b
  have hsum : Summable fun k => J.PexitSum K k h c := J.summable_PexitSum K c hc hh
  have hENN : (∑' k, ENNReal.ofReal (J.PexitSum K k h c))
      = ENNReal.ofReal (J.exitMass K c h) := by
    calc
      (∑' k, ENNReal.ofReal (J.PexitSum K k h c))
          = ENNReal.ofReal (∑' k, J.PexitSum K k h c) :=
            (ENNReal.ofReal_tsum_of_nonneg hnonneg hsum).symm
      _ = ENNReal.ofReal (J.exitMass K c h) := by rw [J.exitMass_eq_tsum_PexitSum K c hc hh]
  refine le_trans (MeasureTheory.measure_iUnion_le A) ?_
  rw [← hENN]
  exact ENNReal.tsum_le_tsum fun k => hA k

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **The identification (★) for stochastic mass-action kinetics.** -/
theorem exitMass_eq_tsum_Pexit (N : Network S) (κ : N.RateConstants) (K : Finset (S → ℕ))
    (c : S → ℕ) (hc : c ∈ K) {h : ℝ} (hh : 0 ≤ h) :
    (N.jumpSystem κ).exitMass K c h = ∑' k, ∑' b, (N.jumpSystem κ).Pexit K k h c b :=
  (N.jumpSystem κ).exitMass_eq_tsum_Pexit K c hc hh

/--
**The Markov step (★★★).**

The `i`-th window of the grid exit mass is at least the exit mass of the same window
started from the chain *frozen* outside the set `B_i` at time `t i`.  Indeed the original
chain dominates the frozen chain on the set `B_i` (`JumpSystem.Pmin_stopOutside_le`), and the
exit mass is non-negative; the terms with `c ∉ B_i` are non-negative as well.

This is the deterministic content of the Markov step of the sample-path reading of Kurtz's
law of large numbers: the exit mass of the window is controlled by the frozen chain, which
is the chain that the path measure would have to be compared with.
-/
theorem grid_exitMass_ge_window (N : Network S) (κ : N.RateConstants) (m : ℕ) (t : ℕ → ℝ)
    (h : ℝ) (ht : 0 ≤ h) (hgrid : ∀ i, i < m → 0 ≤ t i) (K : ℕ → Finset (S → ℕ)) (n : S → ℕ)
    (i : ℕ) (hi : i < m) :
    (∑' c, N.transition κ (t i) n c * (N.jumpSystem κ).exitMass (K i) c h) ≥
      ∑ c ∈ K i, ((N.jumpSystem κ).stopOutside (K i)).Pmin (t i) n c *
        (N.jumpSystem κ).exitMass (K i) c h := by
  have hnonneg : ∀ c, 0 ≤ N.transition κ (t i) n c *
      (N.jumpSystem κ).exitMass (K i) c h :=
    fun c => mul_nonneg (N.transition_nonneg κ (hgrid i hi) n c)
      ((N.jumpSystem κ).exitMass_nonneg (K i) c ht)
  have hsumm : Summable fun c => N.transition κ (t i) n c *
      (N.jumpSystem κ).exitMass (K i) c h := by
    refine Summable.of_nonneg_of_le
      (f := fun c => N.transition κ (t i) n c)
      (g := fun c => N.transition κ (t i) n c * (N.jumpSystem κ).exitMass (K i) c h) ?_ ?_ ?_
    · intro c
      exact hnonneg c
    · intro c
      exact le_trans (mul_le_mul_of_nonneg_left ((N.jumpSystem κ).exitMass_le_one (K i) c ht)
        (N.transition_nonneg κ (hgrid i hi) n c)) (by simp)
    · exact summable_of_sum_le (fun c => N.transition_nonneg κ (hgrid i hi) n c)
        (fun F => N.sum_transition_le_one κ (hgrid i hi) n F)
  calc
    (∑' c, N.transition κ (t i) n c * (N.jumpSystem κ).exitMass (K i) c h)
        ≥ ∑ c ∈ K i, N.transition κ (t i) n c * (N.jumpSystem κ).exitMass (K i) c h :=
      Summable.sum_le_tsum (K i) (fun c _ => hnonneg c) hsumm
    _ ≥ ∑ c ∈ K i, ((N.jumpSystem κ).stopOutside (K i)).Pmin (t i) n c *
        (N.jumpSystem κ).exitMass (K i) c h := by
      refine Finset.sum_le_sum fun c hc => ?_
      have hle : ((N.jumpSystem κ).stopOutside (K i)).Pmin (t i) n c ≤
          (N.jumpSystem κ).Pmin (t i) n c :=
        (N.jumpSystem κ).Pmin_stopOutside_le (K i) (hgrid i hi) n hc
      have hEq : (N.jumpSystem κ).Pmin (t i) n c = N.transition κ (t i) n c := rfl
      rw [← hEq]
      exact mul_le_mul_of_nonneg_right hle
        ((N.jumpSystem κ).exitMass_nonneg (K i) c ht)

/-- **The grid version of the Markov step (★★★).** -/
theorem grid_exitMass_ge (N : Network S) (κ : N.RateConstants) (m : ℕ) (t : ℕ → ℝ)
    (h : ℝ) (ht : 0 ≤ h) (hgrid : ∀ i, i < m → 0 ≤ t i) (K : ℕ → Finset (S → ℕ)) (n : S → ℕ) :
    N.grid_exitMass κ m t h K n ≥
      ∑ i ∈ Finset.range m, ∑ c ∈ K i, ((N.jumpSystem κ).stopOutside (K i)).Pmin (t i) n c *
        (N.jumpSystem κ).exitMass (K i) c h := by
  unfold grid_exitMass
  refine Finset.sum_le_sum fun i hi => ?_
  exact (N.grid_exitMass_ge_window κ m t h ht hgrid K n i (Finset.mem_range.mp hi)).ge

end Network

end CRNT
