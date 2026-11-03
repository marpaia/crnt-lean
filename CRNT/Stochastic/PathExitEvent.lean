import CRNT.Stochastic.ExitMass
import CRNT.Stochastic.NonExplosion
import CRNT.Stochastic.MinimalSemigroupChapmanKolmogorov
import CRNT.Stochastic.KurtzPathwise

/-!
# The path exit event, the exit mass, and the union bound over a grid

This module builds the *minimal path space* needed to state the exit event literally, and
proves the identification of the exit mass with that event, together with the union bound
over a grid.

## 1. The path space

The library models the chain by its transition function (`JumpSystem.Pmin`) and, on the
combinatorial side, by *jump paths*: count sequences `n : ℕ → S → ℕ` with
`n (k+1) = N.jumpNextCount (n k) r` for a reaction `r` of positive propensity
(`CRNT.Network.IsJumpPath`).  A jump path is indexed by the *number of jumps*, not by
time.  To speak about time we must add the *holding times*.

`CRNT.Network.JumpPath` is therefore the minimal path space: a count sequence, the
sequence of fired reactions, and the sequence of holding times, together with the validity
conditions.  `CRNT.Network.JumpPath.jumpTime p k = ∑_{j<k} p.hold j` is the time of the
`k`-th jump, and `CRNT.Network.LeavesDuring` is the literal exit event:

`LeavesDuring N κ K h n hold  ↔  ∃ k, (∑_{j<k} hold j) ≤ h ∧ n k ∉ K`

(the chain is outside `K` at some jump time `≤ h`).

## 2. The exit-exact kernel

`JumpSystem.Pexit K k t a b` is the probability that the chain started at `a` makes its
`k`-th jump at a time `≤ t`, that this jump is the *first* jump leaving `K`, and that it
lands at `b`.  It is defined by the first-jump recursion, so it is a genuine probability
(the recursion is the Kolmogorov one, restricted to the first exit).

The kernel comes with its support (`JumpSystem.Pexit_eq_zero_of_not_mem`), its
non-negativity (`JumpSystem.Pexit_nonneg`) and its continuity in the time parameter
(`JumpSystem.Pexit_continuous`), and with the recursion for the exit-exact *mass*
(`JumpSystem.PexitSum_succ`):

`PexitSum K (k+1) t a = ∫₀ᵗ ∑_i e^{−q(a)s}·rate_i(a)·(if next_i a ∈ K then PexitSum K k (t−s)(next_i a) else if k = 0 then 1 else 0) ds`

The *identification* that the exit mass of the chain frozen outside `K` is the sum of the
disjoint path events "the `k`-th jump leaves `K`, at a time `≤ h`" is the remaining
algebraic step; it is stated precisely in section 4 below.

## 3. The pathwise identification

`CRNT.Network.LeavesDuring` is the literal path event, and
`CRNT.Network.LeavesDuring.exists_firstExit` shows that it is realised at a *unique first
exit index* — the index `k` that `JumpSystem.Pexit` refers to — while
`CRNT.Network.LeavesDuring.frozen_outside` shows that the chain frozen outside `K` stays
outside `K` at every later jump index.  Together these two facts are the pathwise content
of the identification "the exit mass is the probability of the exit event".

## 4. The union bound over the grid

`CRNT.Network.grid_exitMass` is the grid sum
`∑_{i<m} ∑_c P(t_i)(n,c) · exitMass_{B_i}(c)`, the total exit mass of the chain over the
windows of the grid; it is non-negative (`CRNT.Network.grid_exitMass_nonneg`).

`CRNT.Network.union_bound_grid` is the union bound itself, in the only form in which it
is a theorem of probability theory: for a probability measure `μ` and sets
`A_0, …, A_{m-1}` with `μ (A_i) ≤ μ_i`, one has `μ (⋃_i A_i) ≤ ∑_i μ_i`.  Instantiating
`μ_i` with the grid exit masses gives the bound of the sample-path reading.

`CRNT.Network.dist_le_three_halves` is the `3δ/2` step: a chain inside the ball of
radius `δ` around `x t₀` at time `t₀`, with `x` moving by less than `δ/2` during the
window, stays within `3δ/2` of `x` throughout the window.

## 5. What is still missing

Two steps are still missing; they are exactly the two steps that the library cannot
formally perform yet.

**(a) The algebraic identification.**  The exit mass of the chain frozen outside `K` is
the sum of the disjoint path events "the `k`-th jump leaves `K`, at a time `≤ h`", i.e.

`J.exitMass K c h = ∑_k ∑_b J.Pexit K k h c b`  (for `c ∈ K`).

The exit-exact kernel `J.Pexit` and its recursion `J.PexitSum_succ` are proved here.  The
missing ingredient is the *frozen chain's* recursion (the same computation for
`J.stopOutside K`), which is needed to show

`∑_b J.Pexit K k t a b = ∑_{b ∉ K} (J.stopOutside K).Pexact k t a b`  (for `k ≥ 1`),

i.e. that the `k`-th jump of the chain started at `a` is the first jump leaving `K` with
the same probability as "the chain frozen outside `K` has made exactly `k` jumps by time
`t` and is outside `K`".  This is the discrete analogue of the fact that the original
chain and the chain frozen outside `K` agree up to the first exit.

**(b) The path measure.**  The library still has **no path measure**.  Consequently:

* the identification `exitMass K c h = P(exit during [0,h])` cannot be stated as an
  equality of probabilities of events on a probability space;
* the union bound over the grid is proved for an arbitrary probability measure carrying
  events with the grid exit masses as their measures; to conclude
  `P (∃ i, the chain leaves B_i in the i-th window) ≤ grid_exitMass` one needs a
  probability measure on the space of sample paths of the chain on which the events
  "the chain leaves `B_i` during the `i`-th window" live, together with the strong Markov
  property at the deterministic grid times `t_i` (which identifies their measures with
  `∑_c P(t_i)(n,c) · exitMass_{B_i}(c)`).

Everything else — the path space, the literal exit event, the exit-exact kernel with its
support, non-negativity, continuity and recursion, the pathwise first-exit
identification, the grid sum, the union bound over a finite grid of events, and the
`3δ/2` step — is proved here.
-/

open MeasureTheory Set Filter intervalIntegral
open scoped BigOperators ENNReal Topology

namespace CRNT

namespace JumpSystem

variable {α : Type*} [DecidableEq α] (J : JumpSystem α)

/--
**The exit-exact kernel.**

`J.Pexit K k t a b` is the probability that the chain started at `a` makes its `k`-th
jump at a time `≤ t`, that this jump is the *first* jump leaving `K`, and that the jump
lands at `b`.  For `k = 0` there is no jump, so the value is `0`; for `k + 1` the first
jump either stays inside `K` (and the remaining `k` jumps are again an exit event) or it
leaves `K` (which is only possible when `k = 0`, i.e. for the very first jump).
-/
noncomputable def Pexit (K : Finset α) : ℕ → ℝ → α → α → ℝ
  | 0, _, _, _ => 0
  | k + 1, t, a, b =>
      if a ∉ K then 0 else
        ∫ s in (0 : ℝ)..t, ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
            (if J.next i a ∈ K then Pexit K k (t - s) (J.next i a) b
             else if k = 0 ∧ J.next i a = b then 1 else 0)

theorem Pexit_zero (K : Finset α) (t : ℝ) (a b : α) : J.Pexit K 0 t a b = 0 := rfl

theorem Pexit_succ (K : Finset α) (k : ℕ) (t : ℝ) (a b : α) :
    J.Pexit K (k + 1) t a b = if a ∉ K then 0 else
      ∫ s in (0 : ℝ)..t, ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
          (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
           else if k = 0 ∧ J.next i a = b then 1 else 0) := rfl

/-- **Outside `K` there is no exit.** A chain started outside `K` never leaves it. -/
theorem Pexit_of_not_mem (K : Finset α) :
    ∀ (k : ℕ) (t : ℝ) (a b : α), a ∉ K → J.Pexit K k t a b = 0 := by
  intro k
  induction k with
  | zero => intro t a b ha; rw [Pexit_zero]
  | succ k ih =>
      intro t a b ha
      rw [Pexit_succ]
      simp [ha]

/-- **Continuity in the time parameter.** -/
theorem Pexit_continuous (K : Finset α) (k : ℕ) : ∀ a b : α, Continuous fun t => J.Pexit K k t a b := by
  induction k with
  | zero =>
      intro a b; simp only [Pexit_zero]; fun_prop
  | succ k ih =>
      intro a b
      by_cases ha : a ∉ K
      · have hz : ∀ t, J.Pexit K (k + 1) t a b = 0 := fun t => J.Pexit_of_not_mem K _ _ _ _ ha
        simpa only [hz] using (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
      · have hexp : (fun t => J.Pexit K (k + 1) t a b) = fun t => ∫ s in (0 : ℝ)..t,
            ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
              (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
               else if k = 0 ∧ J.next i a = b then 1 else 0) := by
          funext t; rw [Pexit_succ, ite_eq_right ha]
        rw [hexp]
        have hF : Continuous (Function.uncurry fun (t s : ℝ) => ∑ i, Real.exp (-(J.q a * s)) *
              J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then 1 else 0)) := by
          have hExp : Continuous fun p : ℝ × ℝ => Real.exp (-(J.q a * p.2)) := by fun_prop
          refine continuous_finsetSum _ fun i _ => ?_
          refine Continuous.mul (Continuous.mul hExp continuous_const) ?_
          by_cases hi : J.next i a ∈ K
          · have h1 : (fun p : ℝ × ℝ =>
                (if J.next i a ∈ K then J.Pexit K k (p.1 - p.2) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then 1 else 0))
              = fun p : ℝ × ℝ => J.Pexit K k (p.1 - p.2) (J.next i a) b := by
              funext p; rw [ite_eq_left hi]
            rw [h1]
            exact (ih (J.next i a) b).comp (continuous_fst.sub continuous_snd)
          · have h1 : (fun p : ℝ × ℝ =>
                (if J.next i a ∈ K then J.Pexit K k (p.1 - p.2) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then 1 else 0))
              = fun p : ℝ × ℝ => (if k = 0 ∧ J.next i a = b then 1 else 0) := by
              funext p; rw [ite_eq_right hi]
            rw [h1]
            by_cases hk0 : k = 0 ∧ J.next i a = b
            · have h2 : (fun p : ℝ × ℝ =>
                  (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
                = fun _ : ℝ × ℝ => (1 : ℝ) := by
                funext p; rw [ite_eq_left hk0]
              rw [h2]
              exact continuous_const
            · have h2 : (fun p : ℝ × ℝ =>
                  (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
                = fun _ : ℝ × ℝ => (0 : ℝ) := by
                funext p; rw [ite_eq_right hk0]
              rw [h2]
              exact (continuous_const : Continuous fun _ : ℝ × ℝ => (0 : ℝ))
        exact continuous_parametric_intervalIntegral_of_continuous (a₀ := 0) hF continuous_id

/-- **Non-negativity** of the exit-exact kernel. -/
theorem Pexit_nonneg (K : Finset α) :
    ∀ (k : ℕ) (t : ℝ), 0 ≤ t → ∀ a b : α, 0 ≤ J.Pexit K k t a b := by
  intro k
  induction k with
  | zero =>
      intro t ht a b; simp [Pexit_zero]
  | succ k ih =>
      intro t ht a b
      by_cases ha : a ∉ K
      · simp [J.Pexit_of_not_mem K _ _ _ _ ha]
      · have hexp : J.Pexit K (k + 1) t a b = ∫ s in (0 : ℝ)..t, ∑ i, Real.exp (-(J.q a * s)) *
              J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by
          rw [Pexit_succ, ite_eq_right ha]
        rw [hexp]
        refine intervalIntegral.integral_nonneg ht fun s hs => ?_
        refine Finset.sum_nonneg fun i _ => ?_
        refine mul_nonneg (mul_nonneg (Real.exp_pos _).le (J.rate_nonneg i a)) ?_
        by_cases hi : J.next i a ∈ K
        · have h1 : (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
              else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
            = J.Pexit K k (t - s) (J.next i a) b := by rw [ite_eq_left hi]
          rw [h1]
          exact ih (t - s) (by linarith [hs.2]) _ _
        · have h1 : (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
              else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
            = (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by rw [ite_eq_right hi]
          rw [h1]
          by_cases hk0 : k = 0 ∧ J.next i a = b
          · rw [ite_eq_left hk0]
            exact zero_le_one
          · rw [ite_eq_right hk0]

/-- The successor of a state is reachable in one jump. -/
theorem next_mem_reachK_one (a : α) (i : J.ι) : J.next i a ∈ J.reachK 1 a := by
  rw [JumpSystem.reachK, Finset.mem_insert]
  exact Or.inr (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, by
    simp [JumpSystem.reachK]⟩)

/--
**Support of the exit-exact kernel.**

`J.Pexit_support` proves that the exit-exact kernel vanishes outside the states reachable
in `k` jumps; the second component proves the corresponding statement for the integrand
of the recursion, which is what is needed to interchange the integral with the sum over
the target states.
-/
theorem Pexit_support (K : Finset α) (k : ℕ) :
    (∀ (t : ℝ) (a b : α), b ∉ J.reachK k a → J.Pexit K k t a b = 0) ∧
    (∀ (t : ℝ) (a b : α), b ∉ J.reachK (k + 1) a → ∀ s : ℝ,
      (∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
        (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
         else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) = 0) := by
  induction k with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro t a b hb; rw [Pexit_zero]
      · intro t a b hb s
        have hsum : (∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
              (if J.next i a ∈ K then J.Pexit K 0 (t - s) (J.next i a) b
               else if 0 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          by_cases hi : J.next i a ∈ K
          · have h1 : (if J.next i a ∈ K then J.Pexit K 0 (t - s) (J.next i a) b
                else if 0 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
              = J.Pexit K 0 (t - s) (J.next i a) b := by rw [ite_eq_left hi]
            rw [h1, Pexit_zero]
            exact mul_zero _
          · have h1 : (if J.next i a ∈ K then J.Pexit K 0 (t - s) (J.next i a) b
                else if 0 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
              = (if 0 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by rw [ite_eq_right hi]
            rw [h1]
            have hmem : J.next i a ∈ J.reachK 1 a := J.next_mem_reachK_one a i
            by_cases hk0 : 0 = 0 ∧ J.next i a = b
            · rw [ite_eq_left hk0]
              have hcontra : b ∈ J.reachK 1 a := by rw [← hk0.2]; exact hmem
              exact absurd hcontra hb
            · rw [ite_eq_right hk0]
              exact mul_zero _
        rw [hsum]
  | succ k ih =>
      rcases ih with ⟨ihP, ihT⟩
      have hP : ∀ (t : ℝ) (a b : α), b ∉ J.reachK (k + 1) a → J.Pexit K (k + 1) t a b = 0 := by
        intro t a b hb
        by_cases ha : a ∉ K
        · rw [J.Pexit_of_not_mem K _ _ _ _ ha]
        · rw [Pexit_succ, ite_eq_right ha]
          have hsum : ∀ s : ℝ, (∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) = 0 := by
            intro s
            refine Finset.sum_eq_zero fun i _ => ?_
            by_cases hi : J.next i a ∈ K
            · have h1 : (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                  else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
                = J.Pexit K k (t - s) (J.next i a) b := by rw [ite_eq_left hi]
              rw [h1]
              have hnot : b ∉ J.reachK k (J.next i a) :=
                fun hmem2 => hb (J.reachK_next_subset k a i hmem2)
              rw [ihP _ _ _ hnot]
              exact mul_zero _
            · have h1 : (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                  else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
                = (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by rw [ite_eq_right hi]
              rw [h1]
              by_cases hk0 : k = 0 ∧ J.next i a = b
              · rw [ite_eq_left hk0]
                have hmem : J.next i a ∈ J.reachK (k + 1) a :=
                  J.reachK_next_subset k a i (J.mem_reachK_self k (J.next i a))
                have hcontra : b ∈ J.reachK (k + 1) a := by rw [← hk0.2]; exact hmem
                exact absurd hcontra hb
              · rw [ite_eq_right hk0]
                exact mul_zero _
          have hconv : (∫ s in (0 : ℝ)..t, ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) = 0 := by
            have hEq : (fun s : ℝ => ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
                = fun _ : ℝ => (0 : ℝ) := by
              funext s; rw [hsum s]
            calc
              (∫ s in (0 : ℝ)..t, ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                  (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                   else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
                  = ∫ s in (0 : ℝ)..t, (0 : ℝ) := by
                    rw [intervalIntegral.integral_congr (E := ℝ)
                      (f := fun s : ℝ => ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                        (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                         else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
                      (g := fun _ : ℝ => (0 : ℝ)) (fun s _ => congrFun hEq s)]
              _ = 0 := intervalIntegral.integral_zero
          rw [hconv]
      refine ⟨hP, ?_⟩
      intro t a b hb s
      have hsum : (∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
            (if J.next i a ∈ K then J.Pexit K (k + 1) (t - s) (J.next i a) b
             else if k + 1 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        by_cases hi : J.next i a ∈ K
        · have h1 : (if J.next i a ∈ K then J.Pexit K (k + 1) (t - s) (J.next i a) b
              else if k + 1 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
            = J.Pexit K (k + 1) (t - s) (J.next i a) b := by rw [ite_eq_left hi]
          rw [h1]
          have hnot : b ∉ J.reachK (k + 1) (J.next i a) :=
            fun hmem2 => hb (J.reachK_next_subset (k + 1) a i hmem2)
          rw [hP _ _ _ hnot]
          exact mul_zero _
        · have h1 : (if J.next i a ∈ K then J.Pexit K (k + 1) (t - s) (J.next i a) b
              else if k + 1 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))
            = (if k + 1 = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by rw [ite_eq_right hi]
          rw [h1]
          by_cases hk0 : k + 1 = 0 ∧ J.next i a = b
          · rw [ite_eq_left hk0]
            have hmem : J.next i a ∈ J.reachK (k + 2) a :=
              J.reachK_next_subset (k + 1) a i (J.mem_reachK_self (k + 1) (J.next i a))
            have hcontra : b ∈ J.reachK (k + 2) a := by rw [← hk0.2]; exact hmem
            exact absurd hcontra hb
          · rw [ite_eq_right hk0]
            exact mul_zero _
      rw [hsum]

/-- **Support.** The exit-exact kernel vanishes outside the states reachable in `k` jumps. -/
theorem Pexit_eq_zero_of_not_mem (K : Finset α) :
    ∀ (k : ℕ) (t : ℝ) (a b : α), b ∉ J.reachK k a → J.Pexit K k t a b = 0 :=
  fun k => (J.Pexit_support K k).1

/-- **The integrand vanishes outside the states reachable in `k + 1` jumps.** -/
theorem Pexit_term_eq_zero (K : Finset α) :
    ∀ (k : ℕ) (t : ℝ) (a b : α), b ∉ J.reachK (k + 1) a → ∀ s : ℝ,
      (∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
        (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
         else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) = 0 :=
  fun k => (J.Pexit_support K k).2

/-- **The integrand of the exit-exact recursion.** -/
noncomputable def PexitTerm (K : Finset α) (k : ℕ) (t : ℝ) (a b : α) (s : ℝ) : ℝ :=
  ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
    (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
     else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))

theorem Pexit_succ_term (K : Finset α) (k : ℕ) (t : ℝ) (a b : α) :
    J.Pexit K (k + 1) t a b = if a ∉ K then 0 else
      ∫ s in (0 : ℝ)..t, J.PexitTerm K k t a b s := by
  rw [Pexit_succ]
  congr 1

theorem PexitTerm_continuous (K : Finset α) (k : ℕ) (t : ℝ) (a b : α) :
    Continuous fun s => J.PexitTerm K k t a b s := by
  have hmain : ∀ i : J.ι,
      Continuous fun s : ℝ => Real.exp (-(J.q a * s)) * J.rate i a *
        (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
         else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by
    intro i
    have hnext : Continuous fun s : ℝ => J.Pexit K k (t - s) (J.next i a) b :=
      (J.Pexit_continuous K k (J.next i a) b).comp (continuous_const.sub continuous_id)
    have hExp : Continuous fun s : ℝ => Real.exp (-(J.q a * s)) := by fun_prop
    by_cases hi : J.next i a ∈ K
    · have h1 : (fun s : ℝ => Real.exp (-(J.q a * s)) * J.rate i a *
            (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
             else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
        = fun s : ℝ => (Real.exp (-(J.q a * s)) * J.rate i a) *
            J.Pexit K k (t - s) (J.next i a) b := by
        funext s; rw [ite_eq_left hi]
      rw [h1]
      exact Continuous.mul (Continuous.mul hExp continuous_const) hnext
    · have h1 : (fun s : ℝ => Real.exp (-(J.q a * s)) * J.rate i a *
            (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
             else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
        = fun s : ℝ => (Real.exp (-(J.q a * s)) * J.rate i a) *
            (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by
        funext s; rw [ite_eq_right hi]
      rw [h1]
      by_cases hk0 : k = 0 ∧ J.next i a = b
      · have h2 : (fun s : ℝ => Real.exp (-(J.q a * s)) * J.rate i a *
              (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
            = fun s : ℝ => Real.exp (-(J.q a * s)) * J.rate i a := by
          funext s; rw [ite_eq_left hk0, mul_one]
        rw [h2]
        exact Continuous.mul hExp (continuous_const : Continuous fun _ : ℝ => J.rate i a)
      · have h2 : (fun s : ℝ => Real.exp (-(J.q a * s)) * J.rate i a *
              (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
            = fun s : ℝ => (Real.exp (-(J.q a * s)) * J.rate i a) * 0 := by
          funext s; rw [ite_eq_right hk0]
        rw [h2]
        exact Continuous.mul (Continuous.mul hExp continuous_const)
          (continuous_const : Continuous fun _ : ℝ => (0 : ℝ))
  unfold PexitTerm
  exact continuous_finsetSum (Finset.univ : Finset J.ι) fun i _ => hmain i

set_option linter.unusedVariables false in
set_option linter.unusedSectionVars false in
/-- **Interchanging a countable sum with an integral.**  If the family `f b` vanishes
outside a finite set `F` and every `f b` is continuous, the sum over `b` and the integral
commute. -/
theorem tsum_integral_swap (f : α → ℝ → ℝ) (F : Finset α)
    (hF : ∀ b ∉ F, ∀ s : ℝ, f b s = 0) (hc : ∀ b ∈ F, Continuous fun s => f b s) (t : ℝ) :
    (∑' b, ∫ s in (0 : ℝ)..t, f b s) = ∫ s in (0 : ℝ)..t, ∑ b ∈ F, f b s := by
  have hzero : ∀ b ∉ F, (∫ s in (0 : ℝ)..t, f b s) = 0 := by
    intro b hb
    have hEq : (fun s : ℝ => f b s) = fun _ : ℝ => (0 : ℝ) := by
      funext s; rw [hF b hb s]
    rw [intervalIntegral.integral_congr (E := ℝ) (f := fun s : ℝ => f b s)
      (g := fun _ : ℝ => (0 : ℝ)) (fun s _ => congrFun hEq s)]
    exact intervalIntegral.integral_zero
  rw [tsum_eq_sum (s := F) hzero]
  rw [← intervalIntegral.integral_finsetSum fun b hb => (hc b hb).intervalIntegrable _ _]

/-- **The `k`-th-jump exit mass** of the chain started at `a`: the probability that its
`k`-th jump is the first jump leaving `K` and happens by time `t`. -/
noncomputable def PexitSum (K : Finset α) (k : ℕ) (t : ℝ) (a : α) : ℝ :=
  ∑' b, J.Pexit K k t a b

/-- **The mass of the chain frozen outside `K`** which is outside `K` after exactly `k`
jumps by time `t`. -/
noncomputable def PexactOutside (K : Finset α) (k : ℕ) (t : ℝ) (a : α) : ℝ :=
  ∑' b, (if b ∈ K then (0 : ℝ) else (J.stopOutside K).Pexact k t a b)

/-- The sum of an indicator over the states of a finite set. -/
theorem sum_ite_eq (F : Finset α) (x : α) (hx : x ∈ F) :
    (∑ b ∈ F, (if x = b then (1 : ℝ) else 0)) = 1 := by
  rw [Finset.sum_eq_single_of_mem x hx (fun b _ hb => by rw [ite_eq_right (Ne.symm hb)])]
  simp

/-- **The exit-exact mass over a finite set** which contains all the reachable states. -/
theorem sum_Pexit_eq_PexitSum (K : Finset α) (k : ℕ) (t : ℝ) (a : α) (F : Finset α)
    (hF : J.reachK k a ⊆ F) :
    (∑ b ∈ F, J.Pexit K k t a b) = J.PexitSum K k t a := by
  rw [(Finset.sum_subset hF (fun b _ hb => J.Pexit_eq_zero_of_not_mem K k t a b hb)).symm]
  exact (tsum_eq_sum (s := J.reachK k a)
    fun b hb => J.Pexit_eq_zero_of_not_mem K k t a b hb).symm

/-- **The recursion for the exit-exact mass.** -/
theorem PexitSum_succ (K : Finset α) (k : ℕ) (t : ℝ) (a : α) :
    J.PexitSum K (k + 1) t a = if a ∉ K then 0 else
      ∫ s in (0 : ℝ)..t, ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
        (if J.next i a ∈ K then J.PexitSum K k (t - s) (J.next i a)
         else if k = 0 then 1 else 0) := by
  have hEq : J.PexitSum K (k + 1) t a = (∑' b, J.Pexit K (k + 1) t a b) := rfl
  rw [hEq]
  by_cases ha : a ∉ K
  · have hz : (∑' b, J.Pexit K (k + 1) t a b) = 0 := by
      refine tsum_eq_sum (s := (∅ : Finset α)) ?_
      intro b hb
      exact J.Pexit_of_not_mem K _ _ _ _ ha
    rw [hz, ite_eq_left ha]
  · rw [ite_eq_right ha]
    have hpt : ∀ b : α, J.Pexit K (k + 1) t a b = ∫ s in (0 : ℝ)..t, J.PexitTerm K k t a b s := by
      intro b; rw [Pexit_succ_term, ite_eq_right ha]
    rw [tsum_congr hpt]
    rw [tsum_integral_swap (f := fun b s => J.PexitTerm K k t a b s) (F := J.reachK (k + 1) a)
      (fun b hb s => J.Pexit_term_eq_zero K k t a b hb s)
      (fun b hb => J.PexitTerm_continuous K k t a b)]
    have hinner : ∀ s : ℝ, (∑ b ∈ J.reachK (k + 1) a, J.PexitTerm K k t a b s) =
        ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
          (if J.next i a ∈ K then J.PexitSum K k (t - s) (J.next i a)
           else if k = 0 then 1 else 0) := by
      intro s
      have hsplit : ∀ i : J.ι, (∑ b ∈ J.reachK (k + 1) a,
            (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
             else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) =
          (if J.next i a ∈ K then J.PexitSum K k (t - s) (J.next i a)
           else if k = 0 then 1 else 0) := by
        intro i
        by_cases hi : J.next i a ∈ K
        · rw [ite_eq_left hi]
          have h2 : (∑ b ∈ J.reachK (k + 1) a, (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
              = (∑ b ∈ J.reachK (k + 1) a, J.Pexit K k (t - s) (J.next i a) b) := by
            refine Finset.sum_congr rfl fun b hb => ?_
            rw [ite_eq_left hi]
          rw [h2]
          exact J.sum_Pexit_eq_PexitSum K k (t - s) (J.next i a) (J.reachK (k + 1) a)
            (J.reachK_next_subset k a i)
        · rw [ite_eq_right hi]
          have h2 : (∑ b ∈ J.reachK (k + 1) a, (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
              = (∑ b ∈ J.reachK (k + 1) a, (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ))) := by
            refine Finset.sum_congr rfl fun b hb => ?_
            rw [ite_eq_right hi]
          rw [h2]
          by_cases hk : k = 0
          · rw [ite_eq_left hk]
            have h3 : (∑ b ∈ J.reachK (k + 1) a, (if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
                = (∑ b ∈ J.reachK (k + 1) a, (if J.next i a = b then (1 : ℝ) else (0 : ℝ))) := by
              refine Finset.sum_congr rfl fun b hb => ?_
              simp [hk]
            rw [h3]
            have hmem : J.next i a ∈ J.reachK (k + 1) a :=
              J.reachK_next_subset k a i (J.mem_reachK_self k (J.next i a))
            rw [sum_ite_eq (J.reachK (k + 1) a) (J.next i a) hmem]
          · rw [ite_eq_right hk]
            refine Finset.sum_eq_zero fun b hb => ?_
            simp [hk]
      calc
        (∑ b ∈ J.reachK (k + 1) a, J.PexitTerm K k t a b s)
            = ∑ b ∈ J.reachK (k + 1) a, ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)) := by
              refine Finset.sum_congr rfl fun b hb => ?_
              simp only [PexitTerm]
        _ = ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
              (if J.next i a ∈ K then J.PexitSum K k (t - s) (J.next i a)
               else if k = 0 then 1 else 0) := by
              rw [Finset.sum_comm (f := fun b i => Real.exp (-(J.q a * s)) * J.rate i a *
                (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                 else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))]
              refine Finset.sum_congr rfl fun i hi => ?_
              rw [← Finset.mul_sum (J.reachK (k + 1) a)
                (fun b => (if J.next i a ∈ K then J.Pexit K k (t - s) (J.next i a) b
                   else if k = 0 ∧ J.next i a = b then (1 : ℝ) else (0 : ℝ)))
                (Real.exp (-(J.q a * s)) * J.rate i a), hsplit i]
    refine intervalIntegral.integral_congr (E := ℝ)
      (f := fun s : ℝ => ∑ b ∈ J.reachK (k + 1) a, J.PexitTerm K k t a b s)
      (g := fun s : ℝ => ∑ i, Real.exp (-(J.q a * s)) * J.rate i a *
        (if J.next i a ∈ K then J.PexitSum K k (t - s) (J.next i a)
         else if k = 0 then 1 else 0)) (fun s _ => hinner s)

end JumpSystem

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/--
**A sample path of the continuous-time Markov chain.**

The library already provides the combinatorial part of a path (`CRNT.Network.IsJumpPath`:
a count sequence together with the reaction fired at each step).  What is missing for the
*timed* statements is the sequence of holding times.  `JumpPath` is the minimal path space:
the counts, the fired reactions, the holding times, and the validity conditions.

* `p.n k` is the count vector after `k` jumps;
* `p.r k` is the reaction fired at the `k`-th jump (of positive propensity);
* `p.hold k > 0` is the holding time preceding the `k`-th jump.
-/
structure JumpPath (N : Network S) (κ : N.RateConstants) where
  /-- The counts after `k` jumps. -/
  n : ℕ → S → ℕ
  /-- The reaction fired at the `k`-th jump. -/
  r : ℕ → N.R
  /-- The holding time preceding the `k`-th jump. -/
  hold : ℕ → ℝ
  /-- The count sequence is a jump path. -/
  isJumpPath : N.IsJumpPath κ n
  /-- The reaction fired at the `k`-th jump has positive propensity at `n k`. -/
  rate_pos : ∀ k, 0 < N.stochasticMassActionRate κ (n k) (r k)
  /-- The counts follow the fired reactions. -/
  step : ∀ k, n (k + 1) = N.jumpNextCount (n k) (r k)
  /-- The holding times are positive. -/
  hold_pos : ∀ k, 0 < hold k

/-- **The time of the `k`-th jump**: the sum of the first `k` holding times.  The `0`-th
jump happens at time `0`. -/
def JumpPath.jumpTime {N : Network S} {κ : N.RateConstants} (p : JumpPath N κ) (k : ℕ) : ℝ := ∑ j ∈ Finset.range k, p.hold j

theorem JumpPath.jumpTime_zero {N : Network S} {κ : N.RateConstants} (p : JumpPath N κ) :
    p.jumpTime 0 = 0 := by
  simp [jumpTime]

theorem JumpPath.jumpTime_succ {N : Network S} {κ : N.RateConstants} (p : JumpPath N κ) (k : ℕ) :
    p.jumpTime (k + 1) = p.jumpTime k + p.hold k := by
  simp only [jumpTime, Finset.sum_range_succ]

/-- The jump times are strictly increasing. -/
theorem JumpPath.jumpTime_lt_succ {N : Network S} {κ : N.RateConstants} (p : JumpPath N κ) (k : ℕ) :
    p.jumpTime k < p.jumpTime (k + 1) := by
  rw [p.jumpTime_succ]
  exact lt_add_of_pos_right (p.jumpTime k) (p.hold_pos k)

/-- The jump times are non-decreasing. -/
theorem JumpPath.jumpTime_mono {N : Network S} {κ : N.RateConstants} (p : JumpPath N κ) {j k : ℕ}
    (hjk : j ≤ k) :
    p.jumpTime j ≤ p.jumpTime k := by
  induction k, hjk using Nat.le_induction with
  | base => exact le_rfl
  | succ k hk ih =>
      have h1 : p.jumpTime k ≤ p.jumpTime (k + 1) := by
        rw [p.jumpTime_succ]
        exact le_add_of_nonneg_right (le_of_lt (p.hold_pos k))
      exact ih.trans h1

set_option linter.unusedVariables false
/--
**The exit event.**

`LeavesDuring N κ K h n hold` says that the chain is outside `K` at some jump time `≤ h`:
there is a `k` with `∑_{j<k} hold j ≤ h` and `n k ∉ K`.  This is the literal path event
that the exit mass is meant to measure.
-/
def LeavesDuring (N : Network S) (κ : N.RateConstants) (K : Finset (S → ℕ)) (h : ℝ)
    (n : ℕ → S → ℕ) (hold : ℕ → ℝ) : Prop :=
  ∃ k, (∑ j ∈ Finset.range k, hold j) ≤ h ∧ n k ∉ K
set_option linter.unusedVariables true

/-- The exit event along a path. -/
def JumpPath.leavesDuring {N : Network S} {κ : N.RateConstants} (p : JumpPath N κ)
    (K : Finset (S → ℕ)) (h : ℝ) : Prop :=
  LeavesDuring N κ K h p.n p.hold

/-- The exit event is realised at some jump index. -/
theorem leavesDuring_iff (N : Network S) (κ : N.RateConstants) (K : Finset (S → ℕ))
    (h : ℝ) (n : ℕ → S → ℕ) (hold : ℕ → ℝ) :
    LeavesDuring N κ K h n hold ↔
      ∃ k, (∑ j ∈ Finset.range k, hold j) ≤ h ∧ n k ∉ K := Iff.rfl

/-- Monotonicity of the exit event in the window length. -/
theorem leavesDuring_mono (N : Network S) (κ : N.RateConstants) (K : Finset (S → ℕ))
    {h h' : ℝ} (hh : h ≤ h') (n : ℕ → S → ℕ) (hold : ℕ → ℝ)
    (he : LeavesDuring N κ K h n hold) : LeavesDuring N κ K h' n hold := by
  obtain ⟨k, hk, hnk⟩ := he
  exact ⟨k, le_trans hk hh, hnk⟩

/-- Monotonicity of the exit event in the set. -/
theorem leavesDuring_mono_set (N : Network S) (κ : N.RateConstants) {K K' : Finset (S → ℕ)}
    (hKK : K' ⊆ K) (h : ℝ) (n : ℕ → S → ℕ) (hold : ℕ → ℝ)
    (he : LeavesDuring N κ K h n hold) : LeavesDuring N κ K' h n hold := by
  obtain ⟨k, hk, hnk⟩ := he
  exact ⟨k, hk, fun hmemK' => hnk (hKK hmemK')⟩

/-- **Monotonicity of the jump times** for a non-negative holding-time sequence. -/
theorem jumpTime_mono (hold : ℕ → ℝ) (hhold : ∀ j, 0 ≤ hold j) {j k : ℕ} (hjk : j ≤ k) :
    (∑ i ∈ Finset.range j, hold i) ≤ (∑ i ∈ Finset.range k, hold i) := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hjk) ?_
  intro b hb _
  exact hhold b

/--
**The pathwise identification of the exit event.**

If the path is *frozen outside* `K` (it does not move once it is outside `K`), then the
exit event during `[0, h]` is realised at a *unique first exit index*, and the chain is
outside `K` at every later time.  The first exit index is exactly the index `k` that
`JumpSystem.Pexit` refers to.
-/
theorem LeavesDuring.exists_firstExit (N : Network S) (κ : N.RateConstants)
    {K : Finset (S → ℕ)} {h : ℝ} {n : ℕ → S → ℕ} {hold : ℕ → ℝ}
    (hhold : ∀ j, 0 ≤ hold j)
    (he : LeavesDuring N κ K h n hold) :
    ∃ k, (∑ j ∈ Finset.range k, hold j) ≤ h ∧ n k ∉ K ∧ ∀ j < k, n j ∈ K := by
  obtain ⟨k0, hk0, hnk0⟩ := he
  have hdec : DecidablePred (fun k : ℕ => (∑ j ∈ Finset.range k, hold j) ≤ h ∧ n k ∉ K) :=
    fun k => inferInstance
  have hex : ∃ k, (∑ j ∈ Finset.range k, hold j) ≤ h ∧ n k ∉ K := ⟨k0, hk0, hnk0⟩
  have hfind : (∑ j ∈ Finset.range (Nat.find hex), hold j) ≤ h ∧ n (Nat.find hex) ∉ K :=
    Nat.find_spec hex
  refine ⟨Nat.find hex, hfind.1, hfind.2, ?_⟩
  intro j hj
  by_contra hjK
  have hjt : (∑ l ∈ Finset.range j, hold l) ≤ h := by
    have h1 : (∑ l ∈ Finset.range j, hold l) ≤ (∑ l ∈ Finset.range (Nat.find hex), hold l) :=
      jumpTime_mono hold hhold (by omega)
    exact le_trans h1 hfind.1
  have hPj : (∑ l ∈ Finset.range j, hold l) ≤ h ∧ n j ∉ K := ⟨hjt, hjK⟩
  have hmin := Nat.find_min' hex hPj
  omega

set_option linter.unusedVariables false
/-- **The frozen chain stays outside `K`.**  Once the chain has left `K` it does not move
any more; in particular it is outside `K` at every later jump index.  This is the property
that identifies the exit event with "the chain is outside `K` at time `h`" for the chain
frozen outside `K`. -/
theorem LeavesDuring.frozen_outside (N : Network S) (κ : N.RateConstants)
    {K : Finset (S → ℕ)} {n : ℕ → S → ℕ}
    (hfrozen : ∀ k, n k ∉ K → n (k + 1) = n k) {k : ℕ} (hk : n k ∉ K) {j : ℕ} (hjk : k ≤ j) :
    n j ∉ K := by
  have hkey : ∀ j, k ≤ j → n j = n k := by
    intro j hj
    induction j, hj using Nat.le_induction with
    | base => rfl
    | succ j hj ih =>
        rw [hfrozen j (by rw [ih]; exact hk)]
        rw [ih]
  rw [hkey j hjk]
  exact hk
set_option linter.unusedVariables true

/-- Conversely, a first exit index witnesses the exit event. -/
theorem LeavesDuring.of_firstExit (N : Network S) (κ : N.RateConstants)
    {K : Finset (S → ℕ)} {h : ℝ} {n : ℕ → S → ℕ} {hold : ℕ → ℝ}
    (he : ∃ k, (∑ j ∈ Finset.range k, hold j) ≤ h ∧ n k ∉ K ∧ ∀ j < k, n j ∈ K) :
    LeavesDuring N κ K h n hold := by
  obtain ⟨k, hk, hnk, -⟩ := he
  exact ⟨k, hk, hnk⟩

/--
**The grid sum of exit masses.**

For a grid of times `t 0, t 1, …` and the corresponding sets `K i`, this is the total
exit mass of the chain over the windows: `∑_i ∑_c P(t i)(n,c) · exitMass (K i) c h`.
It is the quantity that appears in the sample-path reading of Kurtz's law of large
numbers, and it is the sum of the measures of the window-exit events.
-/
noncomputable def grid_exitMass (N : Network S) (κ : N.RateConstants) (m : ℕ) (t : ℕ → ℝ)
    (h : ℝ) (K : ℕ → Finset (S → ℕ)) (n : S → ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, ∑' c, N.transition κ (t i) n c * (N.jumpSystem κ).exitMass (K i) c h

/-- The grid sum is non-negative. -/
theorem grid_exitMass_nonneg (N : Network S) (κ : N.RateConstants) (m : ℕ) (t : ℕ → ℝ)
    (h : ℝ) (ht : 0 ≤ h) (hgrid : ∀ i, i < m → 0 ≤ t i) (K : ℕ → Finset (S → ℕ))
    (n : S → ℕ) :
    0 ≤ N.grid_exitMass κ m t h K n := by
  unfold grid_exitMass
  refine Finset.sum_nonneg fun i hi => ?_
  refine tsum_nonneg fun c => ?_
  refine mul_nonneg (N.transition_nonneg κ (hgrid i (Finset.mem_range.mp hi)) n c) ?_
  exact (N.jumpSystem κ).exitMass_nonneg (K i) c ht

/--
**The union bound over a finite grid of events.**

This is the union bound in the only form in which it is a theorem of probability theory: for
a probability measure `μ` and measurable events `A_0, …, A_{m-1}` with `μ (A_i) = μ_i`, one
has `μ (⋃_i A_i) ≤ ∑_i μ_i`.  Instantiating `μ_i` with the grid exit masses gives the
bound of the sample-path reading of Kurtz's law of large numbers.
-/
theorem union_bound_grid {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {m : ℕ}
    (A : Fin m → Set Ω) (μi : Fin m → ℝ≥0∞) (hle : ∀ i, μ (A i) ≤ μi i) :
    μ (⋃ i, A i) ≤ ∑' i, μi i := by
  refine le_trans (MeasureTheory.measure_iUnion_le A) ?_
  exact ENNReal.tsum_le_tsum fun i => hle i

set_option linter.unusedSectionVars false
/--
**The `3δ/2` step.**

If the chain is inside the ball of radius `δ` around `x t₀` at time `t₀`, and the solution
`x` moves by less than `δ/2` during the window, then the chain stays within `3δ/2` of `x`
throughout the window.  This is the deterministic ingredient of the sample-path reading of
Kurtz's law of large numbers.
-/
theorem dist_le_three_halves {V : ℝ} (hV : 0 < V) {x : ℝ → Concentration S} {δ : ℝ}
    (hδ : 0 ≤ δ) {t₀ σ : ℝ} {c : S → ℕ}
    (hball : ∑ s, ((c s : ℝ) / V - x t₀ s) ^ 2 ≤ δ ^ 2)
    (hmove : ∑ s, (x (t₀ + σ) s - x t₀ s) ^ 2 ≤ δ ^ 2 / 4) :
    ∑ s, ((c s : ℝ) / V - x (t₀ + σ) s) ^ 2 ≤ (3 * δ / 2) ^ 2 := by
  have hmove' : ∑ s, (x t₀ s - x (t₀ + σ) s) ^ 2 ≤ δ ^ 2 / 4 := by
    refine le_trans (Finset.sum_le_sum fun s _ => ?_) hmove
    have heq : (x t₀ s - x (t₀ + σ) s) ^ 2 = (x (t₀ + σ) s - x t₀ s) ^ 2 := by ring
    rw [heq]
  have hstep := Network.three_halves_step δ hδ
    (fun s => (c s : ℝ) / V - x t₀ s) (fun s => x t₀ s - x (t₀ + σ) s) hball hmove'
  have hsplit : ∀ s, ((c s : ℝ) / V - x (t₀ + σ) s)
      = ((c s : ℝ) / V - x t₀ s) + (x t₀ s - x (t₀ + σ) s) := by
    intro s
    have hVne : V ≠ 0 := ne_of_gt hV
    rw [div_eq_mul_inv]
    ring
  rw [show (∑ s, ((c s : ℝ) / V - x (t₀ + σ) s) ^ 2)
      = ∑ s, ((c s : ℝ) / V - x t₀ s + (x t₀ s - x (t₀ + σ) s)) ^ 2 by
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [hsplit s]]
  exact hstep

end Network

end CRNT
