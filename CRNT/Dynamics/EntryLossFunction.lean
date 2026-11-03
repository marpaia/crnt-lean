import CRNT.Dynamics.FacetRepulsionAndersonShiu
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# The persistence entry-loss function `η_s(t) = -log (x_s(t)/x_s(0))`

Anderson's persistence apparatus is built on one scalar function per species, the
**entry-loss**

```
  η_s (t) = -log ( x_s(t) / x_s(0) ) ,
```

normalised by the initial concentration.  It satisfies `η_s 0 = 0`, `η_s (t) ≥ 0` exactly when
`x_s` has not grown past its initial value, and `η_s (t) → +∞` exactly when `x_s (t) → 0`.
Anderson's near-face argument then reduces to a **rate hierarchy**: for a set `P` of vanishing
species and an off-face species `j` that stays bounded away from zero,

```
  η_j (t) / max_{s ∈ P} η_s (t)   →   0      (t → ∞) ,
```

i.e. an off-face species' entry-loss is asymptotically negligible compared with the worst
on-face species.

**Source.** The entry-loss function and the face entry-time bookkeeping are Anderson's
(D. F. Anderson, SIAM J. Appl. Math. **68** (2008), 1464–1476).  Its use in the
codimension-one face argument is D. F. Anderson and A. Shiu, *The dynamics of weakly reversible
population processes near facets*, SIAM J. Appl. Math. **70** (2010), 1840–1858
(arXiv:0903.0901), Theorem 3.2 — the theorem `CRNT.Dynamics.FacetRepulsionAndersonShiu`
already formalizes.

Per `research/DEAD-ENDS.md` entries A-8 and A-10: the entry-loss function appears in **neither**
Craciun–Nazarov–Pantea nor Craciun v3, and arXiv:2306.03055 is **not** Craciun v3 (that is
arXiv:1501.02860).  Nothing in the existing `CRNT/` tree mentions an entry-loss function, so
this module is genuinely new.

## A note on the hypotheses

A concentration is a bare real-valued map `Concentration S = S → ℝ`, so it carries **no**
built-in sign information: a coordinate may be `0` (or negative) at some time `n`.  Three
consequences shape the statements below, and each is a place where the naive statement is
simply **false** against this tree.

* **A coordinate that has *hit* zero has entry-loss `0`, not `+∞`**, because
  `Real.log 0 = 0`.  A trajectory with `y n s = 0` for all `n ≥ 1` therefore does *not* have
  `η_s n → +∞`, even though `y n s → 0` and `y 0 s > 0`.  Hence the tendsto theorems of
  section C take an extra **eventual strict positivity** hypothesis
  `∀ᶠ n in atTop, 0 < y n s` besides `y 0 s > 0`.  In every application the trajectory is a
  positive concentration, so this hypothesis is free.
* **Rescaling a whole trajectory does not shift `η` by `-log c`; it leaves `η` alone.**  The
  entry-loss is a function of the *ratio* `y n s / y 0 s` alone, and scaling numerator and
  denominator by the same `c > 0` does not change that ratio.  So `entryLoss_smul` is
  **scale invariance**, `η (c • y) = η y`.  The `-log c` shift belongs to the *unnormalised*
  quantity `-log (c * x)`, recorded separately as `negLog_mul`.
* **An upper bound alone does not bound a ratio.**  `f n / g n → 0` needs `0 ≤ f n` as well as
  `f n ≤ B`; without the lower bound the quotient may diverge to `-∞`.  So
  `entryLoss_div_tendsto_zero` assumes nonnegativity of the numerator, which the
  Anderson–Shiu application supplies from `y n j ≤ y 0 j`.

## Contents

**A. The entry-loss and its exact algebraic characterisations.**

* `entryLoss` : `η_s (n) = -(y n s / y 0 s).log` for `y : ℕ → Concentration S`.
* `entryLoss_zero` : `η_s 0 = 0`.
* `entryLoss_nonneg_iff` : `0 ≤ η_s n ↔ y n s ≤ y 0 s` for a trajectory with `y 0 s > 0` and
  `y n s ≥ 0`.  No boundary trouble: at `y n s = 0` both sides hold.
* `entryLoss_pos_iff` : `0 < η_s n ↔ 0 < y n s ∧ y n s < y 0 s`.  The `0 < y n s` conjunct is
  essential, not cosmetic: at `y n s = 0` the right-hand condition `y n s < y 0 s` holds while
  `η_s n = 0`, so the shorter `η_s n > 0 ↔ y n s < y 0 s` is false.
* `entryLoss_neg_iff` : `η_s n < 0 ↔ y n s > y 0 s`.  No boundary case arises: the hypothesis
  `y n s ≥ 0` makes both sides false at `y n s = 0`.
* `entryLoss_smul` : **rescaling a trajectory by `c > 0` leaves every entry-loss unchanged**,
  so the asymptotic content of `η` is scale-invariant.  This is what makes `η` a function of
  the *ratio* rather than of the absolute concentration.
* `negLog_mul` : the companion identity `-log (c * x) = -log x - log c` for `c, x > 0`,
  i.e. the `-log c` shift of the *unnormalised* entry-loss.
* `entryLoss_mul` : `η (y * z) = η y + η z` for strictly positive trajectories — `η` is a
  homomorphism from the multiplicative monoid of positive trajectories to `(ℝ, +)`.  This is
  the identity that lets `η` be applied to monomial-weighted trajectories.

**B. The face entry-loss `η_P` and its order structure.**

* `faceEntryLoss` : `η_P (n) = max_{s ∈ P} η_s n` for `P.Nonempty`.
* `faceEntryLoss_le`, `faceEntryLoss_mem` : on-face species are bounded by, and one attains,
  the face entry-loss.
* `faceEntryLoss_mono` : **the face hierarchy is monotone** — `P ⊆ Q → η_P ≤ η_Q`.  This is the
  order structure that makes the `Pmax` package meaningful: the maximal face dominates every
  sub-face.
* `faceEntryLoss_eq_of_subset_of_mem` : an on-face maximiser of `P` that lies in `Q ⊇ P`
  forces the two face entry-losses to be equal.

**C. The rate hierarchy (Anderson–Shiu).**

* `entryLoss_tendsto_atTop_of_tendsto_zero` : `y n s → 0`, `y 0 s > 0` and `0 < y n s`
  eventually give `η_s n → +∞`.
* `faceEntryLoss_tendsto_atTop` : if every on-face species dies out, `η_P n → +∞`.
* `faceEntryLoss_tendsto_atTop_pos` : consequently `η_P n` is eventually strictly positive.
* `entryLoss_div_tendsto_zero` : **the rate hierarchy, in its cleanest form.** If
  `η_P n → +∞`, `0 ≤ η_j n ≤ B` for all `n`, then `(η_j n) / (η_P n) → 0`.  Pure filter
  algebra, no CRNT hypotheses.
* `faceEntryLoss_tendsto_zero_div` : **the hierarchy for an off-face species.** If every
  on-face species tends to zero and the off-face species `j` satisfies `0 < c ≤ y n j` and
  `y n j ≤ y 0 j` for all `n` (i.e. `j` is persistent and never grows), then
  `(η_j n) / (η_P n) → 0`.  This is the exact statement the Anderson–Shiu argument consumes.
* `faceEntryLoss_gt_mul_eventually` : the same hierarchy read as a `C`-multiple estimate.

**D. Entry times: the discrete shadow of the hierarchy.**

* `entryTimeBelow` : the least `n` with `y n s < ε`.
* `entryTimeBelow_spec` : the defining witness.
* `entryTimeBelow_mono` : **a larger threshold is entered no later** — `ε ≤ ε'` gives
  `entryTimeBelow ε' ≤ entryTimeBelow ε`.
* `exists_entryTime_below_of_tendsto_zero` : a dying-out species has a finite entry time below
  every positive threshold.
* `pow_neg_tendsto_zero` : the limit lemma `a ^ (-n) → 0` for `a > 1`, used by the example.

**E. Worked example (non-vacuity).**

`decayTraj n = (2 ^ (-n), 1)` over `S = Fin 2`.  Verified: `η_0 n = n * log 2` grows without
bound, `η_1 n = 0` identically, `η_{0} n = η_{0,1} n = η_0 n` (so the face hierarchy is
non-degenerate), the off-face ratio `η_1 n / η_{0,1} n = 0`, and the rate-hierarchy
hypotheses hold with `c = 1`.

Depends on: `CRNT.Dynamics.FacetRepulsionAndersonShiu`, Mathlib
`Analysis.SpecialFunctions.Log`, `Analysis.SpecialFunctions.Exp`,
`Analysis.SpecificLimits.Basic`, `Topology.Algebra.Order.Field`.
-/

namespace CRNT
namespace Dynamics

open Filter
open scoped BigOperators Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### Log preliminaries

The three equivalences below are what all the sign characterisations of `entryLoss` rest on.
They are stated once, for a nonnegative (resp. positive) argument, and then applied. -/

section Log

variable {r : ℝ}

/-- For a nonnegative argument, `log r ≤ 0` exactly when `r ≤ 1`. -/
theorem log_le_zero_iff_of_nonneg (hr : 0 ≤ r) : Real.log r ≤ 0 ↔ r ≤ 1 := by
  constructor
  · intro h
    by_contra hr1
    have hx : 0 < Real.log r :=
      by simpa using Real.log_lt_log (by norm_num) (lt_of_not_ge hr1)
    exact (fun hc => (not_lt_of_ge h) hc) hx
  · intro h
    exact Real.log_nonpos hr h

/-- For a positive argument, `log r < 0` exactly when `r < 1`. -/
theorem log_lt_zero_iff_of_pos (hr : 0 < r) : Real.log r < 0 ↔ r < 1 := by
  constructor
  · intro h
    by_contra hr1
    have hle : 1 ≤ r := le_of_not_gt hr1
    rcases lt_or_eq_of_le hle with hlt | hEq
    · have hx : 0 < Real.log r := by simpa using Real.log_lt_log (by norm_num) hlt
      exact (fun hc => (not_lt_of_ge (le_of_lt h)) hc) hx
    · subst hEq
      rw [Real.log_one] at h
      simp at h
  · intro h
    exact Real.log_neg hr h

/-- For a positive argument, `log r > 0` exactly when `1 < r`. -/
theorem log_pos_iff_of_pos (hr : 0 < r) : 0 < Real.log r ↔ 1 < r := by
  constructor
  · intro h
    by_contra hr1
    have hle : r ≤ 1 := le_of_not_gt hr1
    have hz : Real.log r ≤ 0 := Real.log_nonpos hr.le hle
    exact (fun hc => (not_le_of_gt h) hc) hz
  · intro h
    exact Real.log_pos h

/-- The strict comparison of a positive ratio against one. -/
theorem lt_one_div_iff (a b : ℝ) (hb : 0 < b) : a / b < 1 ↔ a < b := div_lt_one hb

/-- The strict comparison of a ratio against one, from above. -/
theorem one_lt_div_iff' (a b : ℝ) (hb : 0 < b) : 1 < a / b ↔ b < a := by
  rw [lt_div_iff₀ hb]
  constructor
  · intro h; simpa using h
  · intro h; simpa using h

end Log

/-! ### A. The entry-loss function -/

/-- **The entry-loss of species `s` along a trajectory `y` at time `n`**:
`η_s n = -log (y n s / y 0 s)`.

Normalising by the initial concentration makes `η_s 0 = 0` and makes `η_s` depend only on the
*ratio* `y n s / y 0 s`, i.e. only on the relative loss of the species. -/
noncomputable def entryLoss (y : ℕ → Concentration S) (s : S) (n : ℕ) : ℝ :=
  -Real.log (y n s / y 0 s)

@[simp] theorem entryLoss_zero (y : ℕ → Concentration S) (s : S) :
    entryLoss y s 0 = 0 := by
  by_cases h : y 0 s = 0 <;> simp [entryLoss, h]

/-- **A nonnegative ratio at most one gives a nonnegative entry-loss.**  This holds with no
strictness on `y n s`: the boundary case `y n s = 0` gives `η_s n = -log 0 = 0`. -/
theorem entryLoss_nonneg_iff {y : ℕ → Concentration S} {s : S} {n : ℕ}
    (h0 : 0 < y 0 s) (hn : 0 ≤ y n s) :
    0 ≤ entryLoss y s n ↔ y n s ≤ y 0 s := by
  have hr0 : 0 ≤ y n s / y 0 s := div_nonneg hn h0.le
  constructor
  · intro h
    exact (div_le_one h0).1 ((log_le_zero_iff_of_nonneg hr0).1 (by
      have : Real.log (y n s / y 0 s) ≤ 0 := by
        rw [entryLoss] at h; simpa using h
      exact this))
  · intro h
    have h' : Real.log (y n s / y 0 s) ≤ 0 :=
      (log_le_zero_iff_of_nonneg hr0).2 ((div_le_one h0).2 h)
    rw [entryLoss]
    linarith

/-- **The entry-loss is strictly positive exactly when the coordinate is strictly positive and
strictly decreased.**  The `0 < y n s` conjunct is essential rather than cosmetic: at the
boundary `y n s = 0` one has `η_s n = -log 0 = 0`, so strict positivity of `η_s` fails while
`y n s < y 0 s` still holds.  So the shorter `0 < η_s n ↔ y n s < y 0 s` would be false. -/
theorem entryLoss_pos_iff {y : ℕ → Concentration S} {s : S} {n : ℕ}
    (h0 : 0 < y 0 s) (hn : 0 ≤ y n s) :
    0 < entryLoss y s n ↔ 0 < y n s ∧ y n s < y 0 s := by
  by_cases hz : y n s = 0
  · simp [entryLoss, hz, Real.log_zero]
  · have hp : 0 < y n s := lt_of_le_of_ne hn (Ne.symm hz)
    have hr0 : 0 < y n s / y 0 s := div_pos hp h0
    constructor
    · intro h
      refine ⟨hp, (lt_one_div_iff _ _ h0).1 ?_⟩
      have hlt : Real.log (y n s / y 0 s) < 0 := by
        rw [entryLoss] at h; linarith [h]
      exact (log_lt_zero_iff_of_pos hr0).1 hlt
    · intro h
      have hlt : Real.log (y n s / y 0 s) < 0 :=
        (log_lt_zero_iff_of_pos hr0).2 ((lt_one_div_iff _ _ h0).2 h.2)
      rw [entryLoss]
      linarith

/-- **The entry-loss is negative exactly when the coordinate grew.**  No boundary case arises
here: the hypothesis `y n s ≥ 0` makes both sides false at `y n s = 0`. -/
theorem entryLoss_neg_iff {y : ℕ → Concentration S} {s : S} {n : ℕ}
    (h0 : 0 < y 0 s) (hn : 0 ≤ y n s) :
    entryLoss y s n < 0 ↔ y n s > y 0 s := by
  by_cases hz : y n s = 0
  · simp [entryLoss, hz, Real.log_zero, not_lt.mpr h0.le]
  · have hp : 0 < y n s := lt_of_le_of_ne hn (Ne.symm hz)
    have hr0 : 0 < y n s / y 0 s := div_pos hp h0
    constructor
    · intro h
      have hpos : 0 < Real.log (y n s / y 0 s) := by
        rw [entryLoss] at h; linarith [h]
      have h1 : 1 < y n s / y 0 s := (log_pos_iff_of_pos hr0).1 hpos
      have h1' : y 0 s < y n s := (one_lt_div_iff' (y n s) (y 0 s) h0).mp h1
      exact h1'
    · intro h
      have h1 : 1 < y n s / y 0 s := (one_lt_div_iff' (y n s) (y 0 s) h0).mpr h
      have hpos : 0 < Real.log (y n s / y 0 s) := (log_pos_iff_of_pos hr0).2 h1
      rw [entryLoss]
      linarith

/-- **Rescaling a trajectory by `c > 0` leaves every entry-loss unchanged.**  The entry-loss
is a function of the ratio `y n s / y 0 s` alone, and scaling numerator and denominator by
`c` does not change that ratio.  Hence the asymptotic content of `η` is invariant under
rescaling. -/
theorem entryLoss_smul (y : ℕ → Concentration S) (s : S) (n : ℕ) {c : ℝ} (hc : 0 < c) :
    entryLoss (fun k => c • y k) s n = entryLoss y s n := by
  by_cases hb : y 0 s = 0
  · simp [entryLoss, Pi.smul_apply, smul_eq_mul, hb, Real.log_zero]
  · have key : (c * y n s) / (c * y 0 s) = y n s / y 0 s := by
      field_simp [ne_of_gt hc, hb]
    simp only [entryLoss, Pi.smul_apply, smul_eq_mul]
    rw [key]

/-- **The `-log c` shift, for the unnormalised entry-loss.**  Scaling a single positive
concentration `x` by `c > 0` shifts `-log` of it by `-log c`; this is the identity behind the
heuristic "`η` shifts by `-log c` under rescaling", and `entryLoss_smul` is what shows that no
such shift survives in the ratio-normalised `η`. -/
theorem negLog_mul {x c : ℝ} (hc : 0 < c) (hx : 0 < x) :
    -Real.log (c * x) = -Real.log x - Real.log c := by
  rw [Real.log_mul (ne_of_gt hc) (ne_of_gt hx)]
  ring

/-- **Entry-loss is additive under multiplication of strictly positive trajectories**:
`η (y * z) = η y + η z`.  This is the identity that lets `η` be applied to products of
trajectories, e.g. monomial-weighted ones. -/
theorem entryLoss_mul (y z : ℕ → Concentration S) (s : S) (n : ℕ)
    (hy : ∀ k, 0 < y k s) (hz : ∀ k, 0 < z k s) :
    entryLoss (fun k => y k * z k) s n = entryLoss y s n + entryLoss z s n := by
  have key : y n s * z n s / (y 0 s * z 0 s) = (y n s / y 0 s) * (z n s / z 0 s) := by
    field_simp [ne_of_gt (hy 0), ne_of_gt (hz 0)]
  have hyn : y n s / y 0 s ≠ 0 := ne_of_gt (div_pos (hy n) (hy 0))
  have hzn : z n s / z 0 s ≠ 0 := ne_of_gt (div_pos (hz n) (hz 0))
  simp only [entryLoss, Pi.mul_apply]
  calc -Real.log (y n s * z n s / (y 0 s * z 0 s))
      = -Real.log ((y n s / y 0 s) * (z n s / z 0 s)) := by rw [key]
    _ = -(Real.log (y n s / y 0 s) + Real.log (z n s / z 0 s)) := by
        rw [Real.log_mul hyn hzn]
    _ = -Real.log (y n s / y 0 s) + -Real.log (z n s / z 0 s) := by ring

/-! ### B. The face entry-loss -/

/-- **The face entry-loss** `η_P n = max_{s ∈ P} η_s n`: the worst entry-loss among the species
of a nonempty face `P`.  This is the quantity the Anderson–Shiu rate hierarchy compares an
off-face species against. -/
noncomputable def faceEntryLoss (y : ℕ → Concentration S) (P : Finset S) (hP : P.Nonempty)
    (n : ℕ) : ℝ :=
  P.sup' hP (fun s => entryLoss y s n)

/-- Every on-face species' entry-loss is bounded by the face entry-loss. -/
theorem faceEntryLoss_le (y : ℕ → Concentration S) {P : Finset S} (hP : P.Nonempty)
    {s : S} (hs : s ∈ P) (n : ℕ) : entryLoss y s n ≤ faceEntryLoss y P hP n :=
  Finset.le_sup' (fun t => entryLoss y t n) hs

/-- The face entry-loss is attained by an on-face species. -/
theorem faceEntryLoss_mem (y : ℕ → Concentration S) {P : Finset S} (hP : P.Nonempty)
    (n : ℕ) : ∃ s ∈ P, entryLoss y s n = faceEntryLoss y P hP n := by
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image P (fun t => entryLoss y t n) hP
  exact ⟨s, hs, le_antisymm (faceEntryLoss_le y hP hs n)
    (Finset.sup'_le hP _ fun t ht => hmax t ht)⟩

/-- **The face hierarchy is monotone**: enlarging a face enlarges the face entry-loss.  This
is the order structure that makes the `Pmax` package meaningful — for `P ⊆ Q`,
`η_P ≤ η_Q`, so a maximal face's entry-loss dominates every sub-face. -/
theorem faceEntryLoss_mono (y : ℕ → Concentration S) {P Q : Finset S}
    (hP : P.Nonempty) (hQ : Q.Nonempty) (hPQ : P ⊆ Q) (n : ℕ) :
    faceEntryLoss y P hP n ≤ faceEntryLoss y Q hQ n :=
  Finset.sup'_le hP _ fun t ht => faceEntryLoss_le y hQ (hPQ ht) n

/-- **A shared maximiser collapses two faces.**  If `P ⊆ Q` and some `s ∈ P` attains `η_Q` —
the *outer* face's entry-loss — then `η_P = η_Q`: the two face entry-losses coincide.

The direction of `hattain` matters.  The hypothesis `entryLoss y s n = faceEntryLoss y P hP n`
(the species attains the *inner* face's value) would make the conclusion **false**: with
`P = {0}` and `Q = {0, 1}` the species `0` can attain `η_P` while `η_Q` is strictly larger
because of species `1`.  That hypothesis yields only `η_P ≤ η_Q`, which is exactly
`faceEntryLoss_mono`. -/
theorem faceEntryLoss_eq_of_subset_of_mem (y : ℕ → Concentration S) {P Q : Finset S}
    (hP : P.Nonempty) (hQ : Q.Nonempty) {s : S} (hPQ : P ⊆ Q) (hs : s ∈ P) (n : ℕ)
    (hattain : entryLoss y s n = faceEntryLoss y Q hQ n) :
    faceEntryLoss y P hP n = faceEntryLoss y Q hQ n :=
  le_antisymm (faceEntryLoss_mono y hP hQ hPQ n)
    (hattain.ge.trans (faceEntryLoss_le y hP hs n))

/-! ### C. The rate hierarchy -/

/-- **A coordinate dying out has entry-loss tending to `+∞`.**  Requires `y 0 s > 0`, the
normalisation being well posed, and `0 < y n s` eventually: at a coordinate that has *hit*
zero the entry-loss is `0`, not `+∞`. -/
theorem entryLoss_tendsto_atTop_of_tendsto_zero {y : ℕ → Concentration S} {s : S}
    (h0 : 0 < y 0 s) (hpos : ∀ᶠ n in atTop, 0 < y n s)
    (htend : Tendsto (fun n => y n s) atTop (𝓝 0)) :
    Tendsto (entryLoss y s) atTop atTop := by
  have hratio : Tendsto (fun n => y n s / y 0 s) atTop (𝓝 0) := by
    simpa using htend.div_const (y 0 s)
  have hrpos : ∀ᶠ n in atTop, 0 < y n s / y 0 s :=
    hpos.mono fun _ hn => div_pos hn h0
  -- `r n → 0⁺` gives `r n⁻¹ → +∞`
  have hinv : Tendsto (fun n => (y n s / y 0 s)⁻¹) atTop atTop := by
    refine tendsto_atTop_atTop.2 fun M => ?_
    by_cases hM : 0 < M
    · obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
        (hratio.eventually (eventually_lt_nhds (inv_pos.mpr hM)))
      obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hrpos
      refine ⟨max N N0, fun n hn => ?_⟩
      have hposn : 0 < y n s / y 0 s := hN0 n ((le_max_right N N0).trans hn)
      have hlt : y n s / y 0 s * M < 1 :=
        (lt_div_iff₀ hM).mp (by simpa using hN n ((le_max_left N N0).trans hn))
      have hle : M * (y n s / y 0 s) ≤ 1 := by linarith
      have : M ≤ (y n s / y 0 s)⁻¹ := by
        rw [inv_eq_one_div]
        exact (le_div_iff₀ hposn).2 (by linarith)
      simpa using this
    · obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.1 hrpos
      refine ⟨N0, fun n hn => ?_⟩
      exact (not_lt.mp hM).trans (inv_pos.mpr (hN0 n hn)).le
  have hlog : Tendsto (fun n : ℕ => Real.log ((y n s / y 0 s)⁻¹)) atTop atTop := by
    refine (Real.tendsto_log_atTop.comp hinv).congr'
      (Filter.Eventually.of_forall fun n => ?_)
    simp
  unfold entryLoss
  refine hlog.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact Real.log_inv (y n s / y 0 s)

/-- **The face entry-loss tends to `+∞` when every on-face species dies out.** This is the
on-face half of the hierarchy. -/
theorem faceEntryLoss_tendsto_atTop {y : ℕ → Concentration S} {P : Finset S}
    (hP : P.Nonempty) (h0 : ∀ s ∈ P, 0 < y 0 s)
    (hpos : ∀ s ∈ P, ∀ᶠ n in atTop, 0 < y n s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0)) :
    Tendsto (faceEntryLoss y P hP) atTop atTop := by
  obtain ⟨s₀, hs₀⟩ := hP
  have hP' : P.Nonempty := ⟨s₀, hs₀⟩
  have hη₀ := entryLoss_tendsto_atTop_of_tendsto_zero (h0 s₀ hs₀) (hpos s₀ hs₀)
    (htend s₀ hs₀)
  refine tendsto_atTop_atTop.2 fun M => ?_
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hη₀.eventually (show ∀ᶠ x : ℝ in atTop, M ≤ x from eventually_ge_atTop M))
  refine ⟨N, fun n hn => ?_⟩
  exact le_trans (hN n hn) (faceEntryLoss_le y hP' hs₀ n)

/-- **The face entry-loss is eventually strictly positive.** A corollary of the preceding
theorem; this is the nonvanishing needed to form the ratio in the hierarchy. -/
theorem faceEntryLoss_tendsto_atTop_pos {y : ℕ → Concentration S} {P : Finset S}
    (hP : P.Nonempty) (h0 : ∀ s ∈ P, 0 < y 0 s)
    (hpos : ∀ s ∈ P, ∀ᶠ n in atTop, 0 < y n s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 0 < faceEntryLoss y P hP n := by
  have h : ∀ᶠ n in atTop, (1:ℝ) ≤ faceEntryLoss y P hP n :=
    (faceEntryLoss_tendsto_atTop hP h0 hpos htend).eventually
      (show ∀ᶠ x : ℝ in atTop, (1:ℝ) ≤ x from eventually_ge_atTop 1)
  filter_upwards [h] with n hn
  linarith

/-- **The rate hierarchy in its pure filter-algebra form.**  A nonnegative numerator bounded
above by `B`, over a denominator tending to `+∞`, tends to `0`.  The nonnegativity of the
numerator is part of the statement: an upper bound alone would not control the ratio, which
could diverge to `-∞`. -/
theorem entryLoss_div_tendsto_zero {f g : ℕ → ℝ} {B : ℝ} (hg : Tendsto g atTop atTop)
    (hpos : ∀ n, 0 ≤ f n) (hb : ∀ n, f n ≤ B) :
    Tendsto (fun n => f n / g n) atTop (𝓝 0) := by
  have h1 : ∀ᶠ n in atTop, (1:ℝ) ≤ g n :=
    hg.eventually (show ∀ᶠ x : ℝ in atTop, (1:ℝ) ≤ x from eventually_ge_atTop 1)
  have hgpos : ∀ᶠ n in atTop, 0 < g n := by
    filter_upwards [h1] with n hn
    linarith
  refine squeeze_zero' ?_ ?_ (hg.const_div_atTop B)
  · filter_upwards [hgpos] with n hn
    exact div_nonneg (hpos n) hn.le
  · filter_upwards [hgpos] with n hn
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (hb n) (inv_nonneg.mpr hn.le)

/-- **The Anderson–Shiu rate hierarchy for an off-face species.**

Let `P` be a nonempty face whose species all die out, and let `j` be a species off the face
which stays uniformly bounded away from zero and never grows past its initial value.  Then the
ratio of `j`'s entry-loss to the face entry-loss tends to `0`:

```
  η_j n / η_P n  →  0      (n → ∞) .
```

The hypotheses `0 < c ≤ y n j` and `y n j ≤ y 0 j` say exactly that `j` is *persistent* in the
Definition 2.7 sense of Craciun–Nazarov–Pantea (*Persistence and permanence of mass-action
and power-law dynamical systems*, J. Math. Anal. Appl. 342 (2008), 366–382): `y_j` has a
positive uniform lower bound, hence `0 ≤ η_j n ≤ -log (c / y 0 j)`, while `η_P n → +∞`. -/
theorem faceEntryLoss_tendsto_zero_div {y : ℕ → Concentration S} {P : Finset S} {j : S}
    (hP : P.Nonempty) (hj : j ∉ P) {c : ℝ} (hc : 0 < c)
    (hbelow : ∀ n, c ≤ y n j) (habove : ∀ n, y n j ≤ y 0 j)
    (h0j : 0 < y 0 j)
    (h0 : ∀ s ∈ P, 0 < y 0 s)
    (hpos : ∀ s ∈ P, ∀ᶠ n in atTop, 0 < y n s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0)) :
    Tendsto (fun n => entryLoss y j n / faceEntryLoss y P hP n) atTop (𝓝 0) := by
  -- the numerator is nonnegative (from `habove`) and bounded above by `-log (c / y 0 j)`
  have hbound : ∀ n, entryLoss y j n ≤ -Real.log (c / y 0 j) := by
    intro n
    have hnn : 0 ≤ y n j := hc.le.trans (hbelow n)
    have hratio : c / y 0 j ≤ y n j / y 0 j :=
      (div_le_div_iff_of_pos_right h0j).2 (hbelow n)
    have hlog : Real.log (c / y 0 j) ≤ Real.log (y n j / y 0 j) :=
      Real.log_le_log (div_pos hc h0j) hratio
    have hneg : -Real.log (y n j / y 0 j) ≤ -Real.log (c / y 0 j) := neg_le_neg hlog
    simpa [entryLoss] using hneg
  refine entryLoss_div_tendsto_zero (faceEntryLoss_tendsto_atTop hP h0 hpos htend) ?_ hbound
  intro n
  exact (entryLoss_nonneg_iff h0j (hc.le.trans (hbelow n))).2 (habove n)

/-- **The hierarchy in the form a descent argument consumes.** Under the hypotheses of
`faceEntryLoss_tendsto_zero_div`, for every `C > 0` there is `N` with
`C * η_j n < η_P n` for all `n ≥ N`: the face entry-loss eventually dominates any fixed
multiple of the off-face entry-loss. -/
theorem faceEntryLoss_gt_mul_eventually {y : ℕ → Concentration S} {P : Finset S} {j : S}
    (hP : P.Nonempty) (hj : j ∉ P) {c : ℝ} (hc : 0 < c)
    (hbelow : ∀ n, c ≤ y n j) (habove : ∀ n, y n j ≤ y 0 j)
    (h0j : 0 < y 0 j)
    (h0 : ∀ s ∈ P, 0 < y 0 s)
    (hpos : ∀ s ∈ P, ∀ᶠ n in atTop, 0 < y n s)
    (htend : ∀ s ∈ P, Tendsto (fun n => y n s) atTop (𝓝 0))
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ n in atTop, C * entryLoss y j n < faceEntryLoss y P hP n := by
  have hratio := faceEntryLoss_tendsto_zero_div hP hj hc hbelow habove h0j h0 hpos htend
  have hpos' := faceEntryLoss_tendsto_atTop_pos hP h0 hpos htend
  have h1 : ∀ᶠ n in atTop, 0 < faceEntryLoss y P hP n := hpos'
  have h2 : ∀ᶠ n in atTop,
      entryLoss y j n / faceEntryLoss y P hP n < C⁻¹ :=
    hratio.eventually (eventually_lt_nhds (inv_pos.mpr hC))
  filter_upwards [h1, h2] with n hpn hn
  have hratio' : entryLoss y j n / faceEntryLoss y P hP n < C⁻¹ := hn
  have hmul : entryLoss y j n < C⁻¹ * faceEntryLoss y P hP n :=
    (div_lt_iff₀ hpn).mp hratio'
  calc C * entryLoss y j n < C * (C⁻¹ * faceEntryLoss y P hP n) :=
        mul_lt_mul_of_pos_left hmul hC
    _ = faceEntryLoss y P hP n := by
        rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]

/-! ### D. Entry times -/

/-- **The entry time of a species below a threshold**: the least `n` at which `y n s < ε`. -/
noncomputable def entryTimeBelow (y : ℕ → Concentration S) (s : S) (ε : ℝ)
    (h : ∃ n, y n s < ε) : ℕ :=
  Nat.find h

/-- The defining witness of the entry time. -/
theorem entryTimeBelow_spec (y : ℕ → Concentration S) (s : S) {ε : ℝ} (h : ∃ n, y n s < ε) :
    y (entryTimeBelow y s ε h) s < ε :=
  Nat.find_spec h

/-- **A larger threshold is entered no later**: `ε ≤ ε'` gives
`entryTimeBelow ε' ≤ entryTimeBelow ε`.  This is the monotonicity of the entry-time
"matrix" in the threshold variable.

Note the direction: it is the *larger* threshold that is entered sooner, so the inequality
runs from `ε'` down to `ε`.  The opposite orientation (`entryTimeBelow ε ≤ entryTimeBelow ε'`)
is **false**: take `y n 0 = 2.5` at `n = 0`, `y 5 0 = 1`, and `y n 0 = 100` for `n ≥ 6`,
with thresholds `ε = 2 < ε' = 3`.  The species is below `ε` only from `n = 5`, but below `ε'`
already from `n = 0`. -/
theorem entryTimeBelow_mono (y : ℕ → Concentration S) (s : S) {ε ε' : ℝ} (hε : ε ≤ ε')
    (h : ∃ n, y n s < ε) (h' : ∃ n, y n s < ε') :
    entryTimeBelow y s ε' h' ≤ entryTimeBelow y s ε h :=
  Nat.find_min' h' (m := Nat.find h) (lt_of_lt_of_le (Nat.find_spec h) hε)

/-- **A dying-out species has a finite entry time below every threshold.** If
`y n s → 0` and `ε > 0`, the trajectory eventually drops below `ε`. -/
theorem exists_entryTime_below_of_tendsto_zero {y : ℕ → Concentration S} {s : S} {ε : ℝ}
    (hε : 0 < ε) (htend : Tendsto (fun n => y n s) atTop (𝓝 0)) :
    ∃ n, y n s < ε :=
  htend.eventually (eventually_lt_nhds hε) |>.exists

/-- **A geometric decay rate `a > 1` gives `a ^ (-n) → 0`.**  The natural limit lemma for the
worked example below. -/
theorem pow_neg_tendsto_zero (a : ℝ) (ha : 1 < a) :
    Tendsto (fun n : ℕ => a ^ (-(n : ℤ))) atTop (𝓝 0) := by
  have heq : (fun n : ℕ => a ^ (-(n : ℤ))) = (fun n : ℕ => a⁻¹ ^ n) := by
    funext n
    rw [zpow_neg, zpow_natCast, ← inv_pow]
  have hlt : a⁻¹ < 1 := (inv_lt_one₀ (lt_trans (by norm_num) ha)).2 ha
  have hnonneg : 0 ≤ a⁻¹ := (inv_pos.mpr (lt_trans (by norm_num) ha)).le
  have hlim : Tendsto (fun n : ℕ => a⁻¹ ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hnonneg hlt
  rw [heq]
  refine hlim.congr' (Filter.Eventually.of_forall fun n => ?_)
  simp

/-! ### E. Worked example: `y n = (2 ^ (-n), 1)` over `Fin 2` -/

section Example

/-- A nonnegative trajectory on two species: the first decaying like `2^{-n}`, the second
constant at `1`. -/
noncomputable def decayTraj : ℕ → Concentration (Fin 2) :=
  fun n s => if s = 0 then (2 : ℝ) ^ (-(n : ℤ)) else 1

@[simp] theorem decayTraj_zero (n : ℕ) : decayTraj n 0 = (2 : ℝ) ^ (-(n : ℤ)) := by
  simp [decayTraj]

@[simp] theorem decayTraj_one (n : ℕ) : decayTraj n 1 = 1 := by
  simp [decayTraj]

@[simp] theorem decayTraj_nonneg (n : ℕ) (s : Fin 2) : 0 ≤ decayTraj n s := by
  by_cases hs : s = 0
  · subst hs
    exact zpow_nonneg (by norm_num) _
  · simp [decayTraj, hs]

@[simp] theorem decayTraj_pos (n : ℕ) (s : Fin 2) : 0 < decayTraj n s := by
  by_cases hs : s = 0
  · subst hs
    exact zpow_pos (by norm_num) _
  · simp [decayTraj, hs]

theorem decayTraj_zero_zerocoord : decayTraj 0 0 = 1 := by
  simp [decayTraj]

/-- The decaying coordinate tends to `0`. -/
theorem decayTraj_tendsto_zero : Tendsto (fun n => decayTraj n 0) atTop (𝓝 0) := by
  simpa using pow_neg_tendsto_zero (2 : ℝ) (by norm_num)

/-- **The entry-loss of the decaying species tends to `+∞`.** -/
theorem entryLoss_decay_tendsto_atTop : Tendsto (entryLoss decayTraj 0) atTop atTop := by
  refine entryLoss_tendsto_atTop_of_tendsto_zero ?_ ?_ decayTraj_tendsto_zero
  · rw [decayTraj_zero_zerocoord]; norm_num
  · exact Filter.Eventually.of_forall fun n => decayTraj_pos n 0

/-- **The entry-loss of the constant species vanishes identically.** -/
theorem entryLoss_const_zero : ∀ n, entryLoss decayTraj 1 n = 0 := by
  intro n
  simp [entryLoss, decayTraj]

/-- **The face entry-loss of the singleton face `{0}` is the decaying species' entry-loss.** -/
theorem faceEntryLoss_single (n : ℕ) :
    faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n = entryLoss decayTraj 0 n := by
  simp [faceEntryLoss, Finset.sup'_singleton]

/-- **The face entry-loss of the full face `univ` equals that of `{0}`**, because the second
species contributes the entry-loss `0`.  Together with `faceEntryLoss_mono` this shows the
face hierarchy is non-degenerate in this example. -/
theorem faceEntryLoss_univ (n : ℕ) :
    faceEntryLoss decayTraj (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty n
      = faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n := by
  obtain ⟨s, _, hmem⟩ := faceEntryLoss_mem decayTraj Finset.univ_nonempty n
  obtain hs0 | hs1 : s = 0 ∨ s = 1 := by
    have := s.isLt
    omega
  · subst hs0
    -- `hmem` says species `0` attains `η_univ`, and `0 ∈ {0} ⊆ univ`
    exact (faceEntryLoss_eq_of_subset_of_mem
      (y := decayTraj) (P := ({0} : Finset (Fin 2))) (Q := Finset.univ) (s := 0)
      (by simp) Finset.univ_nonempty (Finset.subset_univ _) (by simp) n hmem).symm
  · subst hs1
    -- species `1` attains `η_univ` but `η_1 n = 0 ≤ η_0 n = η_{ {0} } n`
    have hdecay : decayTraj n 0 ≤ 1 := by
      rw [decayTraj_zero, zpow_neg, zpow_natCast, ← inv_pow]
      exact pow_le_one₀ (by norm_num) (by norm_num)
    have h0le : 0 ≤ entryLoss decayTraj 0 n :=
      (entryLoss_nonneg_iff (by rw [decayTraj_zero_zerocoord]; norm_num)
        (decayTraj_nonneg n 0)).2 (hdecay.trans_eq decayTraj_zero_zerocoord)
    have hle : faceEntryLoss decayTraj Finset.univ Finset.univ_nonempty n
        ≤ faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n := by
      calc faceEntryLoss decayTraj Finset.univ Finset.univ_nonempty n
          = entryLoss decayTraj 1 n := hmem.symm
        _ = 0 := entryLoss_const_zero n
        _ ≤ faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n := by
          rw [faceEntryLoss_single n]
          exact h0le
    exact le_antisymm hle
      (faceEntryLoss_mono decayTraj (P := ({0} : Finset (Fin 2))) (Q := Finset.univ)
        (by simp) Finset.univ_nonempty (Finset.subset_univ _) n)

/-- **The rate hierarchy in the example**: the off-face ratio is identically `0`. -/
theorem entryLoss_ratio_example (n : ℕ) :
    entryLoss decayTraj 1 n
      / faceEntryLoss decayTraj (Finset.univ : Finset (Fin 2)) Finset.univ_nonempty n = 0 := by
  rw [entryLoss_const_zero, zero_div]

/-- **The hierarchy hypotheses of the example are satisfied with `c = 1`**, so
`faceEntryLoss_tendsto_zero_div` really applies here: the off-face species `1` is persistent
(`y n 1 = 1 ≥ 1`) and never grows. -/
theorem hierarchy_applies_example :
    Tendsto (fun n => entryLoss decayTraj 1 n
      / faceEntryLoss decayTraj ({0} : Finset (Fin 2)) (by simp) n) atTop (𝓝 0) := by
  have hP : ({0} : Finset (Fin 2)).Nonempty := by simp
  have hpos : ∀ s ∈ ({0} : Finset (Fin 2)), ∀ᶠ n in atTop, 0 < decayTraj n s := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst hs
    exact Filter.Eventually.of_forall fun n => decayTraj_pos n 0
  have htend : ∀ s ∈ ({0} : Finset (Fin 2)), Tendsto (fun n => decayTraj n s) atTop (𝓝 0) := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst hs
    exact decayTraj_tendsto_zero
  have h0 : ∀ s ∈ ({0} : Finset (Fin 2)), 0 < decayTraj 0 s := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    subst hs
    rw [decayTraj_zero_zerocoord]
    norm_num
  exact faceEntryLoss_tendsto_zero_div hP (by simp) (c := (1 : ℝ)) (by norm_num)
    (fun _ => by simp) (fun _ => by simp) (by norm_num) h0 hpos htend

/-- **The entry times separate strictly in the example**: for `0 < ε ≤ 1` the decaying species
enters below `ε`, while the constant species (stuck at `1`) never does.  The hypothesis
`ε ≤ 1` is necessary: the constant species sits at `1`, so it *does* fall below any threshold
`ε > 1`. -/
theorem entryTime_example {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ n, decayTraj n 0 < ε ∧ ∀ m, decayTraj m 1 ≥ ε := by
  obtain ⟨n, hn⟩ := exists_entryTime_below_of_tendsto_zero hε decayTraj_tendsto_zero
  exact ⟨n, by simpa using hn, fun m => by rw [decayTraj_one]; exact hε1⟩

end Example

end Dynamics
end CRNT
