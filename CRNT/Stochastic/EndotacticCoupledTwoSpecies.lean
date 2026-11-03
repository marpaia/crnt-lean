import CRNT.Stochastic.EndotacticTierPositiveRecurrence

/-
# A coupled two-species example: count-lattice tiers, drift, and ergodicity

This module formalizes one seven-reaction, genuinely coupled two-species mass-action network.
For this specific network and every positive rate vector, it proves strong endotacticity,
constructs a count-lattice tier certificate, computes a Foster–Lyapunov drift bound, proves
irreducibility, and derives non-explosion, positive recurrence, geometric ergodicity, and a
hitting-tail estimate from the repository's count-lattice tier machinery. These results concern
this concrete network; the module does not claim a stochastic recurrence theorem for all strongly
endotactic networks.

The deterministic tier terminology follows G. Craciun, *Tiers, subcycles and reaction networks*,
J. Differential Equations **245** (2006), 559–592. The stochastic conclusions below are derived
through the repository's `CRNT.Stochastic.EndotacticTierPositiveRecurrence` criteria.

## The network

Species `A` (index `0`) and `B` (index `1`); seven channels:

| `r` | reaction          | source | target | propensity              | `w`-rate (`w = (1,1)`) |
|-----|-------------------|--------|--------|-------------------------|-----------------------|
| `0` | `0 → A`           | `0`    | `A`    | `κ₀`                    | `+1`                  |
| `1` | `0 → B`           | `0`    | `B`    | `κ₁`                    | `+1`                  |
| `2` | `2A → A`          | `2A`   | `A`    | `κ₂ · n(A)^{↓2}`        | `−1`                  |
| `3` | `2B → B`          | `2B`   | `B`    | `κ₃ · n(B)^{↓2}`        | `−1`                  |
| `4` | `A + B → A`       | `A+B`  | `A`    | `κ₄ · n(A) · n(B)`      | `−1`                  |
| `5` | `A → 0`           | `A`    | `0`    | `κ₅ · n(A)`             | `−1`                  |
| `6` | `B → 0`           | `B`    | `0`    | `κ₆ · n(B)`             | `−1`                  |

Channel `4` is the **coupling**: `A` catalyses the degradation of `B`, its propensity is the
*product* `n(A) · n(B)` of the two counts (`coupling_propensity`), so it vanishes when either
count is zero (`coupling_depends_on_A`, `coupling_depends_on_B`) and is strictly positive when
both counts are positive (`coupling_both`).  This is the property that the two-species instance
of `CRNT.Stochastic.EndotacticTwoSpecies` — a *product* of two one-species systems — does not
have.

**Remark (why this coupling).**  The most immediate candidate coupling, `A + B → 2B` (with
`A → B` and `B → A`), is *not* strongly endotactic: in the direction `w = (0, 1)` the source
complexes `B` and `A + B` are both `w`-maximal (both have `w`-value `1`), and the rate of
`A + B → 2B` in that direction is `w · (−1, +1) = +1 > 0`, i.e. a channel out of the `w`-maximal
face ascends the tier potential, which violates endotacticity.  The coupling used here,
`A + B → A`, has rate `w · (0, −1) = −b`, so it never ascends the tier potential and can be
placed on the top tier together with the single-species complexes `2A` and `2B`.

## The mathematics

### 1. Strong endotacticity

The source complexes of the network are `0`, `A`, `B`, `2A`, `2B` and `A+B`, whose `w`-values in
the direction `w = (a, b)` are `0`, `a`, `b`, `2a`, `2b` and `a+b`.  The characterisation of the
`w`-maximal sources (`isMaxSource_birthA`, `isMaxSource_birthB`, `isMaxSource_annA`,
`isMaxSource_annB`, `isMaxSource_catal`, `isMaxSource_deathA`, `isMaxSource_deathB`) is:

* the empty complex is `w`-maximal iff `a ≤ 0` and `b ≤ 0`;
* `2A` is `w`-maximal iff `0 ≤ a` and `b ≤ a`;  `2B` is `w`-maximal iff `0 ≤ b` and `a ≤ b`;
* `A+B` is `w`-maximal iff `a = b` and `0 ≤ a`;
* `A` is `w`-maximal iff `a = 0` and `b ≤ 0`;  `B` is `w`-maximal iff `b = 0` and `a ≤ 0`.

Every channel out of a `w`-maximal source has nonpositive `w`-rate, and for every stoichiometrically
active direction there is a `w`-maximal channel with strictly negative `w`-rate
(`stronglyEndotacticStd`); the network is therefore **strongly endotactic** in the standard
sense (`CRNT.Network.StronglyEndotacticStd`).  This certifies the geometric condition for this
network; strong endotacticity alone is not used as a stochastic recurrence theorem.

### 2. The count-lattice tier weight

The tier weight is the total-count direction `w = (1, 1)` (`tierWeight`).  Its top tier consists
of the three complexes `2A`, `2B` and `A+B` (all of `w`-value `2`); the channels `2A → A` and
`2B → B` descend it strictly, and the coupling channel `A + B → A` descends it as well.  The two
ascending channels `0 → A` and `0 → B` have the **empty** source complex, hence count-independent
propensities.  The network therefore carries the count-lattice tier structure `countTier`
(`CRNT.Network.CountTier`), and in particular the **count-lattice tier descent**
(`countTierDescent_net`), a count-lattice tier descent certificate for this network.

### 3. The count-lattice drift

The count-lattice tier Lyapunov function is `V (n) = n(A) + n(B)`, and the drift is *exact*
(`drift_eq`):

```
Q V (n) = (κ₀ + κ₁) − κ₂ n(A)^{↓2} − κ₃ n(B)^{↓2} − κ₄ n(A) n(B) − κ₅ n(A) − κ₆ n(B).
```

The coupling channel contributes the term `−κ₄ · n(A) · n(B)`: it is a strictly negative,
*genuinely coupled* contribution to the drift of the total count.  From it one reads the
multiplicative Foster–Lyapunov drift `Q V (n) ≤ −ε · V (n) + K` with `ε = min κ₂ κ₃ > 0` and
`K = κ₀ + κ₁ + κ₂ + κ₃ ≥ 0` (`drift_le`), and hence the **count-lattice tier drift certificate**
used by the count-lattice Foster machinery: a constant negative drift `≤ −1` outside a finite
set of counts
(`countTierDrift_certificate`).

### 4. The stochastic conclusion

* **non-explosion** (`nonExplosion`): the minimal transition function is stochastic;
* **positive recurrence** (`positiveRecurrence`): there is a stationary probability `π` charging
  **every** count (`0 < π b`) and `N.transition κ t a a → π a`;
* **geometric ergodicity** (`geometricErgodic`): the Meyn–Tweedie `V`-uniform estimate;
* **hitting time / return** (`fosterHittingTime`): the probability of not yet entering a finite
  set by time `t` is bounded by a constant multiple of `V(a) / t`, and entry occurs almost surely.

All four are obtained from the tier machinery of
`CRNT.Stochastic.EndotacticTierPositiveRecurrence` (`tier_nonExplosion`,
`tier_positiveRecurrence`, `tier_geometricErgodic`, `tierFoster_hitting_time`) once the
count-lattice tier structure `countTier` and the irreducibility of the embedded jump chain
(`reachPos`) are established.

Depends on: `CRNT.Stochastic.EndotacticTierPositiveRecurrence`.
-/

open Filter Topology
open scoped BigOperators

namespace CRNT
namespace Examples
namespace CoupledTwoSpecies

open Network

/-! ## 1. The network -/

/-- **The coupled two-species network.**  Species `A` (`0`) and `B` (`1`); the channels are
`0 → A`, `0 → B`, `2A → A`, `2B → B`, the **coupling** channel `A + B → A` (in which `A`
catalyses the degradation of `B`), `A → 0` and `B → 0`.  The propensity of the coupling channel
is `κ₄ · n(A) · n(B)`, so it depends on the counts of *both* species.

The theorems in this module establish stochastic stability for this particular strongly
endotactic network; they do not assert the same conclusion for the full class of such networks. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 7, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![0, 0], ![1, 0]⟩
    else if r = 1 then ⟨![0, 0], ![0, 1]⟩
    else if r = 2 then ⟨![2, 0], ![1, 0]⟩
    else if r = 3 then ⟨![0, 2], ![0, 1]⟩
    else if r = 4 then ⟨![1, 1], ![1, 0]⟩
    else if r = 5 then ⟨![1, 0], ![0, 0]⟩
    else ⟨![0, 1], ![0, 0]⟩⟩

/-- The count vector `(m, k)`: `m` molecules of `A` and `k` molecules of `B`. -/
def count (m k : ℕ) : Fin 2 → ℕ := fun s => if s = 0 then m else k

/-- **The tier weight of the instance**: the total-count direction `w = (1, 1)`. -/
def tierWeight : Fin 2 → ℝ := fun _ => 1

/-! ## 2. The `w`-values and `w`-rates of the seven channels -/

/-- The `w`-value of the source of the birth channel `0 → A` is `0`. -/
theorem wValue_birthA (w : Fin 2 → ℝ) : net.wValue w 0 = 0 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]

/-- The `w`-value of the source of the birth channel `0 → B` is `0`. -/
theorem wValue_birthB (w : Fin 2 → ℝ) : net.wValue w 1 = 0 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]

/-- The `w`-value of the source `2A` of the annihilation channel `2A → A` is `2a`. -/
theorem wValue_annA (w : Fin 2 → ℝ) : net.wValue w 2 = 2 * w 0 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]
  ring

/-- The `w`-value of the source `2B` of the annihilation channel `2B → B` is `2b`. -/
theorem wValue_annB (w : Fin 2 → ℝ) : net.wValue w 3 = 2 * w 1 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]
  ring

/-- The `w`-value of the source `A + B` of the coupling channel `A + B → A` is `a + b`. -/
theorem wValue_catal (w : Fin 2 → ℝ) : net.wValue w 4 = w 0 + w 1 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]

/-- The `w`-value of the source `A` of the death channel `A → 0` is `a`. -/
theorem wValue_deathA (w : Fin 2 → ℝ) : net.wValue w 5 = w 0 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]

/-- The `w`-value of the source `B` of the death channel `B → 0` is `b`. -/
theorem wValue_deathB (w : Fin 2 → ℝ) : net.wValue w 6 = w 1 := by
  simp [Network.wValue, Network.dotProduct, exponentVector]

/-- The `w`-rate of the birth channel `0 → A` is `a`: it ascends the tier potential. -/
theorem wRate_birthA (w : Fin 2 → ℝ) : net.wRate w 0 = w 0 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]

/-- The `w`-rate of the birth channel `0 → B` is `b`: it ascends the tier potential. -/
theorem wRate_birthB (w : Fin 2 → ℝ) : net.wRate w 1 = w 1 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]

/-- The `w`-rate of the annihilation channel `2A → A` is `−a`. -/
theorem wRate_annA (w : Fin 2 → ℝ) : net.wRate w 2 = -w 0 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
  ring

/-- The `w`-rate of the annihilation channel `2B → B` is `−b`. -/
theorem wRate_annB (w : Fin 2 → ℝ) : net.wRate w 3 = -w 1 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]
  ring

/-- The `w`-rate of the **coupling** channel `A + B → A` is `−b`: the channel destroys one
molecule of `B` and leaves the count of `A` unchanged, so it descends the tier potential in the
direction `w = (1, 1)`. -/
theorem wRate_catal (w : Fin 2 → ℝ) : net.wRate w 4 = -w 1 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]

/-- The `w`-rate of the death channel `A → 0` is `−a`. -/
theorem wRate_deathA (w : Fin 2 → ℝ) : net.wRate w 5 = -w 0 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]

/-- The `w`-rate of the death channel `B → 0` is `−b`. -/
theorem wRate_deathB (w : Fin 2 → ℝ) : net.wRate w 6 = -w 1 := by
  simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply]

/-! ## 3. The `w`-maximal sources -/

/-- The empty source complex is `w`-maximal iff both coordinates of `w` are nonpositive. -/
theorem isMaxSource_birthA (w : Fin 2 → ℝ) :
    net.IsMaxSource w 0 ↔ (w 0 ≤ 0 ∧ w 1 ≤ 0) := by
  constructor
  · intro h
    have h5 := h 5
    have h6 := h 6
    rw [wValue_deathA, wValue_birthA] at h5
    rw [wValue_deathB, wValue_birthA] at h6
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩ r'
    fin_cases r' <;> simp [Network.wValue, Network.dotProduct, exponentVector] <;> linarith

/-- The empty source complex is `w`-maximal iff both coordinates of `w` are nonpositive
(the birth channel `0 → B` has the same source complex as `0 → A`). -/
theorem isMaxSource_birthB (w : Fin 2 → ℝ) :
    net.IsMaxSource w 1 ↔ (w 0 ≤ 0 ∧ w 1 ≤ 0) := by
  constructor
  · intro h
    have h5 := h 5
    have h6 := h 6
    rw [wValue_deathA, wValue_birthB] at h5
    rw [wValue_deathB, wValue_birthB] at h6
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩ r'
    fin_cases r' <;> simp [Network.wValue, Network.dotProduct, exponentVector] <;> linarith

/-- The source complex `2A` of the annihilation channel `2A → A` is `w`-maximal iff `0 ≤ a` and
`b ≤ a`. -/
theorem isMaxSource_annA (w : Fin 2 → ℝ) :
    net.IsMaxSource w 2 ↔ (0 ≤ w 0 ∧ w 1 ≤ w 0) := by
  constructor
  · intro h
    have h0 := h 0
    have h3 := h 3
    rw [wValue_birthA, wValue_annA] at h0
    rw [wValue_annB, wValue_annA] at h3
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩ r'
    fin_cases r' <;> simp [Network.wValue, Network.dotProduct, exponentVector] <;> linarith

/-- The source complex `2B` of the annihilation channel `2B → B` is `w`-maximal iff `0 ≤ b` and
`a ≤ b`. -/
theorem isMaxSource_annB (w : Fin 2 → ℝ) :
    net.IsMaxSource w 3 ↔ (0 ≤ w 1 ∧ w 0 ≤ w 1) := by
  constructor
  · intro h
    have h0 := h 0
    have h2 := h 2
    rw [wValue_birthA, wValue_annB] at h0
    rw [wValue_annA, wValue_annB] at h2
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩ r'
    fin_cases r' <;> simp [Network.wValue, Network.dotProduct, exponentVector] <;> linarith

/-- The source complex `A + B` of the coupling channel is `w`-maximal iff `a = b` and `0 ≤ a`. -/
theorem isMaxSource_catal (w : Fin 2 → ℝ) :
    net.IsMaxSource w 4 ↔ (w 0 = w 1 ∧ 0 ≤ w 0) := by
  constructor
  · intro h
    have h0 := h 0
    have h2 := h 2
    have h3 := h 3
    rw [wValue_birthA, wValue_catal] at h0
    rw [wValue_annA, wValue_catal] at h2
    rw [wValue_annB, wValue_catal] at h3
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨hab, ha⟩ r'
    fin_cases r' <;> simp [Network.wValue, Network.dotProduct, exponentVector] <;> linarith

/-- The source complex `A` of the death channel `A → 0` is `w`-maximal iff `a = 0` and `b ≤ 0`. -/
theorem isMaxSource_deathA (w : Fin 2 → ℝ) :
    net.IsMaxSource w 5 ↔ (w 0 = 0 ∧ w 1 ≤ 0) := by
  constructor
  · intro h
    have h0 := h 0
    have h2 := h 2
    have h6 := h 6
    rw [wValue_birthA, wValue_deathA] at h0
    rw [wValue_annA, wValue_deathA] at h2
    rw [wValue_deathB, wValue_deathA] at h6
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩ r'
    fin_cases r' <;> simp [Network.wValue, Network.dotProduct, exponentVector] <;> linarith

/-- The source complex `B` of the death channel `B → 0` is `w`-maximal iff `b = 0` and `a ≤ 0`. -/
theorem isMaxSource_deathB (w : Fin 2 → ℝ) :
    net.IsMaxSource w 6 ↔ (w 1 = 0 ∧ w 0 ≤ 0) := by
  constructor
  · intro h
    have h0 := h 0
    have h3 := h 3
    have h5 := h 5
    rw [wValue_birthA, wValue_deathB] at h0
    rw [wValue_annB, wValue_deathB] at h3
    rw [wValue_deathA, wValue_deathB] at h5
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨ha, hb⟩ r'
    fin_cases r' <;> simp [Network.wValue, Network.dotProduct, exponentVector] <;> linarith

/-! ## 4. Strong endotacticity -/

/-- **The coupled network is strongly endotactic.**

Every channel out of a `w`-maximal source has nonpositive `w`-rate (endotacticity), and for
every stoichiometrically active direction there is a `w`-maximal channel with strictly negative
`w`-rate (strong endotacticity).  This is the geometric condition used by the tier construction below; it is not itself a
stochastic recurrence conclusion. -/
theorem stronglyEndotacticStd : net.StronglyEndotacticStd := by
  refine ⟨?_, ?_⟩
  · -- endotacticity: no channel out of a `w`-maximal source ascends the tier potential
    intro w r hmax
    fin_cases r
    · show net.wRate w 0 ≤ 0
      have hmax' : net.IsMaxSource w 0 := hmax
      rw [wRate_birthA]; exact (isMaxSource_birthA w).mp hmax' |>.1
    · show net.wRate w 1 ≤ 0
      have hmax' : net.IsMaxSource w 1 := hmax
      rw [wRate_birthB]; exact (isMaxSource_birthB w).mp hmax' |>.2
    · show net.wRate w 2 ≤ 0
      have hmax' : net.IsMaxSource w 2 := hmax
      rw [wRate_annA]
      exact neg_nonpos.mpr ((isMaxSource_annA w).mp hmax').1
    · show net.wRate w 3 ≤ 0
      have hmax' : net.IsMaxSource w 3 := hmax
      rw [wRate_annB]
      exact neg_nonpos.mpr ((isMaxSource_annB w).mp hmax').1
    · show net.wRate w 4 ≤ 0
      have hmax' : net.IsMaxSource w 4 := hmax
      rw [wRate_catal]
      have h := (isMaxSource_catal w).mp hmax'
      have h' : 0 ≤ w 1 := by linarith [h.1, h.2]
      exact neg_nonpos.mpr h'
    · show net.wRate w 5 ≤ 0
      have hmax' : net.IsMaxSource w 5 := hmax
      rw [wRate_deathA]
      have h := (isMaxSource_deathA w).mp hmax'
      rw [h.1]
      linarith
    · show net.wRate w 6 ≤ 0
      have hmax' : net.IsMaxSource w 6 := hmax
      rw [wRate_deathB]
      have h := (isMaxSource_deathB w).mp hmax'
      rw [h.1]
      linarith
  · -- strong endotacticity: a strictly descending `w`-maximal channel in every active direction
    intro w hactive
    by_cases ha : 0 < w 0
    · by_cases hb : w 1 ≤ w 0
      · refine ⟨2, (isMaxSource_annA w).2 ⟨le_of_lt ha, hb⟩, ?_⟩
        rw [wRate_annA]; linarith
      · refine ⟨3, (isMaxSource_annB w).2 ⟨by linarith, by linarith⟩, ?_⟩
        rw [wRate_annB]; linarith
    · by_cases hb : 0 < w 1
      · refine ⟨3, (isMaxSource_annB w).2 ⟨le_of_lt hb, by linarith⟩, ?_⟩
        rw [wRate_annB]; linarith
      · by_cases ha0 : w 0 < 0
        · refine ⟨0, (isMaxSource_birthA w).2 ⟨by linarith, by linarith⟩, ?_⟩
          rw [wRate_birthA]; linarith
        · by_cases hb0 : w 1 < 0
          · refine ⟨1, (isMaxSource_birthB w).2 ⟨by linarith, by linarith⟩, ?_⟩
            rw [wRate_birthB]; linarith
          · -- `w = 0`: the direction is not stoichiometrically active
            have hw0 : w 0 = 0 := by linarith
            have hw1 : w 1 = 0 := by linarith
            exfalso
            obtain ⟨r, hr⟩ := hactive
            fin_cases r <;>
              simp [Network.wRate, Network.dotProduct, Network.reactionVector_apply, hw0, hw1] at hr

/-! ## 5. The propensities: the coupling is genuine -/

/-- The propensity of the birth channel `0 → A` is the constant `κ₀`. -/
theorem rate_birthA (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n 0 = κ.k 0 := by
  unfold Network.stochasticMassActionRate
  simp

/-- The propensity of the birth channel `0 → B` is the constant `κ₁`. -/
theorem rate_birthB (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n 1 = κ.k 1 := by
  unfold Network.stochasticMassActionRate
  simp

/-- The propensity of the annihilation channel `2A → A` is `κ₂ · n(A)^{↓2}`. -/
theorem rate_annA (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n 2 = κ.k 2 * ((n 0).descFactorial 2 : ℝ) := by
  unfold Network.stochasticMassActionRate
  simp

/-- The propensity of the annihilation channel `2B → B` is `κ₃ · n(B)^{↓2}`. -/
theorem rate_annB (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n 3 = κ.k 3 * ((n 1).descFactorial 2 : ℝ) := by
  unfold Network.stochasticMassActionRate
  simp

/-- **The propensity of the coupling channel `A + B → A` is `κ₄ · n(A) · n(B)`.**  It is the
product of the counts of the two species: the channel is genuinely coupled, and this is the
first point at which the instance of this module differs from the *product* two-species instance
of `CRNT.Stochastic.EndotacticTwoSpecies`.

Mathematically: the count-lattice analogue of the mass-action monomial `x_A · x_B` of the
complex `A + B` is the falling-factorial product `n(A)^{↓1} · n(B)^{↓1} = n(A) · n(B)`, which is the
propensity used in the drift computation. -/
theorem coupling_propensity (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n 4 = κ.k 4 * ((n 0 : ℝ) * (n 1 : ℝ)) := by
  unfold Network.stochasticMassActionRate
  simp

/-- The propensity of the death channel `A → 0` is `κ₅ · n(A)`. -/
theorem rate_deathA (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n 5 = κ.k 5 * (n 0 : ℝ) := by
  unfold Network.stochasticMassActionRate
  simp

/-- The propensity of the death channel `B → 0` is `κ₆ · n(B)`. -/
theorem rate_deathB (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.stochasticMassActionRate κ n 6 = κ.k 6 * (n 1 : ℝ) := by
  unfold Network.stochasticMassActionRate
  simp

/-- The count of `A` in the count vector `(m, k)`. -/
theorem count_A (m k : ℕ) : count m k 0 = m := by
  simp [count]

/-- The count of `B` in the count vector `(m, k)`. -/
theorem count_B (m k : ℕ) : count m k 1 = k := by
  simp [count]

/-- **The propensity of the coupling channel depends on the count of `B`.**  At the count
`(3, 0)` the coupling channel is silent although three molecules of `A` are present: the
count-lattice propensity of the coupled channel is a product of the two counts, as in
Anderson–Cappelletti–Kim–Nguyen (2020), §3. -/
theorem coupling_depends_on_B (κ : net.RateConstants) :
    net.stochasticMassActionRate κ (count 3 0) 4 = 0 := by
  rw [coupling_propensity, count_A, count_B]
  ring

/-- **The propensity of the coupling channel depends on the count of `A`.**  At the count
`(0, 5)` the coupling channel is silent although five molecules of `B` are present. -/
theorem coupling_depends_on_A (κ : net.RateConstants) :
    net.stochasticMassActionRate κ (count 0 5) 4 = 0 := by
  rw [coupling_propensity, count_A, count_B]
  ring

/-- **The coupling channel fires when both species are present.**  At the count `(3, 5)` the
propensity of the coupling channel is `15 κ₄`, which is strictly positive. -/
theorem coupling_both (κ : net.RateConstants) :
    net.stochasticMassActionRate κ (count 3 5) 4 = κ.k 4 * 15 ∧
      0 < net.stochasticMassActionRate κ (count 3 5) 4 := by
  rw [coupling_propensity, count_A, count_B]
  constructor
  · ring
  · exact mul_pos (κ.positive 4) (by norm_num)

/-- The coupling channel is *not* a self-loop of the count lattice: it changes the count of
`B` while leaving the count of `A` unchanged. -/
theorem coupling_changes_state (κ : net.RateConstants) (m k : ℕ) (hm : 1 ≤ m) :
    (net.jumpSystem κ).next (4 : Fin 7) (count m k) = count m (k - 1) := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, count] ; omega

/-! ## 6. The count-lattice tier structure -/

/-- **The count-lattice tier structure of the coupled instance.**  The tier weight is the
total-count direction `w = (1, 1)`; the top tier consists of the complexes `2A`, `2B` and `A+B`,
the channels `2A → A` and `2B → B` descend it strictly, the only ascending channels
`0 → A` and `0 → B` have the empty source complex (hence count-independent propensities), and
each species is consumed by a strictly descending top-tier channel supported on it alone.

This is the count-lattice tier structure of Craciun (2006) / Anderson–Cappelletti–Kim–Nguyen
(2020), §4, for the present network; it is what the count-lattice transfer
(`CRNT.Network.tierDrift_multiplicative`) consumes. -/
noncomputable def countTier : CountTier net where
  w := tierWeight
  hw := by intro s; fin_cases s <;> simp [tierWeight]
  chain := countTierChain_of_linear net tierWeight
  descent := countTierDescent_of_stronglyEndotacticStd stronglyEndotacticStd (by
    refine ⟨0, ?_⟩
    rw [wRate_birthA]; simp [tierWeight])
  inflow := by
    intro r hr s
    fin_cases r
    · show (net.reaction 0).source s = 0
      have hr' : net.wRate tierWeight 0 > 0 := hr
      rw [wRate_birthA] at hr'
      simp only [tierWeight] at hr'
      fin_cases s <;> simp
    · show (net.reaction 1).source s = 0
      have hr' : net.wRate tierWeight 1 > 0 := hr
      rw [wRate_birthB] at hr'
      simp only [tierWeight] at hr'
      fin_cases s <;> simp
    · show (net.reaction 2).source s = 0
      have hr' : net.wRate tierWeight 2 > 0 := hr
      rw [wRate_annA] at hr'
      simp only [tierWeight] at hr'
      exfalso
      linarith
    · show (net.reaction 3).source s = 0
      have hr' : net.wRate tierWeight 3 > 0 := hr
      rw [wRate_annB] at hr'
      simp only [tierWeight] at hr'
      exfalso
      linarith
    · show (net.reaction 4).source s = 0
      have hr' : net.wRate tierWeight 4 > 0 := hr
      rw [wRate_catal] at hr'
      simp only [tierWeight] at hr'
      exfalso
      linarith
    · show (net.reaction 5).source s = 0
      have hr' : net.wRate tierWeight 5 > 0 := hr
      rw [wRate_deathA] at hr'
      simp only [tierWeight] at hr'
      exfalso
      linarith
    · show (net.reaction 6).source s = 0
      have hr' : net.wRate tierWeight 6 > 0 := hr
      rw [wRate_deathB] at hr'
      simp only [tierWeight] at hr'
      exfalso
      linarith
  coverage := by
    intro s
    fin_cases s
    · refine ⟨2, ?_, ?_, ?_, ?_⟩
      · refine (isMaxSource_annA tierWeight).2 ⟨by simp [tierWeight], by simp [tierWeight]⟩
      · rw [wRate_annA]; simp [tierWeight]
      · simp
      · intro t ht
        fin_cases t
        · simp at ht
        · show (net.reaction 2).source 1 = 0
          simp
    · refine ⟨3, ?_, ?_, ?_, ?_⟩
      · refine (isMaxSource_annB tierWeight).2 ⟨by simp [tierWeight], by simp [tierWeight]⟩
      · rw [wRate_annB]; simp [tierWeight]
      · simp
      · intro t ht
        fin_cases t
        · show (net.reaction 3).source 0 = 0
          simp
        · simp at ht

/-- **The count-lattice tier descent of the coupled instance** (ACK 2020; the deterministic
tier theory of `CRNT.Dynamics.StrongEndotacticTier`): in the tier direction `w = (1, 1)` no
channel out of the top tier ascends the tier potential, and the channels `2A → A` and `2B → B`
descend it strictly. -/
theorem countTierDescent_net : net.CountTierDescent tierWeight :=
  countTierDescent_of_stronglyEndotacticStd stronglyEndotacticStd (by
    refine ⟨0, ?_⟩
    rw [wRate_birthA]; simp [tierWeight])

/-- **The count-lattice tier weight of the coupled instance is strictly positive.** -/
theorem tierWeight_pos (s : Fin 2) : 0 < tierWeight s := by
  fin_cases s <;> simp [tierWeight]

/-- **The count-lattice tier Lyapunov function of the coupled instance is the total count.**
`V (n) = n(A) + n(B)`.  It is the count-lattice extension of the tier weight, as in
Anderson–Cappelletti–Kim–Nguyen (2020), §4. -/
theorem countLyapunov_eq (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    CountLyapunov net κ countTier n = (n 0 : ℝ) + (n 1 : ℝ) := by
  have h : CountLyapunov net κ countTier = linearObservable tierWeight := rfl
  rw [h]
  simp [linearObservable, Fin.sum_univ_two, tierWeight]

/-! ## 7. The count-lattice drift -/

/-- The falling factorial of degree two dominates the count minus one: `n^{↓2} ≥ n − 1`. -/
theorem descFactorial_two_ge (n : ℕ) : ((n.descFactorial 2 : ℝ)) ≥ (n : ℝ) - 1 := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have hz : n.descFactorial 2 = 0 := (Nat.descFactorial_eq_zero_iff_lt).mpr (by omega)
    have h1 : (n : ℝ) ≤ 1 := by exact_mod_cast (by omega)
    rw [hz]; push_cast; linarith
  · have h1 := nat_descFactorial_ge_self (n := n) (k := 2) (by omega) h
    have h2 : ((n.descFactorial 2 : ℝ)) ≥ (n : ℝ) := by exact_mod_cast h1
    linarith

/-- **The exact drift of the count-lattice tier Lyapunov function.**

```
Q V (n) = (κ₀ + κ₁) − κ₂ n(A)^{↓2} − κ₃ n(B)^{↓2} − κ₄ n(A) n(B) − κ₅ n(A) − κ₆ n(B).
```

The coupling channel `A + B → A` contributes the strictly negative, genuinely coupled term
`−κ₄ · n(A) · n(B)`: it is the *product* of the two counts that appears in the drift of the
total count.  This is the count-lattice counterpart of the deterministic tier computation of
Craciun (2006) and Anderson–Cappelletti–Kim–Nguyen (2020). -/
theorem drift_eq (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.observableGenerator κ (CountLyapunov net κ countTier) n =
      (κ.k 0 + κ.k 1) - κ.k 2 * ((n 0).descFactorial 2 : ℝ)
        - κ.k 3 * ((n 1).descFactorial 2 : ℝ) - κ.k 4 * ((n 0 : ℝ) * (n 1 : ℝ))
        - κ.k 5 * (n 0 : ℝ) - κ.k 6 * (n 1 : ℝ) := by
  have hV : CountLyapunov net κ countTier = linearObservable tierWeight := rfl
  rw [hV, Network.observableGenerator_linear]
  rw [Fin.sum_univ_seven]
  simp only [Fin.sum_univ_two]
  simp only [rate_birthA, rate_birthB, rate_annA, rate_annB, coupling_propensity, rate_deathA,
    rate_deathB]
  simp [tierWeight]
  ring

/-- **The multiplicative Foster--Lyapunov drift of the coupled instance.**  The count-lattice
tier Lyapunov function `V (n) = n(A) + n(B)` satisfies `Q V (n) ≤ −ε · V (n) + K` with
`ε = min κ₂ κ₃ > 0` and `K = κ₀ + κ₁ + κ₂ + κ₃ ≥ 0`.

This is the Foster--Lyapunov drift bound used below, read off from the exact drift `drift_eq`. -/
theorem drift_le (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.observableGenerator κ (CountLyapunov net κ countTier) n
      ≤ -min (κ.k 2) (κ.k 3) * CountLyapunov net κ countTier n
        + (κ.k 0 + κ.k 1 + κ.k 2 + κ.k 3) := by
  have hV : CountLyapunov net κ countTier n = (n 0 : ℝ) + (n 1 : ℝ) := countLyapunov_eq κ n
  have hκ2 : 0 ≤ κ.k 2 := (κ.positive 2).le
  have hκ3 : 0 ≤ κ.k 3 := (κ.positive 3).le
  have hA : -(κ.k 2 : ℝ) * ((n 0).descFactorial 2 : ℝ)
      ≤ -κ.k 2 * (n 0 : ℝ) + κ.k 2 := by
    have h := descFactorial_two_ge (n 0)
    have hmul : κ.k 2 * ((n 0).descFactorial 2 : ℝ) ≥ κ.k 2 * ((n 0 : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h hκ2
    linarith
  have hB : -(κ.k 3 : ℝ) * ((n 1).descFactorial 2 : ℝ)
      ≤ -κ.k 3 * (n 1 : ℝ) + κ.k 3 := by
    have h := descFactorial_two_ge (n 1)
    have hmul : κ.k 3 * ((n 1).descFactorial 2 : ℝ) ≥ κ.k 3 * ((n 1 : ℝ) - 1) :=
      mul_le_mul_of_nonneg_left h hκ3
    linarith
  have hC : -(κ.k 4 : ℝ) * ((n 0 : ℝ) * (n 1 : ℝ)) ≤ 0 := by
    have h : 0 ≤ (κ.k 4 : ℝ) * ((n 0 : ℝ) * (n 1 : ℝ)) :=
      mul_nonneg (κ.positive 4).le
        (mul_nonneg (Nat.cast_nonneg (n 0)) (Nat.cast_nonneg (n 1)))
    linarith
  have hD : -(κ.k 5 : ℝ) * (n 0 : ℝ) ≤ 0 := by
    have h : 0 ≤ (κ.k 5 : ℝ) * (n 0 : ℝ) :=
      mul_nonneg (κ.positive 5).le (Nat.cast_nonneg (n 0))
    linarith
  have hE : -(κ.k 6 : ℝ) * (n 1 : ℝ) ≤ 0 := by
    have h : 0 ≤ (κ.k 6 : ℝ) * (n 1 : ℝ) :=
      mul_nonneg (κ.positive 6).le (Nat.cast_nonneg (n 1))
    linarith
  have hmin0 : min (κ.k 2) (κ.k 3) * (n 0 : ℝ) ≤ κ.k 2 * (n 0 : ℝ) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  have hmin1 : min (κ.k 2) (κ.k 3) * (n 1 : ℝ) ≤ κ.k 3 * (n 1 : ℝ) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
  have hstep1 : net.observableGenerator κ (CountLyapunov net κ countTier) n
      ≤ (κ.k 0 + κ.k 1 + κ.k 2 + κ.k 3) - κ.k 2 * (n 0 : ℝ) - κ.k 3 * (n 1 : ℝ) := by
    rw [drift_eq]
    linarith
  have hstep2 : (κ.k 0 + κ.k 1 + κ.k 2 + κ.k 3) - κ.k 2 * (n 0 : ℝ) - κ.k 3 * (n 1 : ℝ)
      ≤ (κ.k 0 + κ.k 1 + κ.k 2 + κ.k 3) - min (κ.k 2) (κ.k 3) * ((n 0 : ℝ) + (n 1 : ℝ)) := by
    have hsum : min (κ.k 2) (κ.k 3) * ((n 0 : ℝ) + (n 1 : ℝ))
        = min (κ.k 2) (κ.k 3) * (n 0 : ℝ) + min (κ.k 2) (κ.k 3) * (n 1 : ℝ) := by ring
    rw [hsum]
    linarith
  calc net.observableGenerator κ (CountLyapunov net κ countTier) n
      ≤ (κ.k 0 + κ.k 1 + κ.k 2 + κ.k 3) - κ.k 2 * (n 0 : ℝ) - κ.k 3 * (n 1 : ℝ) := hstep1
    _ ≤ (κ.k 0 + κ.k 1 + κ.k 2 + κ.k 3) - min (κ.k 2) (κ.k 3) * ((n 0 : ℝ) + (n 1 : ℝ)) :=
      hstep2
    _ = -min (κ.k 2) (κ.k 3) * CountLyapunov net κ countTier n
        + (κ.k 0 + κ.k 1 + κ.k 2 + κ.k 3) := by
      rw [hV]
      ring

/-- **A count-lattice tier drift certificate for the coupled instance.** The count-lattice tier
Lyapunov function has a constant negative drift `≤ −1` outside a finite set of counts. -/
theorem countTierDrift_certificate (κ : net.RateConstants) :
    ∃ D : CountTierDrift net κ, D.V = CountLyapunov net κ countTier :=
  tierDrift_le net κ countTier

/-- **The count-lattice drift condition for the coupled instance.** There are a constant `c > 0`
and a finite set `C` of counts such that the drift of the count-lattice tier Lyapunov function is
at most `−c` outside `C`. This is the drift condition consumed by the repository's
`CRNT.Network.tierFoster_hitting_time`, `CRNT.Network.tier_nonExplosion` and
`CRNT.Network.tier_positiveRecurrence` results. -/
theorem ack_drift_condition (κ : net.RateConstants) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : Set (Fin 2 → ℕ), C.Finite ∧
      ∀ n, n ∉ C → net.observableGenerator κ (CountLyapunov net κ countTier) n ≤ -c := by
  obtain ⟨D, hD⟩ := tierDrift_le net κ countTier
  refine ⟨D.c, D.hc, D.C, D.hC, ?_⟩
  intro n hn
  rw [← hD]
  exact D.hdrift n hn

/-! ## 8. Irreducibility of the embedded jump chain -/

/-- The birth channel `0 → A` increases the count of `A` by one. -/
theorem next_birthA (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (0 : Fin 7) (count m k) = count (m + 1) k := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, count]

/-- The birth channel `0 → B` increases the count of `B` by one. -/
theorem next_birthB (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (1 : Fin 7) (count m k) = count m (k + 1) := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, count]

/-- The death channel `A → 0` decreases the count of `A` by one. -/
theorem next_deathA (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (5 : Fin 7) (count (m + 1) k) = count m k := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, count]

/-- The death channel `B → 0` decreases the count of `B` by one. -/
theorem next_deathB (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (6 : Fin 7) (count m (k + 1)) = count m k := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, count]

/-- **The embedded jump chain of the coupled instance is irreducible.**  From any count one
reaches the origin by firing the death channels `A → 0` and `B → 0` (each of positive rate as
long as the corresponding count is positive), and from the origin one reaches any count by
firing the birth channels `0 → A` and `0 → B`.

This supplies the irreducibility premise used by the repository's count-lattice recurrence
results for this network. -/
theorem reachPos (κ : net.RateConstants) (a b : Fin 2 → ℕ) :
    (net.jumpSystem κ).ReachPos a b := by
  have killA : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (count m k) (count 0 k) := by
    intro m k
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
        refine Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨(5 : Fin 7), ?_, ?_⟩) ih
        · rw [show (net.jumpSystem κ).rate (5 : Fin 7) (count (m + 1) k)
              = net.stochasticMassActionRate κ (count (m + 1) k) 5 from rfl, rate_deathA]
          exact mul_pos (κ.positive 5) (by exact_mod_cast Nat.succ_pos m)
        · rw [next_deathA]
  have killB : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (count m k) (count m 0) := by
    intro m k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
        refine Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨(6 : Fin 7), ?_, ?_⟩) ih
        · rw [show (net.jumpSystem κ).rate (6 : Fin 7) (count m (k + 1))
              = net.stochasticMassActionRate κ (count m (k + 1)) 6 from rfl, rate_deathB]
          exact mul_pos (κ.positive 6) (by exact_mod_cast Nat.succ_pos k)
        · rw [next_deathB]
  have growA : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (count 0 k) (count m k) := by
    intro m k
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
        refine Relation.ReflTransGen.trans ih
          (Relation.ReflTransGen.single ⟨(0 : Fin 7), ?_, ?_⟩)
        · rw [show (net.jumpSystem κ).rate (0 : Fin 7) (count m k)
              = net.stochasticMassActionRate κ (count m k) 0 from rfl, rate_birthA]
          exact κ.positive 0
        · rw [next_birthA]
  have growB : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (count m 0) (count m k) := by
    intro m k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
        refine Relation.ReflTransGen.trans ih
          (Relation.ReflTransGen.single ⟨(1 : Fin 7), ?_, ?_⟩)
        · rw [show (net.jumpSystem κ).rate (1 : Fin 7) (count m k)
              = net.stochasticMassActionRate κ (count m k) 1 from rfl, rate_birthB]
          exact κ.positive 1
        · rw [next_birthB]
  have toZero : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (count m k) (count 0 0) :=
    fun m k => Relation.ReflTransGen.trans (killA m k) (killB 0 k)
  have fromZero : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (count 0 0) (count m k) :=
    fun m k => Relation.ReflTransGen.trans (growA m 0) (growB m k)
  rw [show a = count (a 0) (a 1) from by
    funext s; fin_cases s <;> simp [count]]
  rw [show b = count (b 0) (b 1) from by
    funext s; fin_cases s <;> simp [count]]
  exact Relation.ReflTransGen.trans (toZero (a 0) (a 1)) (fromZero (b 0) (b 1))

/-! ## 9. Stochastic consequences for the coupled instance -/

/-- **Non-explosion of the coupled instance.**  The stochastic mass-action chain of the coupled
two-species network defined above makes only finitely many jumps in a finite time interval: its
minimal transition function is stochastic. -/
theorem nonExplosion (κ : net.RateConstants) {t : ℝ} (ht : 0 ≤ t) (n : Fin 2 → ℕ) :
    HasSum (fun m => net.transition κ t n m) 1 :=
  tier_nonExplosion net κ countTier ht n

/-- **Positive recurrence of the coupled instance.**  The stochastic mass-action chain of the
coupled two-species network defined above is non-explosive and positively recurrent: it has a
stationary probability `π` which charges **every** count (`0 < π b`), and the probability of
being at the starting count converges to the strictly positive limit `π a`. -/
theorem positiveRecurrence (κ : net.RateConstants) :
    ∃ π : (Fin 2 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a : Fin 2 → ℕ, Tendsto (fun t => net.transition κ t a a) atTop (𝓝 (π a))) :=
  tier_positiveRecurrence net κ countTier (fun a b => reachPos κ a b)

/-- **Geometric ergodicity of the coupled instance.**  The chain satisfies the Meyn--Tweedie
`V`-uniform ergodicity estimate with the count-lattice tier Lyapunov function
`V (n) = n(A) + n(B)`. -/
theorem geometricErgodic (κ : net.RateConstants) :
    ∃ π : (Fin 2 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(net.jumpSystem κ).Pmin t a b - π b| *
            (1 + β * CountLyapunov net κ countTier b) ≤
          C₀ * (1 + CountLyapunov net κ countTier a) * ρ ^ ⌊t⌋₊ :=
  tier_geometricErgodic net κ countTier (fun a b => reachPos κ a b)

/-- **The Foster hitting-time statement for the coupled instance.**  There is a constant
`c > 0` and a finite set `C` such that the probability the chain has not entered `C` by time
`t > 0` is at most `V (a) / (c t)`, and the probability of being in `C` tends to one. This
hitting-tail bound follows from the repository's continuous-time Foster criterion applied to
the count-lattice tier drift. -/
theorem fosterHittingTime (κ : net.RateConstants) :
    ∃ c : ℝ, 0 < c ∧ ∃ C : Finset (Fin 2 → ℕ),
      ∀ a : Fin 2 → ℕ,
        (∀ t, 0 < t →
            1 - ∑ b ∈ C, ((net.jumpSystem κ).stopOn C).Pmin t a b ≤
              CountLyapunov net κ countTier a / (c * t)) ∧
          Tendsto (fun t => ∑ b ∈ C, ((net.jumpSystem κ).stopOn C).Pmin t a b) atTop (𝓝 1) := by
  obtain ⟨D, hD⟩ := tierDrift_le net κ countTier
  refine ⟨D.c, D.hc, D.hC.toFinset, ?_⟩
  intro a
  have hh := tierFoster_hitting_time net κ countTier D.hc D.hC (fun n hn => ?_) a
  exact hh
  rw [← hD]
  exact D.hdrift n hn

#print axioms stronglyEndotacticStd
#print axioms countTierDescent_net
#print axioms coupling_propensity
#print axioms drift_eq
#print axioms drift_le
#print axioms ack_drift_condition
#print axioms nonExplosion
#print axioms positiveRecurrence
#print axioms geometricErgodic
#print axioms fosterHittingTime

end CoupledTwoSpecies
end Examples
end CRNT
