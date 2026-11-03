import CRNT.Stochastic.EndotacticTierDomination

/-!
# Positive recurrence of a two-species strongly endotactic network (the ACK conclusion)

This module discharges the Anderson–Cappelletti–Kim–Nguyen (ACK) conclusion for a **genuine
two-species** strongly endotactic stochastic mass-action system.

**Reference.** J. Anderson, A. Cappelletti, E. Kim and H. Nguyen, *Persistence and absence of
infinite trajectories for strongly endotactic chemical reaction networks*, Discrete and
Continuous Dynamical Systems **S** 14 (2020), 1107–1148.  The stochastic part of that paper
(their §5) asserts that a strongly endotactic stochastic mass-action system is
**non-explosive** and **positive recurrent**, with a strictly positive stationary law.

**The instance.** `CRNT.Examples.EndotacticCounterexample.net` is the two-species network

```
0 → A ,   A → 0 ,   0 → B ,   B → 0
```

(species `Fin 2`, reactions `Fin 4`).  It is *strongly endotactic* in the standard sense
(`Examples.EndotacticCounterexample.stronglyEndotacticStd`), and its chain is a **product of two
independent birth–death chains**.  This module proves the ACK conclusion for it: the chain is
non-explosive, is positively recurrent with a stationary probability that charges **every**
count, and is **geometrically ergodic**.

This is the sharpest multispecies progress currently available in the library: the ACK
conclusion was previously proved only in the **one-species** case
(`CRNT.Network.OneSpecies.positiveRecurrence`, `CRNT.Examples.EndotacticBirthDeath`,
`CRNT.Examples.EndotacticTrimerDecay`).  The multispecies instance gap recorded by the field
map (leaf **P7**) is closed *for this instance*.

## The mathematics

### 1. The multiplicative Foster--Lyapunov drift

The observable is the **total count**

`V n = n(A) + n(B) = linearObservable twoSpeciesWeight n`,

the count-lattice extension of the tier weight `w = (1, 1)`.  The four channels have the
following propensity (`λ_r(n) = κ_r · n^{↓ y_r}`) and the following `w`-rate
(`⟨w, y'_r − y_r⟩`):

| `r` | reaction | `λ_r(n)`    | `w`-rate | contribution to `Q V` |
|-----|----------|-------------|----------|-----------------------|
| `0` | `0 → A`  | `κ₀`        | `+1`     | `+κ₀`                 |
| `1` | `A → 0`  | `κ₁ · n(A)` | `−1`     | `−κ₁ n(A)`            |
| `2` | `0 → B`  | `κ₂`        | `+1`     | `+κ₂`                 |
| `3` | `B → 0`  | `κ₃ · n(B)` | `−1`     | `−κ₃ n(B)`            |

Hence the drift is *exactly*

`Q V (n) = (κ₀ + κ₂) − (κ₁ · n(A) + κ₃ · n(B))`   (`twoSpecies_drift_eq`),

which is the **multiplicative Foster–Lyapunov drift**

`Q V (n) ≤ −ε · V (n) + K`,   `ε := min κ₁ κ₃ > 0`,   `K := κ₀ + κ₂ ≥ 0`

(`twoSpecies_drift`): the total count is pulled back towards the origin in every coordinate,
because each species has its own death channel, and the two birth channels have a
count-independent propensity.

### 2. Irreducibility

The embedded jump chain is **irreducible** (`twoSpecies_reachPos`): from any count one reaches
the origin by firing the death channels `A → 0` and `B → 0` (each of positive rate as long as
the corresponding count is positive), and from the origin one reaches any count by firing the
birth channels `0 → A` and `0 → B`.

### 3. The route: the continuous-time Foster criterion

From the multiplicative drift, the repository's continuous-time Foster machinery gives the
three conclusions:

* the minimal transition function is stochastic, i.e. the chain does not explode
  (`JumpSystem.hasSum_Pmin_one_of_drift_affine`): `twoSpecies_nonExplosion`;
* the chain is positively recurrent with a **strictly positive** stationary law
  (`JumpSystem.foster_lyapunov_ergodic`, which charges every state of the class):
  `twoSpecies_positiveRecurrence`;
* the chain is **geometrically ergodic** (`JumpSystem.geometric_ergodic`, the Meyn–Tweedie
  `V`-uniform estimate): `twoSpecies_geometricErgodic`.

The **continuous-time** version of Foster's criterion is the one that applies here: the
embedded-jump-chain version (`CRNT.Network.jumpChain_foster_hitting_time`) would require a
bounded exit rate, which an unbounded count lattice does not provide.

The same instance is also covered by the count-lattice tier structure of
`CRNT.Stochastic.EndotacticTierDomination` (`Examples.EndotacticCounterexample.countTier`, the
weight `w = (1, 1)`), whose tier Lyapunov function is exactly the observable `V` used here
(`twoSpecies_tierLyapunov`); the tier route (`CRNT.Network.tier_nonExplosion`,
`CRNT.Network.tier_positiveRecurrence`, `CRNT.Network.tier_geometricErgodic`) therefore gives
the same three conclusions.

## What is **not** proved here

The **general** multispecies ACK theorem is **not** proved: the deterministic tier-weight
construction of ACK — a weight whose tiers separate the complexes, together with the matching
of each descending channel to the ascending channels it dominates — is the missing input, and it
is not available on the count lattice.  The naive route, in which the top-tier monomial is
assumed to dominate the lower-tier monomials, is **refuted** by this very instance:
`Examples.EndotacticCounterexample.topTier_does_not_dominate` shows that along the escape
direction `n(A) = 0`, `n(B) → ∞` the count-lattice falling factorial of the lower tier `B`
*exceeds* that of the top tier `A`.  What this module shows is that the obstruction is a
property of the *weight*, not of the network: with the weight `w = (1, 1)` the two species
share the top tier, the two ascending channels have the empty source complex (hence
count-independent propensity) and each species is consumed by its own strictly descending
top-tier channel, and the ACK conclusion follows.

Depends on:
`CRNT.Stochastic.EndotacticTierDomination`, `CRNT.Stochastic.EndotacticTierPositiveRecurrence`,
`CRNT.Stochastic.HarrisTheorem`, `CRNT.Stochastic.MinimalSemigroupNonExplosion`,
`CRNT.Stochastic.MinimalSemigroupKrylovBogoliubov`.
-/

open Filter Topology
open scoped BigOperators

namespace CRNT
namespace Examples
namespace EndotacticCounterexample

open Network

/-- The tier weight `w = (1, 1)` of the instance: the total-count direction. -/
def twoSpeciesWeight : Fin 2 → ℝ := fun _ => 1

/-- The count vector `(m, k)`: `m` molecules of `A` and `k` molecules of `B`. -/
def twoSpeciesCount (m k : ℕ) : Fin 2 → ℕ := fun s => if s = 0 then m else k

/-- The total-count weight is strictly positive. -/
private theorem weight_pos (s : Fin 2) : 0 < twoSpeciesWeight s := by
  fin_cases s <;> simp [twoSpeciesWeight]

/-! ### The four channels of the instance -/

private theorem next_birthA (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (0 : Fin 4) (twoSpeciesCount m k) = twoSpeciesCount (m + 1) k := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, net, twoSpeciesCount]

private theorem next_deathA (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (1 : Fin 4) (twoSpeciesCount (m + 1) k) = twoSpeciesCount m k := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, net, twoSpeciesCount]

private theorem next_birthB (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (2 : Fin 4) (twoSpeciesCount m k) = twoSpeciesCount m (k + 1) := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, net, twoSpeciesCount]

private theorem next_deathB (κ : net.RateConstants) (m k : ℕ) :
    (net.jumpSystem κ).next (3 : Fin 4) (twoSpeciesCount m (k + 1)) = twoSpeciesCount m k := by
  funext s
  fin_cases s <;> simp [Network.jumpSystem, Network.jumpNextCount, net, twoSpeciesCount]

private theorem rate_birthA (κ : net.RateConstants) (m k : ℕ) :
    net.stochasticMassActionRate κ (twoSpeciesCount m k) 0 = κ.k 0 := by
  unfold Network.stochasticMassActionRate
  simp [net, twoSpeciesCount]

private theorem rate_deathA (κ : net.RateConstants) (m k : ℕ) :
    net.stochasticMassActionRate κ (twoSpeciesCount (m + 1) k) 1 = κ.k 1 * (m + 1 : ℝ) := by
  unfold Network.stochasticMassActionRate
  simp [net, twoSpeciesCount]

private theorem rate_birthB (κ : net.RateConstants) (m k : ℕ) :
    net.stochasticMassActionRate κ (twoSpeciesCount m k) 2 = κ.k 2 := by
  unfold Network.stochasticMassActionRate
  simp [net, twoSpeciesCount]

private theorem rate_deathB (κ : net.RateConstants) (m k : ℕ) :
    net.stochasticMassActionRate κ (twoSpeciesCount m (k + 1)) 3 = κ.k 3 * (k + 1 : ℝ) := by
  unfold Network.stochasticMassActionRate
  simp [net, twoSpeciesCount]

/-! ### Irreducibility -/

/-- **The embedded jump chain of the two-species instance is irreducible.**  From any count one
reaches the origin by firing the two death channels `A → 0` and `B → 0`; from the origin one
reaches any count by firing the two birth channels `0 → A` and `0 → B`.  Each of these firings
has a strictly positive rate, so the relation `ReachPos` of the jump system is satisfied. -/
theorem twoSpecies_reachPos (κ : net.RateConstants) (a b : Fin 2 → ℕ) :
    (net.jumpSystem κ).ReachPos a b := by
  -- kill all the molecules of `A`
  have killA : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (twoSpeciesCount m k)
      (twoSpeciesCount 0 k) := by
    intro m k
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
        refine Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨(1 : Fin 4), ?_, ?_⟩) ih
        · rw [show (net.jumpSystem κ).rate (1 : Fin 4) (twoSpeciesCount (m + 1) k)
              = net.stochasticMassActionRate κ (twoSpeciesCount (m + 1) k) 1 from rfl,
            rate_deathA]
          exact mul_pos (κ.positive 1) (by exact_mod_cast Nat.succ_pos m)
        · rw [next_deathA]
  -- kill all the molecules of `B`
  have killB : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (twoSpeciesCount m k)
      (twoSpeciesCount m 0) := by
    intro m k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
        refine Relation.ReflTransGen.trans
          (Relation.ReflTransGen.single ⟨(3 : Fin 4), ?_, ?_⟩) ih
        · rw [show (net.jumpSystem κ).rate (3 : Fin 4) (twoSpeciesCount m (k + 1))
              = net.stochasticMassActionRate κ (twoSpeciesCount m (k + 1)) 3 from rfl,
            rate_deathB]
          exact mul_pos (κ.positive 3) (by exact_mod_cast Nat.succ_pos k)
        · rw [next_deathB]
  -- grow the population of `A` from the origin
  have growA : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (twoSpeciesCount 0 k)
      (twoSpeciesCount m k) := by
    intro m k
    induction m with
    | zero => exact Relation.ReflTransGen.refl
    | succ m ih =>
        refine Relation.ReflTransGen.trans ih
          (Relation.ReflTransGen.single ⟨(0 : Fin 4), ?_, ?_⟩)
        · rw [show (net.jumpSystem κ).rate (0 : Fin 4) (twoSpeciesCount m k)
              = net.stochasticMassActionRate κ (twoSpeciesCount m k) 0 from rfl, rate_birthA]
          exact κ.positive 0
        · rw [next_birthA]
  -- grow the population of `B` from the origin
  have growB : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (twoSpeciesCount m 0)
      (twoSpeciesCount m k) := by
    intro m k
    induction k with
    | zero => exact Relation.ReflTransGen.refl
    | succ k ih =>
        refine Relation.ReflTransGen.trans ih
          (Relation.ReflTransGen.single ⟨(2 : Fin 4), ?_, ?_⟩)
        · rw [show (net.jumpSystem κ).rate (2 : Fin 4) (twoSpeciesCount m k)
              = net.stochasticMassActionRate κ (twoSpeciesCount m k) 2 from rfl, rate_birthB]
          exact κ.positive 2
        · rw [next_birthB]
  have toZero : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (twoSpeciesCount m k)
      (twoSpeciesCount 0 0) :=
    fun m k => Relation.ReflTransGen.trans (killA m k) (killB 0 k)
  have fromZero : ∀ (m k : ℕ), (net.jumpSystem κ).ReachPos (twoSpeciesCount 0 0)
      (twoSpeciesCount m k) :=
    fun m k => Relation.ReflTransGen.trans (growA m 0) (growB m k)
  rw [show a = twoSpeciesCount (a 0) (a 1) from by
    funext s; fin_cases s <;> simp [twoSpeciesCount]]
  rw [show b = twoSpeciesCount (b 0) (b 1) from by
    funext s; fin_cases s <;> simp [twoSpeciesCount]]
  exact Relation.ReflTransGen.trans (toZero (a 0) (a 1)) (fromZero (b 0) (b 1))

/-! ### The multiplicative Foster--Lyapunov drift -/

/-- The **inward drift constant** of the two-species instance: the smaller of the two death
rate constants.  It is strictly positive. -/
def twoSpeciesEpsilon (κ : net.RateConstants) : ℝ := min (κ.k 1) (κ.k 3)

/-- The **constant term** of the drift of the two-species instance: the total birth rate.  It is
nonnegative. -/
def twoSpeciesK (κ : net.RateConstants) : ℝ := κ.k 0 + κ.k 2

/-- The inward drift constant is strictly positive. -/
theorem twoSpeciesEpsilon_pos (κ : net.RateConstants) : 0 < twoSpeciesEpsilon κ := by
  show 0 < min (κ.k 1) (κ.k 3)
  exact lt_min (κ.positive 1) (κ.positive 3)

/-- The constant term of the drift is nonnegative. -/
theorem twoSpeciesK_nonneg (κ : net.RateConstants) : 0 ≤ twoSpeciesK κ := by
  show 0 ≤ κ.k 0 + κ.k 2
  exact add_nonneg (κ.positive 0).le (κ.positive 2).le

/-- The total count is the sum of the two species counts. -/
theorem twoSpecies_observable (n : Fin 2 → ℕ) :
    linearObservable twoSpeciesWeight n = (n 0 : ℝ) + (n 1 : ℝ) := by
  simp only [linearObservable, Fin.sum_univ_two, twoSpeciesWeight]
  ring

/-- **The drift of the total count.**  The observable `V n = n(A) + n(B)` has the exact drift

`Q V (n) = (κ₀ + κ₂) − (κ₁ · n(A) + κ₃ · n(B))`,

the two birth channels contributing the count-independent constants `κ₀` and `κ₂` and the two
death channels contributing `−κ₁ n(A)` and `−κ₃ n(B)`. -/
theorem twoSpecies_drift_eq (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.observableGenerator κ (linearObservable twoSpeciesWeight) n
      = twoSpeciesK κ - κ.k 1 * (n 0 : ℝ) - κ.k 3 * (n 1 : ℝ) := by
  have hinner0 : ∑ s : Fin 2, twoSpeciesWeight s * net.reactionVector 0 s = 1 := by
    simp [twoSpeciesWeight, net, Network.reactionVector_apply]
  have hinner1 : ∑ s : Fin 2, twoSpeciesWeight s * net.reactionVector 1 s = -1 := by
    simp [twoSpeciesWeight, net, Network.reactionVector_apply]
  have hinner2 : ∑ s : Fin 2, twoSpeciesWeight s * net.reactionVector 2 s = 1 := by
    simp [twoSpeciesWeight, net, Network.reactionVector_apply]
  have hinner3 : ∑ s : Fin 2, twoSpeciesWeight s * net.reactionVector 3 s = -1 := by
    simp [twoSpeciesWeight, net, Network.reactionVector_apply]
  have hr0 : net.stochasticMassActionRate κ n 0 = κ.k 0 := by
    unfold Network.stochasticMassActionRate
    simp [net]
  have hr1 : net.stochasticMassActionRate κ n 1 = κ.k 1 * (n 0 : ℝ) := by
    unfold Network.stochasticMassActionRate
    simp [net]
  have hr2 : net.stochasticMassActionRate κ n 2 = κ.k 2 := by
    unfold Network.stochasticMassActionRate
    simp [net]
  have hr3 : net.stochasticMassActionRate κ n 3 = κ.k 3 * (n 1 : ℝ) := by
    unfold Network.stochasticMassActionRate
    simp [net]
  rw [Network.observableGenerator_linear]
  simp only [Fin.sum_univ_four, hr0, hr1, hr2, hr3, hinner0, hinner1, hinner2, hinner3,
    twoSpeciesK]
  ring

/-- **The multiplicative Foster–Lyapunov drift of the total count.**

`Q V (n) ≤ −ε · V (n) + K`   with   `ε = min κ₁ κ₃ > 0`   and   `K = κ₀ + κ₂ ≥ 0`,

where `V n = n(A) + n(B)`.  This is the drift condition from which the ACK conclusion is
deduced. -/
theorem twoSpecies_drift (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    net.observableGenerator κ (linearObservable twoSpeciesWeight) n
      ≤ -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight n + twoSpeciesK κ := by
  have hε : twoSpeciesEpsilon κ = min (κ.k 1) (κ.k 3) := rfl
  have hK : twoSpeciesK κ = κ.k 0 + κ.k 2 := rfl
  have hV : linearObservable twoSpeciesWeight n = (n 0 : ℝ) + (n 1 : ℝ) :=
    twoSpecies_observable n
  have h1 : min (κ.k 1) (κ.k 3) * (n 0 : ℝ) ≤ κ.k 1 * (n 0 : ℝ) :=
    mul_le_mul_of_nonneg_right (min_le_left _ _) (Nat.cast_nonneg _)
  have h2 : min (κ.k 1) (κ.k 3) * (n 1 : ℝ) ≤ κ.k 3 * (n 1 : ℝ) :=
    mul_le_mul_of_nonneg_right (min_le_right _ _) (Nat.cast_nonneg _)
  have h3 : min (κ.k 1) (κ.k 3) * ((n 0 : ℝ) + (n 1 : ℝ))
      ≤ κ.k 1 * (n 0 : ℝ) + κ.k 3 * (n 1 : ℝ) := by
    have hsum : min (κ.k 1) (κ.k 3) * ((n 0 : ℝ) + (n 1 : ℝ))
        = min (κ.k 1) (κ.k 3) * (n 0 : ℝ) + min (κ.k 1) (κ.k 3) * (n 1 : ℝ) := by ring
    rw [hsum]
    exact add_le_add h1 h2
  calc net.observableGenerator κ (linearObservable twoSpeciesWeight) n
      = twoSpeciesK κ - κ.k 1 * (n 0 : ℝ) - κ.k 3 * (n 1 : ℝ) := twoSpecies_drift_eq κ n
    _ = twoSpeciesK κ - (κ.k 1 * (n 0 : ℝ) + κ.k 3 * (n 1 : ℝ)) := by ring
    _ ≤ twoSpeciesK κ - min (κ.k 1) (κ.k 3) * ((n 0 : ℝ) + (n 1 : ℝ)) := sub_le_sub_left h3 _
    _ = twoSpeciesK κ - min (κ.k 1) (κ.k 3) * (linearObservable twoSpeciesWeight n) := by
        rw [hV]
    _ = -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight n + twoSpeciesK κ := by
        rw [hε, hK]
        ring

/-- The count-lattice tier structure of the instance (the weight `w = (1, 1)`) has the total-count
observable as its tier Lyapunov function. -/
theorem twoSpecies_tierLyapunov (κ : net.RateConstants) (n : Fin 2 → ℕ) :
    Network.CountLyapunov net κ countTier n = linearObservable twoSpeciesWeight n := rfl

/-! ### The Anderson--Cappelletti--Kim--Nguyen conclusion -/

/-- **Non-explosion of the two-species instance.**  The stochastic mass-action chain of
`0 → A`, `A → 0`, `0 → B`, `B → 0` makes only finitely many jumps in a finite time interval:
its minimal transition function is stochastic. -/
theorem twoSpecies_nonExplosion (κ : net.RateConstants) {t : ℝ} (ht : 0 ≤ t)
    (n : Fin 2 → ℕ) :
    HasSum (fun m => net.transition κ t n m) 1 := by
  classical
  have hV0 : ∀ m : Fin 2 → ℕ, 0 ≤ linearObservable twoSpeciesWeight m :=
    fun m => linearObservable_nonneg_of_positive (w := twoSpeciesWeight) weight_pos m
  have hfinV : ∀ R : ℝ, {m : Fin 2 → ℕ | linearObservable twoSpeciesWeight m ≤ R}.Finite :=
    fun R => finite_linearObservable_le twoSpeciesWeight weight_pos R
  refine (net.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable twoSpeciesWeight)
    hV0 hfinV (le_refl 0) (twoSpeciesK_nonneg κ) (fun m => ?_) ht n
  have hsym : (net.jumpSystem κ).drift (linearObservable twoSpeciesWeight) m
      = net.observableGenerator κ (linearObservable twoSpeciesWeight) m :=
    (Network.observableGenerator_eq_jumpSystem_drift net κ
      (linearObservable twoSpeciesWeight) m).symm
  rw [hsym]
  have h := twoSpecies_drift κ m
  have hεV : 0 ≤ twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m :=
    mul_nonneg (twoSpeciesEpsilon_pos κ).le (hV0 m)
  have hneg : -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m ≤ 0 := by
    simpa [neg_mul] using neg_le_neg hεV
  calc net.observableGenerator κ (linearObservable twoSpeciesWeight) m
      ≤ -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m + twoSpeciesK κ := h
    _ ≤ 0 * linearObservable twoSpeciesWeight m + twoSpeciesK κ := by
        simpa using add_le_add_right hneg (twoSpeciesK κ)

/-- **Positive recurrence of the two-species instance.**  The stochastic mass-action chain of
`0 → A`, `A → 0`, `0 → B`, `B → 0` is non-explosive and positively recurrent: it has a
stationary probability `π` which charges **every** count (`0 < π b`), and the probability of
being at the starting count converges to the strictly positive limit `π a`. -/
theorem twoSpecies_positiveRecurrence (κ : net.RateConstants) :
    ∃ π : (Fin 2 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ b, 0 < π b) ∧
      (∀ a : Fin 2 → ℕ, Tendsto (fun t => net.transition κ t a a) atTop (𝓝 (π a))) := by
  classical
  have hV0 : ∀ n : Fin 2 → ℕ, 0 ≤ linearObservable twoSpeciesWeight n :=
    fun n => linearObservable_nonneg_of_positive (w := twoSpeciesWeight) weight_pos n
  have hfinV : ∀ R : ℝ, {n : Fin 2 → ℕ | linearObservable twoSpeciesWeight n ≤ R}.Finite :=
    fun R => finite_linearObservable_le twoSpeciesWeight weight_pos R
  have hstoch : ∀ t, 0 ≤ t → ∀ c : Fin 2 → ℕ,
      HasSum (fun b => (net.jumpSystem κ).Pmin t c b) 1 := by
    intro t ht c
    refine (net.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable twoSpeciesWeight)
      hV0 hfinV (le_refl 0) (twoSpeciesK_nonneg κ) (fun m => ?_) ht c
    have hsym : (net.jumpSystem κ).drift (linearObservable twoSpeciesWeight) m
        = net.observableGenerator κ (linearObservable twoSpeciesWeight) m :=
      (Network.observableGenerator_eq_jumpSystem_drift net κ
        (linearObservable twoSpeciesWeight) m).symm
    rw [hsym]
    have h := twoSpecies_drift κ m
    have hεV : 0 ≤ twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m :=
      mul_nonneg (twoSpeciesEpsilon_pos κ).le (hV0 m)
    have hneg : -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m ≤ 0 := by
      simpa [neg_mul] using neg_le_neg hεV
    calc net.observableGenerator κ (linearObservable twoSpeciesWeight) m
        ≤ -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m + twoSpeciesK κ := h
      _ ≤ 0 * linearObservable twoSpeciesWeight m + twoSpeciesK κ := by
          simpa using add_le_add_right hneg (twoSpeciesK κ)
  have hfinf : ∀ R : ℝ, {x : Fin 2 → ℕ |
      twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight x ≤ R}.Finite := by
    intro R
    refine (finite_linearObservable_le (fun _ => twoSpeciesEpsilon κ)
      (fun s => twoSpeciesEpsilon_pos κ) R).subset fun x hx => ?_
    simp only [Set.mem_ofPred_eq] at hx ⊢
    have hscale : linearObservable (fun _ => twoSpeciesEpsilon κ) x
        = twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight x := by
      have h1 : linearObservable (fun _ => twoSpeciesEpsilon κ) x
          = twoSpeciesEpsilon κ * (x 0 : ℝ) + twoSpeciesEpsilon κ * (x 1 : ℝ) := by
        simp [linearObservable, Fin.sum_univ_two]
      have h2 : linearObservable twoSpeciesWeight x = (x 0 : ℝ) + (x 1 : ℝ) :=
        twoSpecies_observable x
      rw [h1, h2]
      ring
    rw [hscale]
    exact hx
  have hdrift : ∀ x : Fin 2 → ℕ,
      (net.jumpSystem κ).drift (linearObservable twoSpeciesWeight) x
        ≤ -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight x + twoSpeciesK κ := by
    intro x
    have hsym : (net.jumpSystem κ).drift (linearObservable twoSpeciesWeight) x
        = net.observableGenerator κ (linearObservable twoSpeciesWeight) x :=
      (Network.observableGenerator_eq_jumpSystem_drift net κ
        (linearObservable twoSpeciesWeight) x).symm
    rw [hsym]
    exact twoSpecies_drift κ x
  obtain ⟨π, hπ0, hπ1, hπinv, hπE, hπpos, hconv, -⟩ :=
    (net.jumpSystem κ).foster_lyapunov_ergodic (linearObservable twoSpeciesWeight)
      (fun x => twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight x)
      hV0 (fun x => mul_nonneg (twoSpeciesEpsilon_pos κ).le (hV0 x)) hfinf
      (twoSpeciesK_nonneg κ)
      (fun x => by simpa [neg_mul] using hdrift x)
      hstoch (E := Set.univ) (fun _ _ _ _ => Set.mem_univ _)
      (fun _ _ _ _ => twoSpecies_reachPos κ _ _) (Set.mem_univ (fun _ => 0))
  refine ⟨π, hπ0, hπ1, hπinv, fun b => hπpos b (Set.mem_univ b), ?_⟩
  intro a
  have hlim : Tendsto (fun t => (net.jumpSystem κ).Pmin t a a) atTop (𝓝 (π a)) :=
    (net.jumpSystem κ).tendsto_Pmin_of_invariant
      (fun _ _ _ _ => Set.mem_univ _) (fun _ _ _ _ => twoSpecies_reachPos κ _ _)
      (fun t ht c _ => hstoch t ht c) hπ0 (fun b h => (h (Set.mem_univ b)).elim) hπ1 hπinv
      (Set.mem_univ a) a
  simpa only [Network.transition] using hlim

/-- **Geometric ergodicity of the two-species instance.**  The chain satisfies the Meyn--Tweedie
`V`-uniform ergodicity estimate with the total-count observable `V n = n(A) + n(B)`. -/
theorem twoSpecies_geometricErgodic (κ : net.RateConstants) :
    ∃ π : (Fin 2 → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (net.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(net.jumpSystem κ).Pmin t a b - π b| *
            (1 + β * linearObservable twoSpeciesWeight b) ≤
          C₀ * (1 + linearObservable twoSpeciesWeight a) * ρ ^ ⌊t⌋₊ := by
  classical
  have hV0 : ∀ n : Fin 2 → ℕ, 0 ≤ linearObservable twoSpeciesWeight n :=
    fun n => linearObservable_nonneg_of_positive (w := twoSpeciesWeight) weight_pos n
  have hfinV : ∀ R : ℝ, {n : Fin 2 → ℕ | linearObservable twoSpeciesWeight n ≤ R}.Finite :=
    fun R => finite_linearObservable_le twoSpeciesWeight weight_pos R
  have hstoch : ∀ t, 0 ≤ t → ∀ c : Fin 2 → ℕ,
      HasSum (fun b => (net.jumpSystem κ).Pmin t c b) 1 := by
    intro t ht c
    refine (net.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (linearObservable twoSpeciesWeight)
      hV0 hfinV (le_refl 0) (twoSpeciesK_nonneg κ) (fun m => ?_) ht c
    have hsym : (net.jumpSystem κ).drift (linearObservable twoSpeciesWeight) m
        = net.observableGenerator κ (linearObservable twoSpeciesWeight) m :=
      (Network.observableGenerator_eq_jumpSystem_drift net κ
        (linearObservable twoSpeciesWeight) m).symm
    rw [hsym]
    have h := twoSpecies_drift κ m
    have hεV : 0 ≤ twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m :=
      mul_nonneg (twoSpeciesEpsilon_pos κ).le (hV0 m)
    have hneg : -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m ≤ 0 := by
      simpa [neg_mul] using neg_le_neg hεV
    calc net.observableGenerator κ (linearObservable twoSpeciesWeight) m
        ≤ -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight m + twoSpeciesK κ := h
      _ ≤ 0 * linearObservable twoSpeciesWeight m + twoSpeciesK κ := by
          simpa using add_le_add_right hneg (twoSpeciesK κ)
  have hdrift : ∀ x : Fin 2 → ℕ,
      (net.jumpSystem κ).drift (linearObservable twoSpeciesWeight) x
        ≤ -twoSpeciesEpsilon κ * linearObservable twoSpeciesWeight x + twoSpeciesK κ := by
    intro x
    have hsym : (net.jumpSystem κ).drift (linearObservable twoSpeciesWeight) x
        = net.observableGenerator κ (linearObservable twoSpeciesWeight) x :=
      (Network.observableGenerator_eq_jumpSystem_drift net κ
        (linearObservable twoSpeciesWeight) x).symm
    rw [hsym]
    exact twoSpecies_drift κ x
  exact (net.jumpSystem κ).geometric_ergodic (linearObservable twoSpeciesWeight) hV0 hfinV
    (twoSpeciesEpsilon_pos κ) (twoSpeciesK_nonneg κ) hdrift hstoch
    (fun a b => twoSpecies_reachPos κ a b)

#print axioms twoSpecies_reachPos
#print axioms twoSpecies_drift_eq
#print axioms twoSpecies_drift
#print axioms twoSpecies_nonExplosion
#print axioms twoSpecies_positiveRecurrence
#print axioms twoSpecies_geometricErgodic

end EndotacticCounterexample
end Examples
end CRNT
