import CRNT.Deficiency.DOACapacityConstruction
import CRNT.Deficiency.DOAForward
import CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness
import CRNT.Multistationarity.CapacityCharacterization
import CRNT.Multistationarity.MultiShelfConverse
import CRNT.Multistationarity.MultistationarityRegion

/-!
# The analytic core of the deficiency-one capacity construction

This module supplies the **analytic core** of the forward direction of the Deficiency One
Algorithm: the part of Feinberg's construction which turns a *balance* into a *steady state*.

## Feinberg's construction

Feinberg's deficiency-one theorem (G. Feinberg, *Chemical reaction network structure and the
stability of complex isothermal reactors — I*, Chem. Eng. Sci. **30** (1979), 222–236) says that a
deficiency-one network with the right shelf structure is *multistationary* for a suitable choice
of rate constants. The construction has three steps:

1. a **cut-space vector** `w` in the stoichiometric subspace, whose pairing `⟨y_r, w⟩` with the
   sources of the reactions has a fixed sign on the "upper" part of the network and the opposite
   sign on the "lower" part;
2. the **pair of states** `x ≡ 1` and `y = 1 + t·w` for `t > 0` small enough that `y` is positive
   (the *positional* half of the construction, carried out in
   `CRNT.Deficiency.DOACapacityConstruction` as `exists_compatible_pair_sameSign_logRatio`);
3. the **rate constants** `κ` for which *both* `x` and `y` are mass-action steady states.

Step 3 is the analytic core, and it is what this module formalises.

## The two balances

For a reaction `r` with source `y_r` and target `y'_r`, the mass-action balance at the all-ones
state `x ≡ 1` reads

```
∑_r κ_r ( y'_r − y_r ) = 0                                   (the lower balance)
```

because the source monomial at `1` is `1`; and at the exponential state `y = e^μ` it reads

```
∑_r κ_r e^{⟨y_r, μ⟩} ( y'_r − y_r ) = 0                      (the upper balance)
```

because the source monomial at `e^μ` is `e^{⟨y_r, μ⟩}`. These are exactly the two balances of
the repository's shelf machinery: `ShelfLowerBalanced` and `ShelfUpperBalanced`
(`CRNT.Multistationarity.MultiShelfConverse`), and the *shelf balance criterion*
`shelfLowerBalanced_implies_shelfUpperBalanced` — on a shelf whose sources pair equally with
`μ`, the upper balance is a consequence of the lower one.

## What this module proves

* **The linearised upper balance** (`linearised_upper_balance`, `additiveUpperBalance`,
  `additiveUpperBalance_derivAt_zero`, `upperBalance_derivAt_zero`,
  `massActionJacobianCLM_one`): the *first-order expansion* of the balance map at the all-ones
  state in the direction `w` is the `⟨y_r, w⟩`-weighted reaction vector
  `∑_r κ_r ( ⟨y_r, w⟩ y'_r − ⟨y_r, w⟩ y_r )`. This is the directional-derivative computation
  which underlies the choice of `κ`: the rate constants must annihilate the *linearised*
  reaction vectors of the two states.  For the *additive* candidate pair `1`, `1 + t·w` of
  `exists_compatible_pair_sameSign_logRatio` the exact condition for the pair to be a pair of
  steady states is the vanishing of `additiveUpperBalance` at `t`; its first-order term at
  `t = 0` is the linearised reaction vector.

* **The analytic core** (`shelfBalances_implies_steadyStates`): the two balances make the two
  Feinberg states `x = 1` and `y = e^μ` *mass-action steady states*.

* **Feinberg's construction, in the shelf form** (`shelfFluxes_construction`,
  `shelfFluxes_construction_capacity`, `shelfFluxes_explicit_construction`): a shelf
  decomposition whose shelves are pairing-constant at `μ` and whose shelf fluxes balance at the
  lower state produces *explicit* rate constants — the global flux — for which `1` and `e^μ` are
  both steady states, and, when the two states are compatible, the capacity for multiple steady
  states.

* **The two Feinberg states** (`exp_ne_one_of_ne_zero`, `exp_pair_compatible`,
  `exp_pair_logRatio`): the pair `1`, `e^μ` is distinct, compatible and has log-ratio `μ` — the
  converse of `CRNT.Network.signCompatible_logRatio`.

* **An end-to-end instance** (`DOAExample.analytic_capacity`): for the worked deficiency-one
  network `0 → A`, `0 → B`, `A + B → 0` of `CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness`,
  the rate constants `κ = (1, 1, 1)` make the two states `x = (1, 1)` and `y = (e, e^{-1})` mass-action
  steady states; the network therefore has the capacity for multiple positive steady states, by
  the *analytic* route and not through the feasibility test.

## The two normalisations of the construction

The construction is carried out here in the **log-ratio normalisation** of the Deficiency One
Algorithm, in which the second state is `y = x e^μ`.  With the normalisation `x = 1` of
Feinberg's construction this gives the pair `1`, `e^μ`; the *positional* module
`CRNT.Deficiency.DOACapacityConstruction` uses instead the **additive normalisation**
`x = 1`, `y = 1 + t·w`, in which the *log-ratio* of the pair is `ln (1 + t·w)`, not `μ`.  The two
normalisations describe the same *pairing* of the two states, but they are different points of
the class, and the passage between them is a nonlinear change of variables which is not
formalised here.  What is formalised is:

* the *first-order* condition for the additive pair to be a pair of steady states
  (`additiveUpperBalance_derivAt_zero`), and
* the *exact* condition for the exponential pair to be a pair of steady states
  (`shelfBalances_implies_steadyStates`).

## The entry steps

The forward direction of the Deficiency One Algorithm enters through

* `exists_signCompatible_of_hasMultistationarityCapacity` (`CRNT.Deficiency.DOAForward`): the
  log-ratio `μ = ln y − ln x` of two witnessing steady states is nonzero and sign-compatible with
  the stoichiometric subspace;
* `exists_compatible_pair_sameSign_logRatio` (`CRNT.Deficiency.DOACapacityConstruction`): the
  *positional* pair `x ≡ 1`, `y = 1 + t·w` for a suitable `w ∈ S(N)`.

This module continues from those two steps.

## What remains open

The **general** construction — the choice of the cut-space vector `w`, of the shelf partition and
of the rate constants `κ` for an *arbitrary* deficiency-one network — is Feinberg's structural
analysis and is **not** carried out here.  What this module isolates is the *analytic* part of
that analysis, which is independent of the structural part: once the two balances are met, the
two states are steady states, and the linearisation of the balance map at the lower state is
the `⟨y_r, w⟩`-weighted reaction vector.

The repository's `CRNT.Network.hasMultistationarityCapacity_iff_flux_sign` already turns a
*flux certificate* `(α, μ, σ)` into the capacity, with the states `x_s = σ_s / (e^{μ_s} − 1)` and
`y = x e^μ`. This module gives the complementary **normalised** statement: with the states
`x = 1` and `y = e^μ` (Feinberg's normalisation), the two balances *are* the steady-state
conditions, and the compatibility of the two states is the membership
`e^μ − 1 ∈ S(N)`.

Depends on: `CRNT.Deficiency.DOACapacityConstruction`, `CRNT.Deficiency.DOAForward`,
`CRNT.Deficiency.DeficiencyOneAlgorithmCorrectness`,
`CRNT.Multistationarity.CapacityCharacterization`,
`CRNT.Multistationarity.MultiShelfConverse`,
`CRNT.Multistationarity.MultistationarityRegion`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

set_option maxHeartbeats 800000

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## The linearised upper balance -/

/-- **The gradient of the source monomial at the all-ones point.**  At the point `x ≡ 1` the
gradient of the monomial `∏ s, x_s ^ y_s` is the vector of the coefficients of `y` themselves:
`∂_j (x ^ y) |_{x = 1} = y_j`. -/
theorem massActionMonomialGrad_one (y : Complex S) (j : S) :
    massActionMonomialGrad y (fun _ => 1) j = (y j : ℝ) := by
  simp [massActionMonomialGrad]

/-- **The derivative of the source monomial at the all-ones point.**  The directional derivative
of the monomial `x ^ y` at `x ≡ 1` in the direction `w` is the pairing `⟨y, w⟩` — the
first-order term of the expansion `x ^ y = 1 + t ⟨y, w⟩ + O(t²)` along `x = 1 + t·w`. -/
theorem massActionMonomial_hasDerivAt_one (y : Complex S) (w : Concentration S) :
    HasDerivAt (fun t : ℝ => y.massActionMonomial (fun s => 1 + t * w s)) (complexPairing y w) 0 := by
  have h := massActionMonomial_hasDerivAt_along y (fun _ => (1 : ℝ)) w 0
  have hfun : (fun t : ℝ => y.massActionMonomial (fun s => 1 + t * w s))
      = (fun t : ℝ => y.massActionMonomial ((fun _ => (1 : ℝ)) + t • w)) := by
    funext t
    apply congrArg (fun z : Concentration S => y.massActionMonomial z)
    funext s
    simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have h2 := h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq hfun)
  have hderiv : (∑ j, massActionMonomialGrad y ((fun _ => (1 : ℝ)) + (0 : ℝ) • w) j * w j)
      = complexPairing y w := by
    simp only [zero_smul, add_zero, massActionMonomialGrad_one]
    rfl
  exact h2.congr_deriv hderiv

omit [DecidableEq S] in
/-- **The pairing of a complex with a scaled direction.**  `⟨y, t·w⟩ = t ⟨y, w⟩`. -/
theorem complexPairing_smul (y : Complex S) (t : ℝ) (w : Concentration S) :
    complexPairing y (t • w) = t * complexPairing y w := by
  unfold complexPairing
  simp only [Pi.smul_apply, smul_eq_mul]
  calc ∑ s, (y s : ℝ) * (t * w s) = ∑ s, t * ((y s : ℝ) * w s) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        ring
    _ = t * ∑ s, (y s : ℝ) * w s := by rw [Finset.mul_sum]

/-- **The linearised upper balance.**  The derivative, at the all-ones state, of the mass-action
field along the direction `w` is the `⟨y_r, w⟩`-weighted reaction vector

```
∑_r κ_r ( ⟨y_r, w⟩ y'_r − ⟨y_r, w⟩ y_r ) ,
```

the *linearisation* of the balance map at the lower state.  This is the quantity which the rate
constants of Feinberg's construction have to annihilate, and the first-order term of the
expansion of the upper balance `∑_r κ_r e^{⟨y_r, w⟩} (y'_r − y_r)` around `w = 0`. -/
theorem linearised_upper_balance (N : Network S) (κ : N.RateConstants) (w : Concentration S)
    (s : S) :
    deriv (fun t : ℝ => N.massActionVectorField κ (fun u => 1 + t * w u) s) 0
      = ∑ r, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s := by
  have hfun : (fun t : ℝ => N.massActionVectorField κ (fun u => 1 + t * w u) s)
      = (fun t : ℝ => ∑ r, κ.k r * (N.reaction r).source.massActionMonomial
          (fun u => 1 + t * w u) * N.reactionVector r s) := by
    funext t
    rw [massActionVectorField_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    rfl
  rw [hfun]
  have hsum : HasDerivAt (fun t : ℝ => ∑ r, κ.k r * (N.reaction r).source.massActionMonomial
      (fun u => 1 + t * w u) * N.reactionVector r s)
      (∑ r, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s) 0 := by
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset N.R)) ?_
    intro r _
    have hmono := massActionMonomial_hasDerivAt_one (N.reaction r).source w
    have h1 : HasDerivAt (fun t : ℝ => κ.k r * (N.reaction r).source.massActionMonomial
        (fun u => 1 + t * w u)) (κ.k r * complexPairing (N.reaction r).source w) 0 :=
      hmono.const_mul _
    exact h1.mul_const (N.reactionVector r s)
  rw [hsum.deriv]

/-- **The derivative of the upper-balance function at the origin.**  The first-order expansion of
the upper balance `w ↦ ∑_r κ_r e^{⟨y_r, w⟩} (y'_r − y_r)` at `w = 0` is the linearised
reaction vector: the same quantity as `linearised_upper_balance`. -/
theorem upperBalance_derivAt_zero (N : Network S) (κ : N.RateConstants) (w : Concentration S)
    (s : S) :
    deriv (fun t : ℝ => ∑ r, κ.k r * Real.exp (complexPairing (N.reaction r).source (t • w)) *
      N.reactionVector r s) 0
      = ∑ r, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s := by
  have hsum : HasDerivAt (fun t : ℝ => ∑ r, κ.k r * Real.exp (complexPairing (N.reaction r).source
      (t • w)) * N.reactionVector r s)
      (∑ r, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s) 0 := by
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset N.R)) ?_
    intro r _
    have hexp : (fun t : ℝ => Real.exp (complexPairing (N.reaction r).source (t • w)))
        = (fun t : ℝ => Real.exp (t * complexPairing (N.reaction r).source w)) := by
      funext t
      rw [complexPairing_smul]
    have hexp'' : HasDerivAt (fun t : ℝ => Real.exp (complexPairing (N.reaction r).source (t • w)))
        (complexPairing (N.reaction r).source w) 0 := by
      rw [hexp]
      have hlin : HasDerivAt (fun t : ℝ => t * complexPairing (N.reaction r).source w)
          (complexPairing (N.reaction r).source w) 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).mul_const (complexPairing (N.reaction r).source w)
      have hexp' : HasDerivAt (fun t : ℝ => Real.exp (t * complexPairing (N.reaction r).source w))
          (Real.exp 0 * complexPairing (N.reaction r).source w) 0 := by
        simpa using hlin.exp
      have hexp''' : HasDerivAt (fun t : ℝ => Real.exp (t * complexPairing (N.reaction r).source w))
          (complexPairing (N.reaction r).source w) 0 := by
        simpa using hexp'
      exact hexp'''
    exact (hexp''.const_mul (κ.k r)).mul_const (N.reactionVector r s)
  rw [hsum.deriv]

/-- **The mass-action Jacobian at the all-ones point.**  The Fréchet derivative of the
mass-action field at the lower state `x ≡ 1`, applied to the direction `w`, is the linearised
reaction vector — the `HasFDerivAt` form of `linearised_upper_balance`.  (At a *general* steady
state `x` the linearisation is the mass-action Jacobian `N.massActionJacobianCLM κ x`, by
`CRNT.Network.massActionVectorField_hasFDerivAt`.) -/
theorem massActionJacobianCLM_one (N : Network S) (κ : N.RateConstants) (w : Concentration S) :
    N.massActionJacobianCLM κ (fun _ => 1) w
      = fun s => ∑ r, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s := by
  rw [N.massActionJacobianCLM_apply]
  funext s
  simp only [Matrix.mulVec_apply_eq_sum]
  have hM : ∀ j : S, (N.massActionJacobian κ (fun _ => 1)) s j
      = ∑ r : N.R, κ.k r * massActionMonomialGrad (N.reaction r).source (fun _ => 1) j *
          N.reactionVector r s := by
    intro j
    rfl
  have hexp : (∑ j : S, (N.massActionJacobian κ (fun _ => 1)) s j * w j)
      = ∑ r : N.R, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s := by
    calc (∑ j : S, (N.massActionJacobian κ (fun _ => 1)) s j * w j)
        = ∑ j : S, (∑ r : N.R, κ.k r * massActionMonomialGrad (N.reaction r).source
            (fun _ => 1) j * N.reactionVector r s) * w j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [hM j]
      _ = ∑ j : S, ∑ r : N.R, (κ.k r * massActionMonomialGrad (N.reaction r).source
          (fun _ => 1) j * N.reactionVector r s) * w j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [Finset.sum_mul]
      _ = ∑ r : N.R, ∑ j : S, (κ.k r * massActionMonomialGrad (N.reaction r).source
          (fun _ => 1) j * N.reactionVector r s) * w j := by
            exact Finset.sum_comm (β := ℝ) (γ := S) (α := N.R)
              (s := (Finset.univ : Finset S)) (t := (Finset.univ : Finset N.R))
              (f := fun j r => (κ.k r * massActionMonomialGrad (N.reaction r).source
                (fun _ => 1) j * N.reactionVector r s) * w j)
      _ = ∑ r : N.R, (κ.k r * N.reactionVector r s) *
          (∑ j : S, massActionMonomialGrad (N.reaction r).source (fun _ => 1) j * w j) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            calc (∑ j : S, (κ.k r * massActionMonomialGrad (N.reaction r).source
                  (fun _ => 1) j * N.reactionVector r s) * w j)
                = ∑ j : S, (κ.k r * N.reactionVector r s) *
                    (massActionMonomialGrad (N.reaction r).source (fun _ => 1) j * w j) := by
                    refine Finset.sum_congr rfl fun j _ => ?_
                    ring
              _ = (κ.k r * N.reactionVector r s) *
                  (∑ j : S, massActionMonomialGrad (N.reaction r).source (fun _ => 1) j * w j) := by
                    rw [← Finset.mul_sum]
      _ = ∑ r : N.R, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            have h1 : (∑ j : S, massActionMonomialGrad (N.reaction r).source (fun _ => 1) j * w j)
                = complexPairing (N.reaction r).source w := by
              simp only [massActionMonomialGrad_one]
              rfl
            rw [h1]
            ring
  rw [hexp]

/-- **The exact upper balance at the additive candidate pair.**  This is the mass-action field
along the curve `t ↦ 1 + t·w` — the pair `x = 1`, `y = 1 + t·w` of
`CRNT.Deficiency.DOACapacityConstruction.exists_compatible_pair_sameSign_logRatio`.  The two
states of that pair are simultaneously mass-action steady states exactly when this function
vanishes at `t` (together with its value at `t = 0`, the lower balance). -/
def additiveUpperBalance (N : Network S) (κ : N.RateConstants) (w : Concentration S) (t : ℝ)
    (s : S) : ℝ :=
  ∑ r, κ.k r * (N.reaction r).source.massActionMonomial (fun u => 1 + t * w u) *
    N.reactionVector r s

/-- **The first-order expansion of the upper balance at the additive candidate pair.**  The
derivative of the upper balance at `t = 0` is the linearised reaction vector: the condition that
the pair `1`, `1 + t·w` be a pair of steady states to *first order* is that the rate constants
annihilate the `⟨y_r, w⟩`-weighted reaction vectors. -/
theorem additiveUpperBalance_derivAt_zero (N : Network S) (κ : N.RateConstants)
    (w : Concentration S) (s : S) :
    deriv (fun t : ℝ => additiveUpperBalance N κ w t s) 0
      = ∑ r, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s := by
  unfold additiveUpperBalance
  have hsum : HasDerivAt (fun t : ℝ => ∑ r, κ.k r * (N.reaction r).source.massActionMonomial
      (fun u => 1 + t * w u) * N.reactionVector r s)
      (∑ r, κ.k r * complexPairing (N.reaction r).source w * N.reactionVector r s) 0 := by
    refine HasDerivAt.fun_sum (u := (Finset.univ : Finset N.R)) ?_
    intro r _
    have hmono := massActionMonomial_hasDerivAt_one (N.reaction r).source w
    have h1 : HasDerivAt (fun t : ℝ => κ.k r * (N.reaction r).source.massActionMonomial
        (fun u => 1 + t * w u)) (κ.k r * complexPairing (N.reaction r).source w) 0 :=
      hmono.const_mul _
    exact h1.mul_const (N.reactionVector r s)
  rw [hsum.deriv]

/-! ## The analytic core: the two balances make the two states steady -/
omit [DecidableEq S] in
/-- **The mass-action monomial at the all-ones point is `1`.** -/
theorem massActionMonomial_one (y : Complex S) : y.massActionMonomial (fun _ => 1) = 1 := by
  simp [Complex.massActionMonomial]

omit [DecidableEq S] in
/-- **The mass-action monomial at the exponential state `e^μ` is `e^{⟨y, μ⟩}`.**  This is the
reason why the *upper* balance of Feinberg's construction carries the exponential factor
`e^{⟨y_r, μ⟩}`. -/
theorem massActionMonomial_exp (y : Complex S) (μ : S → ℝ) :
    y.massActionMonomial (fun s => Real.exp (μ s)) = Real.exp (complexPairing y μ) := by
  have h := massActionMonomial_mul_exp y (fun _ => (1 : ℝ)) μ
  have h' : y.massActionMonomial (fun s => Real.exp (μ s))
      = y.massActionMonomial (fun _ => (1 : ℝ)) * Real.exp (complexPairing y μ) := by
    simpa only [one_mul] using h
  rw [h', massActionMonomial_one]
  simp

/-- **The two shelf balances make the two Feinberg states steady.**  This is the analytic core
of Feinberg's construction: if the rate constants satisfy the *lower* balance
`∑_r κ_r (y'_r − y_r) = 0` and the *upper* balance
`∑_r κ_r e^{⟨y_r, μ⟩} (y'_r − y_r) = 0`, then the all-ones state `x ≡ 1` and the exponential
state `y = e^μ` are both mass-action steady states.

The two balances are the shelf balances of `CRNT.Multistationarity.MultiShelfConverse`:
`ShelfLowerBalanced` and `ShelfUpperBalanced`, related by the shelf balance criterion
`shelfLowerBalanced_implies_shelfUpperBalanced`. -/
theorem shelfBalances_implies_steadyStates (N : Network S) (κ : N.RateConstants) (μ : S → ℝ)
    (hlow : ∀ s, ∑ r, κ.k r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, κ.k r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s = 0) :
    N.IsMassActionSteadyState κ (fun _ => 1) ∧
      N.IsMassActionSteadyState κ (fun s => Real.exp (μ s)) := by
  constructor
  · intro s
    rw [massActionVectorField_apply]
    calc ∑ r, N.massActionRate κ r (fun _ => 1) * N.reactionVector r s
        = ∑ r, κ.k r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [massActionRate, massActionMonomial_one, mul_one]
        _ = 0 := hlow s
  · intro s
    rw [massActionVectorField_apply]
    calc ∑ r, N.massActionRate κ r (fun s => Real.exp (μ s)) * N.reactionVector r s
        = ∑ r, κ.k r * Real.exp (complexPairing (N.reaction r).source μ) *
            N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [massActionRate, massActionMonomial_exp]
        _ = 0 := hupp s

/-- **The analytic construction yields the capacity.**  If the rate constants satisfy the two
balances and the two Feinberg states `1` and `e^μ` are stoichiometrically compatible — i.e.
`e^μ − 1 ∈ S(N)` — and `μ ≠ 0`, then the network has the capacity for multiple positive steady
states.

This is the normalised form of the repository's flux certificate
`CRNT.Network.hasMultistationarityCapacity_iff_flux_sign`: there the states are
`x_s = σ_s / (e^{μ_s} − 1)` and `y = x e^μ`; here the states are `x = 1` and `y = e^μ`, and the
compatibility of the two states is exactly the membership `e^μ − 1 ∈ S(N)`. -/
theorem analytic_construction_capacity (N : Network S) (κ : N.RateConstants) (μ : S → ℝ)
    (hμ0 : μ ≠ 0)
    (hcompat : (fun s => Real.exp (μ s) - 1) ∈ N.stoichSubspace)
    (hlow : ∀ s, ∑ r, κ.k r * N.reactionVector r s = 0)
    (hupp : ∀ s, ∑ r, κ.k r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s = 0) :
    N.HasMultistationarityCapacity := by
  refine (N.hasMultistationarityCapacity_iff_flux_sign).2
    ⟨κ.k, μ, fun s => Real.exp (μ s) - 1, ?_, hcompat, ?_, ?_, hlow, hupp⟩
  · intro r; exact κ.positive r
  · intro h
    apply hμ0
    funext s
    have h1 : Real.exp (μ s) = 1 := by
      have h2 := congrFun h s
      rw [Pi.zero_apply] at h2
      linarith
    have h1' : Real.exp (μ s) = Real.exp 0 := h1.trans (by rw [Real.exp_zero])
    exact Real.exp_injective h1'
  · intro s
    rw [sign_sub_eq_sign_logDiff (Real.exp_pos _) (by norm_num : (0 : ℝ) < 1)]
    simp

/-- **Feinberg's construction, in the shelf form.**  Let `d` be a shelf decomposition of the
network whose shelves are *pairing-constant* at `μ` — the sources of the reactions of each shelf
pair equally with `μ` — and whose shelf fluxes balance at the lower state.  Then the **global
flux** of the shelf decomposition is a strictly positive vector which satisfies *both* balances,
so it is a choice of *rate constants* (`DOAShelfFluxes.globalFlux_lower_balance`,
`DOAShelfFluxes.globalFlux_upper_balance`), and the two Feinberg states `x = 1` and `y = e^μ`
are both mass-action steady states. -/
theorem shelfFluxes_construction (N : Network S) (μ : S → ℝ) (d : DOAShelfFluxes N)
    (hconst : ∀ sh ∈ d.shelves, ∀ r ∈ sh, ∀ r' ∈ sh, sourcePairing N μ r = sourcePairing N μ r') :
    ∃ κ : N.RateConstants, κ.k = d.globalFlux ∧
      N.IsMassActionSteadyState κ (fun _ => 1) ∧
        N.IsMassActionSteadyState κ (fun s => Real.exp (μ s)) := by
  refine ⟨⟨d.globalFlux, d.globalFlux_pos⟩, rfl, ?_, ?_⟩
  · intro s
    rw [massActionVectorField_apply]
    calc ∑ r, N.massActionRate ⟨d.globalFlux, d.globalFlux_pos⟩ r (fun _ => 1) *
          N.reactionVector r s
        = ∑ r, d.globalFlux r * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [massActionRate, massActionMonomial_one, mul_one]
        _ = 0 := d.globalFlux_lower_balance s
  · intro s
    rw [massActionVectorField_apply]
    calc ∑ r, N.massActionRate ⟨d.globalFlux, d.globalFlux_pos⟩ r
          (fun s => Real.exp (μ s)) * N.reactionVector r s
        = ∑ r, d.globalFlux r * Real.exp (sourcePairing N μ r) * N.reactionVector r s := by
            refine Finset.sum_congr rfl fun r _ => ?_
            rw [massActionRate, massActionMonomial_exp]
            rfl
        _ = 0 := d.globalFlux_upper_balance μ hconst s

/-- **Feinberg's construction, in the shelf form, gives the capacity.**  If in addition the two
Feinberg states `1` and `e^μ` are stoichiometrically compatible — `e^μ − 1 ∈ S(N)` — and `μ` is
nonzero, the network has the capacity for multiple positive steady states. -/
theorem shelfFluxes_construction_capacity (N : Network S) (μ : S → ℝ) (d : DOAShelfFluxes N)
    (hμ0 : μ ≠ 0)
    (hcompat : (fun s => Real.exp (μ s) - 1) ∈ N.stoichSubspace)
    (hconst : ∀ sh ∈ d.shelves, ∀ r ∈ sh, ∀ r' ∈ sh, sourcePairing N μ r = sourcePairing N μ r') :
    N.HasMultistationarityCapacity :=
  analytic_construction_capacity N ⟨d.globalFlux, d.globalFlux_pos⟩ μ hμ0 hcompat
    (fun s => d.globalFlux_lower_balance s)
    (fun s => d.globalFlux_upper_balance μ hconst s)

/-- **Feinberg's construction: the explicit rate constants and the two states.**  This is the
general statement of the deficiency-one capacity construction: under the *shelf hypotheses* — a
shelf decomposition whose shelves are pairing-constant at `μ`, and a nonzero stoichiometric
vector `σ` with the sign pattern of `μ` — there are rate constants `κ` and two distinct positive
concentrations `x`, `y` in one compatibility class which are both mass-action steady states.

The flux certificate is the global flux of the shelf decomposition, and the rate constants are
the fluxes of the two states divided by the source monomials, as in
`CRNT.Network.hasMultistationarityCapacity_iff_flux_sign`.  (The nonvanishing of `μ` is
implied by `hσ0` and `hsign`: a zero log-ratio would force `σ = 0`.) -/
theorem shelfFluxes_explicit_construction (N : Network S) (μ : S → ℝ) (d : DOAShelfFluxes N)
    (σ : S → ℝ) (hσS : σ ∈ N.stoichSubspace) (hσ0 : σ ≠ 0)
    (hsign : ∀ s, SignType.sign (σ s) = SignType.sign (μ s))
    (hconst : ∀ sh ∈ d.shelves, ∀ r ∈ sh, ∀ r' ∈ sh, sourcePairing N μ r = sourcePairing N μ r') :
    ∃ (κ : N.RateConstants) (x y : Concentration S),
      x.Positive ∧ y.Positive ∧ x ≠ y ∧ N.StoichCompatible x y ∧
        N.IsMassActionSteadyState κ x ∧ N.IsMassActionSteadyState κ y := by
  have hcap : N.HasMultistationarityCapacity :=
    (N.hasMultistationarityCapacity_iff_flux_sign).2
      ⟨d.globalFlux, μ, σ, d.globalFlux_pos, hσS, hσ0, hsign,
        fun s => d.globalFlux_lower_balance s, fun s => d.globalFlux_upper_balance μ hconst s⟩
  obtain ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne⟩ := hcap
  exact ⟨κ, x, y, hx.2, hy.2, hne, hx.1.symm.trans hy.1, hsx, hsy⟩

/-! ## The two Feinberg states -/

omit [DecidableEq S] [Fintype S] in
/-- **The two Feinberg states are distinct.**  The exponential state `e^μ` differs from the
all-ones state as soon as `μ` is nonzero. -/
theorem exp_ne_one_of_ne_zero (μ : S → ℝ) (hμ0 : μ ≠ 0) :
    (fun s => Real.exp (μ s)) ≠ (fun _ => (1 : ℝ)) := by
  intro h
  apply hμ0
  funext s
  have h1 := congrFun h s
  have h1' : Real.exp (μ s) = Real.exp 0 := h1.trans (by rw [Real.exp_zero])
  exact Real.exp_injective h1'

/-- **The two Feinberg states are stoichiometrically compatible** as soon as `e^μ − 1` lies in
the stoichiometric subspace. -/
theorem exp_pair_compatible (N : Network S) (μ : S → ℝ)
    (hcompat : (fun s => Real.exp (μ s) - 1) ∈ N.stoichSubspace) :
    N.StoichCompatible (fun _ => (1 : ℝ)) (fun s => Real.exp (μ s)) := by
  rw [StoichCompatible]
  have heq : (fun s => Real.exp (μ s)) - (fun _ => (1 : ℝ)) = fun s => Real.exp (μ s) - 1 := by
    funext s
    simp [Pi.sub_apply]
  rw [heq]
  exact hcompat

omit [DecidableEq S] [Fintype S] in
/-- **The log-ratio of the two Feinberg states is `μ`.**  This is the inverse of
`CRNT.Network.signCompatible_logRatio` for the constructed pair. -/
theorem exp_pair_logRatio (μ : S → ℝ) :
    (fun s => Real.log (Real.exp (μ s)) - Real.log ((1 : ℝ))) = μ := by
  funext s
  simp

/-! ## An end-to-end instance: the worked deficiency-one network -/

namespace DOAExample

open scoped BigOperators

/-- **The rate constants of the analytic construction on the example**: `κ = (1, 1, 1)`.  These
are the rate constants for which the all-ones state and the exponential state `e^μ` are both
mass-action steady states. -/
def analyticκ : RateConstants N := ⟨fun _ => 1, fun _ => by norm_num⟩

/-- **The lower balance of the example at the all-ones state.**  The reaction vectors of the
three reactions are `(1, 0)`, `(0, 1)` and `(−1, −1)`, and the rate constants are all equal, so
the lower balance `∑_r κ_r (y'_r − y_r) = 0` holds. -/
theorem analyticκ_lowerBalance (s : Species) :
    ∑ r, analyticκ.k r * N.reactionVector r s = 0 := by
  cases s <;>
    simp [analyticκ, univ_Rxn, Finset.sum_insert, Finset.sum_singleton, reaction,
      c0, cA, cB, cAB]

/-- **The upper balance of the example at the exponential state.**  Every source of the example
pairs with `μ = (1, −1)` at `0` — the sources are `0`, `0` and `A + B` — so the exponential
factors are all `1` and the upper balance coincides with the lower one. -/
theorem analyticκ_upperBalance (s : Species) :
    ∑ r, analyticκ.k r * Real.exp (complexPairing (N.reaction r).source μ) *
      N.reactionVector r s = 0 := by
  cases s <;>
    simp [analyticκ, univ_Rxn, Finset.sum_insert, Finset.sum_singleton, reaction,
      c0, cA, cB, cAB, complexPairing, sum_species, μ]

/-- **The two states of the construction lie in one compatibility class.**  The displacement
`e^μ − 1 = (e − 1, e^{-1} − 1)` is a combination of the reaction vectors of `0 → A` and
`0 → B`, which lie in the stoichiometric subspace of the example. -/
theorem analyticκ_compatible : (fun s => Real.exp (μ s) - 1) ∈ N.stoichSubspace := by
  have h1 : N.reactionVector Rxn.r1 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h2 : N.reactionVector Rxn.r2 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have heq : (fun s => Real.exp (μ s) - 1)
      = (Real.exp (μ Species.A) - 1) • N.reactionVector Rxn.r1
        + (Real.exp (μ Species.B) - 1) • N.reactionVector Rxn.r2 := by
    funext s
    cases s <;>
      simp [μ, reaction, c0, cA, cB, Network.reactionVector_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem _ h1) (N.stoichSubspace.smul_mem _ h2)

/-- **The analytic construction on the example: the two states are steady.**  For the rate
constants `κ = (1, 1, 1)` the all-ones state `x = (1, 1)` and the exponential state
`y = e^μ = (e, e^{-1})` are both mass-action steady states. -/
theorem analytic_steadyStates :
    N.IsMassActionSteadyState analyticκ (fun _ => 1) ∧
      N.IsMassActionSteadyState analyticκ (fun s => Real.exp (μ s)) :=
  shelfBalances_implies_steadyStates N analyticκ μ analyticκ_lowerBalance analyticκ_upperBalance

/-- **The log-ratio of the two states of the construction is the prescribed `μ`.**  The two
states of the construction realise exactly the log-ratio `μ = (1, −1)` of the Deficiency One
Algorithm's run on the example. -/
theorem analytic_logRatio :
    (fun s => Real.log (Real.exp (μ s)) - Real.log ((1 : ℝ))) = μ :=
  exp_pair_logRatio μ

/-- **The example has the capacity for multiple positive steady states, by the analytic route.**
This is the end-to-end instance of Feinberg's construction: the rate constants `κ = (1, 1, 1)`
are exhibited, the two states `x = (1, 1)` and `y = (e, e^{-1})` are exhibited, and both are
verified to be mass-action steady states by the balance computation above — not through the
feasibility test `DOAExample.doaFeasible`. -/
theorem analytic_capacity : N.HasMultistationarityCapacity :=
  analytic_construction_capacity N analyticκ μ (by
      intro h
      have h' := congrFun h Species.A
      simp [μ] at h')
    analyticκ_compatible analyticκ_lowerBalance analyticκ_upperBalance

end DOAExample

end Network

end CRNT

/-! ### The principal declarations -/

#print axioms CRNT.Network.linearised_upper_balance
#print axioms CRNT.Network.upperBalance_derivAt_zero
#print axioms CRNT.Network.massActionJacobianCLM_one
#print axioms CRNT.Network.shelfBalances_implies_steadyStates
#print axioms CRNT.Network.analytic_construction_capacity
#print axioms CRNT.Network.shelfFluxes_construction
#print axioms CRNT.Network.shelfFluxes_construction_capacity
#print axioms CRNT.Network.shelfFluxes_explicit_construction
#print axioms CRNT.Network.exp_pair_logRatio
#print axioms CRNT.Network.DOAExample.analytic_steadyStates
#print axioms CRNT.Network.DOAExample.analytic_capacity
