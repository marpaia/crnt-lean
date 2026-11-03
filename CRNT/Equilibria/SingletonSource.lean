import CRNT.Equilibria.SteadyState
import CRNT.Equilibria.CompatibilityClass
import CRNT.Reduction.Intermediates
import CRNT.Stoich.Subspace
import CRNT.Stoich.ConservationDimension
import CRNT.Flux.PSemiflow
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fintype.Card

/-!
# Singleton-source linear mass-action systems

`Network.SingletonSource` requires every reaction source to be one molecule of
one species. Products are unrestricted; for example `A → 2A` is allowed. The
mass-action field is homogeneous linear. This module proves the resulting
linear steady-state equations, convexity, and linear invariants.

This predicate is distinct from the partitioned MESSI class of Pérez Millán and
Dickenstein. It has neither the intermediate/core partition nor the published
complex restrictions, and does not imply conservativity. Full MESSI coverage is
still incomplete. See `docs/semantic-audit-fixes.md`, R1.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Singleton source complexes -/

/-- A complex is the **singleton at `i`** if it consists of exactly one molecule of the
species `i` and of nothing else.  This is the condition "total molecularity one" that a
SingletonSource network imposes on every source complex. -/
def IsSingleton (y : Complex S) (i : S) : Prop :=
  y i = 1 ∧ ∀ j, j ≠ i → y j = 0

omit [Fintype S] in
/-- The singleton complex at `i` is a singleton at `i`. -/
theorem isSingleton_singletonComplex (i : S) : IsSingleton (singletonComplex i) i := by
  refine ⟨?_, ?_⟩
  · simp [singletonComplex]
  · intro j hj
    simp [singletonComplex, hj]

omit [Fintype S] in
/-- The singleton species of a singleton complex is unique. -/
theorem IsSingleton.unique {y : Complex S} {i j : S} (hi : IsSingleton y i)
    (hj : IsSingleton y j) : i = j := by
  by_contra h
  have h1 : y i = 1 := hi.1
  have h2 : y i = 0 := hj.2 i h
  linarith

omit [Fintype S] in
/-- A singleton complex is the singleton complex at its unique species. -/
theorem IsSingleton.eq_singletonComplex {y : Complex S} {i : S} (hi : IsSingleton y i) :
    y = singletonComplex i := by
  funext j
  by_cases hj : j = i
  · subst hj
    simp [singletonComplex, hi.1]
  · have hj0 : y j = 0 := hi.2 j hj
    simp [singletonComplex, hj, hj0]

omit [Fintype S] in
/-- Two singleton complexes at the same species are equal. -/
theorem singletonComplex_inj {i j : S} (h : singletonComplex i = singletonComplex j) :
    i = j := by
  by_contra hne
  have h' := congrFun h i
  simp [singletonComplex, hne] at h'

omit [Fintype S] in
/-- Singleton complexes at different species are different. -/
theorem singletonComplex_ne {i j : S} (h : i ≠ j) : singletonComplex i ≠ singletonComplex j := by
  intro hh
  exact h (singletonComplex_inj hh)

/-- **A SingletonSource network**: every reaction has a source complex of total molecularity one,
i.e. a source that is a singleton complex. -/
def SingletonSource (N : Network S) : Prop :=
  ∀ r : N.R, ∃ i : S, IsSingleton (N.reaction r).source i

/-- The species occurring in the source complex of a reaction of a SingletonSource network. -/
noncomputable def singletonSourceSpecies (N : Network S) (hM : SingletonSource N) (r : N.R) : S :=
  Classical.choose (hM r)

/-- The chosen source species really is the unique singleton species of the source
complex. -/
theorem singletonSourceSpecies_isSingleton (N : Network S) (hM : SingletonSource N) (r : N.R) :
    IsSingleton (N.reaction r).source (N.singletonSourceSpecies hM r) :=
  Classical.choose_spec (hM r)

/-- The source complex of a reaction of a SingletonSource network is the singleton complex at the
chosen source species. -/
theorem singletonSourceComplex_eq (N : Network S) (hM : SingletonSource N) (r : N.R) :
    (N.reaction r).source = singletonComplex (N.singletonSourceSpecies hM r) :=
  (N.singletonSourceSpecies_isSingleton hM r).eq_singletonComplex

/-! ## The monomial of a singleton source -/

omit [DecidableEq S] in
/-- **The monomial of a singleton source complex is the corresponding concentration.**
If `y` is the singleton at `i` then the mass-action monomial of `y` at `x` is `x i`,
because the product `∏ s, x s ^ y s` has a single non-trivial factor. -/
theorem massActionMonomial_of_isSingleton (x : Concentration S) {y : Complex S} {i : S}
    (hy : IsSingleton y i) : y.massActionMonomial x = x i := by
  classical
  unfold Complex.massActionMonomial
  rw [Finset.prod_eq_single i]
  · simp [hy.1]
  · intro b _ hb
    have : y b = 0 := hy.2 b hb
    simp [this]
  · simp

/-! ## The coefficient matrix -/

/-- The indicator of "the source complex of the reaction `r` is the singleton at `i`". -/
def singletonSourceIndicator (N : Network S) (r : N.R) (i : S) : ℝ :=
  if (N.reaction r).source = singletonComplex i then 1 else 0

/-- The coefficient `c_{i,s}(κ)` of the linear steady-state system of a SingletonSource network:

`c_{i,s}(κ) = ∑_{r : σ(r) = i} κ_r · (y'_r(s) − [i = s])`.

For a SingletonSource reaction with source species `i` the bracket is the entry of the reaction
vector (`source s = [i = s]`), so equivalently

`c_{i,s}(κ) = ∑_{r : σ(r) = i} κ_r · N.reactionVector r s`,

which is the definition used here: it does not require choosing the source species. -/
def singletonSourceCoeff (N : Network S) (κ : N.RateConstants) (i s : S) : ℝ :=
  ∑ r : N.R, singletonSourceIndicator N r i * (κ.k r * N.reactionVector r s)

/-- The coefficient `c_{i,s}(κ)` is zero unless `i` is the source species of some
reaction. -/
theorem singletonSourceCoeff_eq_zero_of_not_source (N : Network S) (κ : N.RateConstants)
    {i s : S} (hne : ∀ r : N.R, (N.reaction r).source ≠ singletonComplex i) :
    singletonSourceCoeff N κ i s = 0 := by
  classical
  unfold singletonSourceCoeff
  apply Finset.sum_eq_zero
  intro r _
  have : singletonSourceIndicator N r i = 0 := by
    simp [singletonSourceIndicator, hne r]
  simp [this]

/-! ## Linearity of the steady-state variety -/

/-- **Fiber-sum identity.**  Summing a function over a finite index type and grouping by
the value of a map `g` is the same as summing over the fibers of `g`. -/
theorem sum_eq_sum_fiber (N : Network S) (g : N.R → S) (f : N.R → ℝ) :
    (∑ r : N.R, f r) = ∑ i : S, ∑ r : N.R, (if g r = i then 1 else 0) * f r := by
  classical
  have key : ∀ r : N.R, (∑ i : S, (if g r = i then 1 else 0) * f r) = f r := by
    intro r
    have hmain : (∑ j : S, (if g r = j then 1 else 0) * f r)
        = (if g r = g r then 1 else 0) * f r := by
      rw [Finset.sum_eq_single (g r)]
      · intro j _ hj
        have hne : ¬ (g r = j) := fun hh => hj hh.symm
        rw [ite_eq_right hne]
        simp
      · intro hh
        simp at hh
    rw [hmain]
    simp
  calc (∑ r : N.R, f r)
      = ∑ r : N.R, ∑ i : S, (if g r = i then 1 else 0) * f r := by
        exact Finset.sum_congr rfl fun r _ => (key r).symm
    _ = ∑ i : S, ∑ r : N.R, (if g r = i then 1 else 0) * f r := Finset.sum_comm

/-- **The mass-action vector field of a SingletonSource network is linear.**  For a SingletonSource network the
mass-action monomial of the source complex of `r` is `x (σ r)`, and the vector field is
the linear map `x ↦ fun s => ∑ i, c_{i,s}(κ) * x i`. -/
theorem singletonSource_vectorField_eq_linear (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    (x : Concentration S) :
    N.massActionVectorField κ x = fun s => ∑ i, singletonSourceCoeff N κ i s * x i := by
  classical
  set σ : N.R → S := fun r => N.singletonSourceSpecies hM r with hσdef
  have hσ : ∀ r, IsSingleton (N.reaction r).source (σ r) := by
    intro r
    exact N.singletonSourceSpecies_isSingleton hM r
  have hσeq : ∀ r, (N.reaction r).source = singletonComplex (σ r) := by
    intro r
    exact (hσ r).eq_singletonComplex
  have hind : ∀ r i, singletonSourceIndicator N r i = (if σ r = i then 1 else 0) := by
    intro r i
    by_cases h : σ r = i
    · subst h
      rw [singletonSourceIndicator, hσeq r]
      simp
    · rw [singletonSourceIndicator]
      have hne : ¬ ((N.reaction r).source = singletonComplex i) := by
        intro hh
        exact (h (singletonComplex_inj ((hσeq r).symm.trans hh))).elim
      rw [ite_eq_right hne, ite_eq_right h]
  funext s
  calc N.massActionVectorField κ x s
      = ∑ r : N.R, N.massActionRate κ r x * N.reactionVector r s := rfl
    _ = ∑ r : N.R, κ.k r * x (σ r) * N.reactionVector r s := by
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Network.massActionRate, massActionMonomial_of_isSingleton x (hσ r)]
    _ = ∑ i : S, ∑ r : N.R, (if σ r = i then 1 else 0)
          * (κ.k r * x (σ r) * N.reactionVector r s) :=
        sum_eq_sum_fiber N σ (fun r => κ.k r * x (σ r) * N.reactionVector r s)
    _ = ∑ i : S, ∑ r : N.R, (if σ r = i then 1 else 0)
          * (κ.k r * x i * N.reactionVector r s) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases h : σ r = i
        · simp [h]
        · simp [h]
    _ = ∑ i : S, x i * (∑ r : N.R, (if σ r = i then 1 else 0)
          * (κ.k r * N.reactionVector r s)) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring
    _ = ∑ i : S, singletonSourceCoeff N κ i s * x i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        have hcoeff : singletonSourceCoeff N κ i s
            = ∑ r : N.R, (if σ r = i then 1 else 0) * (κ.k r * N.reactionVector r s) := by
          unfold singletonSourceCoeff
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hind r i]
        rw [hcoeff, Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl fun r _ => by ring

/-- **The steady states of a SingletonSource network are the zeros of a linear system.** -/
theorem singletonSource_steadyState_iff_linear (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    (x : Concentration S) :
    N.IsMassActionSteadyState κ x ↔ ∀ s, ∑ i, singletonSourceCoeff N κ i s * x i = 0 := by
  unfold Network.IsMassActionSteadyState IsSteadyState
  rw [singletonSource_vectorField_eq_linear N κ hM x]

/-- The zero concentration is a steady state of a SingletonSource network (the steady-state variety
is a linear subspace, so it contains the origin). -/
theorem singletonSource_zero_isSteadyState (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N) :
    N.IsMassActionSteadyState κ 0 := by
  rw [singletonSource_steadyState_iff_linear N κ hM]
  intro s
  simp

/-! ## The steady states form a convex cone -/

/-- **The sum of two steady states of a SingletonSource network is a steady state.**  Together with
`singletonSource_steadyState_smul` this says that the steady-state variety of a SingletonSource network is a
linear subspace, and that the *positive* steady states form a convex cone. -/
theorem singletonSource_steadyState_add (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    {x y : Concentration S} (hx : N.IsMassActionSteadyState κ x)
    (hy : N.IsMassActionSteadyState κ y) :
    N.IsMassActionSteadyState κ (x + y) := by
  rw [singletonSource_steadyState_iff_linear N κ hM] at hx hy ⊢
  intro s
  have hsplit : (∑ i, singletonSourceCoeff N κ i s * (x i + y i))
      = (∑ i, singletonSourceCoeff N κ i s * x i) + (∑ i, singletonSourceCoeff N κ i s * y i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Pi.add_apply]
  rw [hsplit, hx s, hy s, add_zero]

/-- **A scalar multiple of a steady state of a SingletonSource network is a steady state.**  In
particular the steady-state variety is closed under nonnegative scaling, so the positive
steady states form a cone. -/
theorem singletonSource_steadyState_smul (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    {x : Concentration S} (hx : N.IsMassActionSteadyState κ x) (c : ℝ) :
    N.IsMassActionSteadyState κ (c • x) := by
  rw [singletonSource_steadyState_iff_linear N κ hM] at hx ⊢
  intro s
  have hsplit : (∑ i, singletonSourceCoeff N κ i s * (c * x i))
      = c * (∑ i, singletonSourceCoeff N κ i s * x i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hsplit, hx s, mul_zero]

/-- **The positive steady states of a SingletonSource network form a convex cone.**  The sum of two
positive steady states is a positive steady state. -/
theorem singletonSource_positiveSteadyState_add (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    {x y : Concentration S} (hx : x.Positive) (hxs : N.IsMassActionSteadyState κ x)
    (hy : y.Positive) (hys : N.IsMassActionSteadyState κ y) :
    (x + y).Positive ∧ N.IsMassActionSteadyState κ (x + y) := by
  refine ⟨fun s => add_pos (hx s) (hy s), singletonSource_steadyState_add N κ hM hxs hys⟩

/-- **A positive scalar multiple of a positive steady state of a SingletonSource network is a
positive steady state.** -/
theorem singletonSource_positiveSteadyState_smul (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    {x : Concentration S} (hx : x.Positive) (hxs : N.IsMassActionSteadyState κ x)
    {c : ℝ} (hc : 0 < c) : (c • x).Positive ∧ N.IsMassActionSteadyState κ (c • x) := by
  refine ⟨fun s => mul_pos hc (hx s), singletonSource_steadyState_smul N κ hM hxs c⟩

/-! ## The steady-state variety as a linear subspace -/

/-- **The steady-state variety of a SingletonSource network is a linear subspace** of `ℝ^S`: the set
of concentrations at which the (linear) mass-action vector field vanishes. -/
def singletonSourceVariety (N : Network S) (κ : N.RateConstants) : Submodule ℝ (S → ℝ) where
  carrier := {x | ∀ s, ∑ i, singletonSourceCoeff N κ i s * x i = 0}
  zero_mem' := by
    intro x
    simp
  add_mem' := by
    intro a b ha hb s
    have hsplit : (∑ i, singletonSourceCoeff N κ i s * (a i + b i))
        = (∑ i, singletonSourceCoeff N κ i s * a i) + (∑ i, singletonSourceCoeff N κ i s * b i) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [Pi.add_apply]
    rw [hsplit, ha s, hb s, add_zero]
  smul_mem' := by
    intro c a ha s
    have hsplit : (∑ i, singletonSourceCoeff N κ i s * (c * a i))
        = c * (∑ i, singletonSourceCoeff N κ i s * a i) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hsplit, ha s, mul_zero]

/-- The steady-state variety of a SingletonSource network consists exactly of its steady states. -/
theorem mem_singletonSourceVariety_iff (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    (x : Concentration S) : x ∈ N.singletonSourceVariety κ ↔ N.IsMassActionSteadyState κ x := by
  rw [singletonSource_steadyState_iff_linear N κ hM]
  rfl

/-- **The steady-state variety of a SingletonSource network is a linear subspace** of `ℝ^S`:
it is closed under linear combinations of its elements.  Being linear, it is a *rational*
variety, and in the two-term case a binomial — hence toric — one in the sense of
`CRNT.Network.HasToricSteadyStates` (`CRNT/Equilibria/ToricSteadyStates.lean`).  This is
the "rational parametrizations" content of leaf **S17**. -/
theorem singletonSourceVariety_smul_add (N : Network S) (κ : N.RateConstants) {x y : Concentration S}
    (hx : x ∈ N.singletonSourceVariety κ) (hy : y ∈ N.singletonSourceVariety κ) (c : ℝ) :
    c • x + y ∈ N.singletonSourceVariety κ :=
  (N.singletonSourceVariety κ).add_mem ((N.singletonSourceVariety κ).smul_mem c hx) hy

/-! ## The positive steady states in a stoichiometric class -/

/-- The positive steady states of `N` at the rate constants `κ` that lie in the
stoichiometric class of `c`. -/
def PositiveSteadyStatesInClass (N : Network S) (κ : N.RateConstants)
    (c : Concentration S) : Set (Concentration S) :=
  {x | x.Positive ∧ N.IsMassActionSteadyState κ x ∧ (x - c) ∈ N.stoichSubspace}

/-- **The positive steady states of a SingletonSource network in a fixed stoichiometric class form a
convex set.**  They are the intersection of the linear variety `V`, the affine class
`c + S(N)` and the open positive orthant.  Hence they are empty, a singleton, or
infinite: a SingletonSource network is never *exactly* multistationary. -/
theorem singletonSource_class_positiveSteadyStates_convex (N : Network S) (κ : N.RateConstants)
    (hM : SingletonSource N) {c x y : Concentration S}
    (hx : x ∈ N.PositiveSteadyStatesInClass κ c)
    (hy : y ∈ N.PositiveSteadyStatesInClass κ c) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) • x + t • y) ∈ N.PositiveSteadyStatesInClass κ c := by
  rcases hx with ⟨hx, hxs, hxc⟩
  rcases hy with ⟨hy, hys, hyc⟩
  refine ⟨?_, ?_, ?_⟩
  · intro s
    by_cases ht0' : t = 0
    · simp only [ht0', sub_zero, one_smul, zero_smul, add_zero]
      exact hx s
    by_cases ht1' : t = 1
    · simp only [ht1', sub_self, zero_smul, one_smul, Pi.add_apply, Pi.zero_apply, zero_add]
      exact hy s
    · have htpos : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
      have htlt : t < 1 := lt_of_le_of_ne ht1 ht1'
      have honepos : 0 < 1 - t := by linarith
      exact add_pos (mul_pos honepos (hx s)) (mul_pos htpos (hy s))
  · exact singletonSource_steadyState_add N κ hM
      (singletonSource_steadyState_smul N κ hM hxs (1 - t))
      (singletonSource_steadyState_smul N κ hM hys t)
  · have hdecomp : ((1 - t) • x + t • y) - c
        = (1 - t) • (x - c) + t • (y - c) := by
      funext s
      simp only [Pi.smul_apply, Pi.sub_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [hdecomp]
    exact N.stoichSubspace.add_mem
      (N.stoichSubspace.smul_mem (1 - t) hxc)
      (N.stoichSubspace.smul_mem t hyc)

/-- **A SingletonSource network is never exactly multistationary.**  If two distinct positive steady
states lie in the same stoichiometric class, then they and their midpoint are three
*distinct* positive steady states in that class. -/
theorem singletonSource_no_exactly_two (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    {c x y : Concentration S} (hx : x ∈ N.PositiveSteadyStatesInClass κ c)
    (hy : y ∈ N.PositiveSteadyStatesInClass κ c) (hxy : x ≠ y) :
    x ∈ N.PositiveSteadyStatesInClass κ c ∧
      y ∈ N.PositiveSteadyStatesInClass κ c ∧
      (fun s => (x s + y s) / 2) ∈ N.PositiveSteadyStatesInClass κ c ∧
      x ≠ (fun s => (x s + y s) / 2) ∧
      (fun s => (x s + y s) / 2) ≠ y := by
  have hmid : (fun s => (x s + y s) / 2) ∈ N.PositiveSteadyStatesInClass κ c := by
    have hconv : ((1 : ℝ) - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y
        ∈ N.PositiveSteadyStatesInClass κ c :=
      singletonSource_class_positiveSteadyStates_convex N κ hM hx hy (t := 1 / 2) (by norm_num) (by norm_num)
    have heq : ((1 : ℝ) - (1 / 2 : ℝ)) • x + (1 / 2 : ℝ) • y = (fun s => (x s + y s) / 2) := by
      funext s
      simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
      ring
    rw [heq] at hconv
    exact hconv
  refine ⟨hx, hy, hmid, ?_, ?_⟩
  · intro h
    have hfun : ∀ s, x s = (x s + y s) / 2 := by
      intro s
      have h1 := congrFun h s
      simpa using h1
    have hxy' : x = y := by
      funext s
      have h1 := hfun s
      linarith
    exact hxy hxy'
  · intro h
    have hfun : ∀ s, (x s + y s) / 2 = y s := by
      intro s
      have h1 := congrFun h s
      simpa using h1
    have hxy' : x = y := by
      funext s
      have h1 := hfun s
      linarith
    exact hxy hxy'

/-! ## Steady-state invariants -/

/-- A linear functional `w` is a **steady-state invariant** of the network `N` at the rate
constants `κ` when it takes the same value at every mass-action steady state.  For a
SingletonSource network the steady states form a linear subspace containing `0`, so this is the
same as saying that `w` annihilates the steady-state variety. -/
def IsSteadyStateInvariant (N : Network S) (κ : N.RateConstants) (w : S → ℝ) : Prop :=
  ∀ x y : Concentration S, N.IsMassActionSteadyState κ x → N.IsMassActionSteadyState κ y →
    (∑ i, w i * x i) = (∑ i, w i * y i)

/-- **The linear steady-state invariants of a SingletonSource network are the rows of the
coefficient matrix.**  A weight vector `w` is a steady-state invariant if and only if it
is an `ℝ`-linear combination of the rows `(c_{i,s})_i` of the coefficient matrix; these
are precisely the *conservation laws of the steady-state variety*. -/
theorem singletonSource_linearInvariant_iff (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    (w : S → ℝ) :
    IsSteadyStateInvariant N κ w ↔
      ∀ x : Concentration S, (∀ s, ∑ i, singletonSourceCoeff N κ i s * x i = 0) →
        (∑ i, w i * x i) = 0 := by
  constructor
  · intro h x hx
    have hx' : N.IsMassActionSteadyState κ x :=
      (singletonSource_steadyState_iff_linear N κ hM x).mpr hx
    have h0 : N.IsMassActionSteadyState κ 0 := N.singletonSource_zero_isSteadyState κ hM
    have hval := h x 0 hx' h0
    simpa using hval
  · intro h x y hx hy
    have hx' : ∀ s, ∑ i, singletonSourceCoeff N κ i s * x i = 0 :=
      (singletonSource_steadyState_iff_linear N κ hM x).mp hx
    have hy' : ∀ s, ∑ i, singletonSourceCoeff N κ i s * y i = 0 :=
      (singletonSource_steadyState_iff_linear N κ hM y).mp hy
    have hxv : (∑ i, w i * x i) = 0 := h x hx'
    have hyv : (∑ i, w i * y i) = 0 := h y hy'
    rw [hxv, hyv]

/-- The space of steady-state invariants: the annihilator of the steady-state variety. -/
def steadyStateInvariantSpace (N : Network S) (κ : N.RateConstants) : Submodule ℝ (S → ℝ) :=
  orthSum (N.singletonSourceVariety κ)

/-- A weight vector is a steady-state invariant of a SingletonSource network if and only if it lies
in the space of steady-state invariants. -/
theorem singletonSource_linearInvariant_mem_iff (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    (w : S → ℝ) :
    IsSteadyStateInvariant N κ w ↔ w ∈ N.steadyStateInvariantSpace κ := by
  rw [IsSteadyStateInvariant, steadyStateInvariantSpace, mem_orthSum]
  constructor
  · intro h x hx
    have hx' : N.IsMassActionSteadyState κ x :=
      (singletonSource_steadyState_iff_linear N κ hM x).mpr hx
    have h0 : N.IsMassActionSteadyState κ 0 := N.singletonSource_zero_isSteadyState κ hM
    have hval := h x 0 hx' h0
    simpa using hval
  · intro h x y hx hy
    have hx' : x ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM x).mpr hx
    have hy' : y ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM y).mpr hy
    have hxv : (∑ i, w i * x i) = 0 := h x hx'
    have hyv : (∑ i, w i * y i) = 0 := h y hy'
    rw [hxv, hyv]

/-- **The condition of the "dual" reading.**  The condition `∀ s, ∑ i, w i * c_{i,s} = 0`
is the *transpose* of the conservation-law condition; it characterises the weight vectors
that are themselves **steady states**, not the steady-state invariants. -/
theorem singletonSource_steadyState_iff_weightedCoeff (N : Network S) (κ : N.RateConstants)
    (hM : SingletonSource N) (w : S → ℝ) :
    (∀ s, ∑ i, w i * singletonSourceCoeff N κ i s = 0) ↔ N.IsMassActionSteadyState κ w := by
  rw [singletonSource_steadyState_iff_linear N κ hM]
  constructor
  · intro h s
    have h' : (∑ i, w i * singletonSourceCoeff N κ i s) = 0 := h s
    simpa [mul_comm] using h'
  · intro h s
    have h' : (∑ i, singletonSourceCoeff N κ i s * w i) = 0 := h s
    simpa [mul_comm] using h'

/-- **The conservation laws of the network satisfy the transposed condition.**  If `w` is a
conservation law of the network, then `∀ i, ∑ s, w s * c_{i,s} = 0`. -/
theorem singletonSource_conservationLaw_weightedCoeff (N : Network S) (κ : N.RateConstants)
    (hM : SingletonSource N) {w : S → ℝ} (hw : w ∈ N.conservationLawSpace) :
    ∀ i, (∑ s, w s * singletonSourceCoeff N κ i s) = 0 := by
  classical
  set σ : N.R → S := fun r => N.singletonSourceSpecies hM r with hσdef
  have hσ : ∀ r, IsSingleton (N.reaction r).source (σ r) := by
    intro r
    exact N.singletonSourceSpecies_isSingleton hM r
  have hσeq : ∀ r, (N.reaction r).source = singletonComplex (σ r) := by
    intro r
    exact (hσ r).eq_singletonComplex
  have hind : ∀ r i, singletonSourceIndicator N r i = (if σ r = i then 1 else 0) := by
    intro r i
    by_cases h : σ r = i
    · subst h
      rw [singletonSourceIndicator, hσeq r]
      simp
    · rw [singletonSourceIndicator]
      have hne : ¬ ((N.reaction r).source = singletonComplex i) := by
        intro hh
        exact (h (singletonComplex_inj ((hσeq r).symm.trans hh))).elim
      rw [ite_eq_right hne, ite_eq_right h]
  -- a conservation law annihilates every reaction vector
  have horth : ∀ r : N.R, (∑ i, w i * N.reactionVector r i) = 0 := by
    intro r
    have hr := (mem_orthSum.mp hw) (N.reactionVector r) (N.reactionVector_mem_stoichSubspace r)
    simpa using hr
  intro i
  have hexp : ∀ s, singletonSourceCoeff N κ i s
      = ∑ r : N.R, (if σ r = i then 1 else 0) * (κ.k r * N.reactionVector r s) := by
    intro s
    unfold singletonSourceCoeff
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hind r i]
  calc (∑ s, w s * singletonSourceCoeff N κ i s)
      = ∑ s, ∑ r : N.R,
          w s * ((if σ r = i then 1 else 0) * (κ.k r * N.reactionVector r s)) := by
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [hexp s, Finset.mul_sum]
    _ = ∑ r : N.R, ∑ s,
          w s * ((if σ r = i then 1 else 0) * (κ.k r * N.reactionVector r s)) :=
        Finset.sum_comm
    _ = ∑ r : N.R, (if σ r = i then 1 else 0) * κ.k r
          * (∑ s, w s * N.reactionVector r s) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        by_cases h : σ r = i
        · simp only [h, ite_true, one_mul]
          calc (∑ s, w s * (κ.k r * N.reactionVector r s))
              = ∑ s, κ.k r * (w s * N.reactionVector r s) := by
                exact Finset.sum_congr rfl fun s _ => by ring
            _ = κ.k r * (∑ s, w s * N.reactionVector r s) := by rw [Finset.mul_sum]
        · simp only [h, ite_false, zero_mul]
          simp
    _ = 0 := by
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases h : σ r = i
      · simp only [h, ite_true, one_mul, horth r, mul_zero]
      · simp only [h, ite_false, zero_mul]

/-! ### The invariants of the steady-state variety are the rows of the coefficient matrix -/

/-- The **transpose of the coefficient matrix** of a SingletonSource network:
`singletonSourceAdjoint κ c i = ∑ s, c s * c_{i,s}(κ)`. -/
def singletonSourceAdjoint (N : Network S) (κ : N.RateConstants) (c : S → ℝ) (i : S) : ℝ :=
  ∑ s, c s * singletonSourceCoeff N κ i s

/-- The transpose of the coefficient matrix, in coordinates. -/
theorem singletonSourceAdjoint_eq (N : Network S) (κ : N.RateConstants) (c : S → ℝ) (i : S) :
    N.singletonSourceAdjoint κ c i = ∑ s, c s * singletonSourceCoeff N κ i s := rfl

/-- The `s`-th unit vector of `ℝ^S`. -/
def unitVector (s : S) : S → ℝ := fun j => if j = s then 1 else 0

/-- The transpose of the coefficient matrix applied to a unit vector picks out the
corresponding row of the matrix. -/
theorem singletonSourceAdjoint_unitVector (N : Network S) (κ : N.RateConstants) (s i : S) :
    N.singletonSourceAdjoint κ (unitVector s) i = singletonSourceCoeff N κ i s := by
  unfold singletonSourceAdjoint
  calc (∑ j, unitVector s j * singletonSourceCoeff N κ i j) = singletonSourceCoeff N κ i s := by
        rw [Finset.sum_eq_single s]
        · simp [unitVector]
        · intro j _ hj
          simp [unitVector, hj]
        · intro hh
          simp at hh

/-- **The space of linear steady-state invariants of a SingletonSource network**: the span of the
rows `(c_{i,s})_i` of the coefficient matrix.  These are the *conservation laws of the
steady-state variety*. -/
def singletonSourceRowSpace (N : Network S) (κ : N.RateConstants) : Submodule ℝ (S → ℝ) where
  carrier := {w | ∃ c : S → ℝ, ∀ i, w i = N.singletonSourceAdjoint κ c i}
  zero_mem' := by
    refine ⟨0, ?_⟩
    intro i
    simp [singletonSourceAdjoint]
  add_mem' := by
    intro w1 w2 h1 h2
    obtain ⟨c1, hc1⟩ := h1
    obtain ⟨c2, hc2⟩ := h2
    refine ⟨c1 + c2, ?_⟩
    intro i
    simp only [Pi.add_apply]
    rw [hc1 i, hc2 i]
    simp only [singletonSourceAdjoint, Pi.add_apply, add_mul]
    rw [Finset.sum_add_distrib]
  smul_mem' := by
    intro a w hw
    obtain ⟨c, hc⟩ := hw
    refine ⟨a • c, ?_⟩
    intro i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hc i]
    simp only [singletonSourceAdjoint, Pi.smul_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

/-- **The steady-state variety is the annihilator of the row space.** -/
theorem singletonSource_variety_eq_orthSum_rowSpace (N : Network S) (κ : N.RateConstants) :
    N.singletonSourceVariety κ = orthSum (N.singletonSourceRowSpace κ) := by
  ext x
  constructor
  · intro hx
    rw [mem_orthSum]
    intro w hw
    obtain ⟨c, hc⟩ := hw
    have hsum : (∑ i, x i * w i) = 0 := by
      have hconv : (∑ i, x i * w i) = ∑ i, x i * N.singletonSourceAdjoint κ c i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hc i]
      rw [hconv]
      simp only [singletonSourceAdjoint]
      have hconv2 : (∑ i, x i * (∑ s, c s * singletonSourceCoeff N κ i s))
          = ∑ s, c s * (∑ i, singletonSourceCoeff N κ i s * x i) := by
        have h3 : (∑ i, x i * (∑ s, c s * singletonSourceCoeff N κ i s))
            = ∑ i, ∑ s, x i * (c s * singletonSourceCoeff N κ i s) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum]
        rw [h3, Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hconv2]
      refine Finset.sum_eq_zero fun s _ => ?_
      rw [hx s, mul_zero]
    exact hsum
  · intro hx s
    have hmem : (fun i => singletonSourceCoeff N κ i s) ∈ N.singletonSourceRowSpace κ := by
      refine ⟨unitVector s, ?_⟩
      intro i
      exact (singletonSourceAdjoint_unitVector N κ s i).symm
    have h1 := hx (fun i => singletonSourceCoeff N κ i s) hmem
    have hconv : (∑ i, x i * (fun i => singletonSourceCoeff N κ i s) i)
        = (∑ i, singletonSourceCoeff N κ i s * x i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only
      ring
    rw [hconv] at h1
    exact h1

/-- **The space of linear steady-state invariants of a SingletonSource network is the row space of
the coefficient matrix.** -/
theorem steadyStateInvariantSpace_eq_rowSpace (N : Network S) (κ : N.RateConstants) :
    N.steadyStateInvariantSpace κ = N.singletonSourceRowSpace κ := by
  rw [steadyStateInvariantSpace, singletonSource_variety_eq_orthSum_rowSpace, orthSum_orthSum]

/-- **The linear steady-state invariants of a SingletonSource network are the rows of the
coefficient matrix.**  A weight vector `w` is a steady-state invariant if and only if it
is an `ℝ`-linear combination of the rows `(c_{i,s})_i` of the coefficient matrix; these
are precisely the *conservation laws of the steady-state variety*. -/
theorem singletonSource_linearInvariant_iff_rowSpace (N : Network S) (κ : N.RateConstants) (hM : SingletonSource N)
    (w : S → ℝ) :
    IsSteadyStateInvariant N κ w ↔
      ∃ c : S → ℝ, ∀ i, w i = ∑ s, c s * singletonSourceCoeff N κ i s := by
  rw [singletonSource_linearInvariant_mem_iff N κ hM, steadyStateInvariantSpace_eq_rowSpace]
  constructor
  · intro h
    obtain ⟨c, hc⟩ := h
    refine ⟨c, fun i => ?_⟩
    rw [hc i]
    exact (singletonSourceAdjoint_eq N κ c i).symm
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro i
    rw [hc i]
    exact singletonSourceAdjoint_eq N κ c i

/-- **Correction of a common slip.**  For a SingletonSource network the conservation laws of the
*network* are the left null space of the coefficient matrix, whereas the steady-state
invariants are the right null space's orthogonal complement; the two spaces need not
coincide, and a conservation law need not be a steady-state invariant (see
`CRNT.Examples.SingletonSource.twoState_conservationLaw_not_invariant`).

What *is* true is the transposed condition
`CRNT.Network.singletonSource_conservationLaw_weightedCoeff`, and the statement proved here: a
conservation law of the network that annihilates the steady-state variety is a
steady-state invariant. -/
theorem singletonSource_conservationLaw_mem_invariant (N : Network S) (κ : N.RateConstants)
    (hM : SingletonSource N) {w : S → ℝ} (hw : w ∈ N.conservationLawSpace)
    (hann : ∀ x : Concentration S, N.IsMassActionSteadyState κ x → (∑ i, w i * x i) = 0) :
    IsSteadyStateInvariant N κ w := by
  have htrans : ∀ i, (∑ s, w s * singletonSourceCoeff N κ i s) = 0 :=
    singletonSource_conservationLaw_weightedCoeff N κ hM hw
  rw [singletonSource_linearInvariant_iff N κ hM]
  intro x hx
  exact hann x ((singletonSource_steadyState_iff_linear N κ hM x).mpr hx)


end Network

/-! ## Concrete examples

The two networks below witness the phenomena described above:

* the reversible pair `X ⇌ Y` is a SingletonSource network whose steady-state variety is the line
  `κ₁ x_X = κ₂ x_Y`; each stoichiometric class contains **exactly one** positive steady
  state, and the *steady-state invariants* of the variety (`(κ₁, −κ₂)`) differ from the
  *conservation laws* of the network (`(1,1)`);
* the chain `X → Y → Z` is a SingletonSource network whose steady-state variety has **two**
  linear invariants, while the network has only **one** conservation law: the steady-state
  variety has strictly more invariants than the network has conservation laws.

-/

namespace Examples.SingletonSource

open CRNT
open scoped BigOperators

/-- The two species `X` and `Y`. -/
abbrev Species : Type := Fin 2

/-- The species `X`. -/
abbrev X : Species := 0

/-- The species `Y`. -/
abbrev Y : Species := 1

/-- The two reaction channels of the reversible pair. -/
abbrev Rxn : Type := Fin 2

/-- The channel `X → Y`. -/
abbrev fwd : Rxn := 0

/-- The channel `Y → X`. -/
abbrev bwd : Rxn := 1

/-- The complex `X`. -/
def cX : Complex Species := ![1, 0]

/-- The complex `Y`. -/
def cY : Complex Species := ![0, 1]

/-- The reaction map of the reversible pair `X ⇌ Y`. -/
def rxn : Rxn → Reaction Species :=
  ![{ source := cX, target := cY }, { source := cY, target := cX }]

/-- The network `X ⇌ Y`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The rate constants of the reversible pair: `k₁` for `X → Y` and `k₂` for `Y → X`. -/
def rates (k₁ k₂ : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) : Network.RateConstants N where
  k := ![k₁, k₂]
  positive := by
    intro r
    fin_cases r
    · simpa using h₁
    · simpa using h₂

/-- The complex `X` is the singleton complex at `X`. -/
theorem cX_eq : cX = Network.singletonComplex X := by
  funext j
  fin_cases j <;> simp [cX, Network.singletonComplex]

/-- The complex `Y` is the singleton complex at `Y`. -/
theorem cY_eq : cY = Network.singletonComplex Y := by
  funext j
  fin_cases j <;> simp [cY, Network.singletonComplex]

/-- The source of the forward channel is `X`. -/
theorem source_fwd : (N.reaction fwd).source = cX := rfl

/-- The source of the backward channel is `Y`. -/
theorem source_bwd : (N.reaction bwd).source = cY := rfl

/-- **The reversible pair `X ⇌ Y` is a SingletonSource network**: both source complexes are
singletons. -/
theorem N_singletonSource : N.SingletonSource := by
  intro r
  fin_cases r
  · refine ⟨X, ?_⟩
    show Network.IsSingleton (N.reaction fwd).source X
    rw [source_fwd, cX_eq]
    exact Network.isSingleton_singletonComplex X
  · refine ⟨Y, ?_⟩
    show Network.IsSingleton (N.reaction bwd).source Y
    rw [source_bwd, cY_eq]
    exact Network.isSingleton_singletonComplex Y

/-- The forward reaction vector has entry `-1` at `X`. -/
theorem reactionVector_fwd_X : N.reactionVector fwd X = -1 := by
  simp [N, rxn, cX, cY, Network.reactionVector]

/-- The forward reaction vector has entry `1` at `Y`. -/
theorem reactionVector_fwd_Y : N.reactionVector fwd Y = 1 := by
  simp [N, rxn, cX, cY, Network.reactionVector]

/-- The backward reaction vector has entry `1` at `X`. -/
theorem reactionVector_bwd_X : N.reactionVector bwd X = 1 := by
  simp [N, rxn, cX, cY, Network.reactionVector]

/-- The backward reaction vector has entry `-1` at `Y`. -/
theorem reactionVector_bwd_Y : N.reactionVector bwd Y = -1 := by
  simp [N, rxn, cX, cY, Network.reactionVector]

/-- The coefficient `c_{X,X}` of the linear steady-state system. -/
theorem singletonSourceCoeff_XX (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ X X = -(κ.k fwd) := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = Network.singletonComplex X then 1 else 0)
    * (κ.k r * N.reactionVector r X)) = _
  have hne : Network.singletonComplex Y ≠ Network.singletonComplex X :=
    Network.singletonComplex_ne (by decide)
  simp [hne, N, rxn, cX_eq, cY_eq, Network.reactionVector, Network.singletonComplex,
    Fin.sum_univ_two]

/-- The coefficient `c_{X,Y}` of the linear steady-state system. -/
theorem singletonSourceCoeff_XY (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ X Y = κ.k fwd := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = Network.singletonComplex X then 1 else 0)
    * (κ.k r * N.reactionVector r Y)) = _
  have hne : Network.singletonComplex Y ≠ Network.singletonComplex X :=
    Network.singletonComplex_ne (by decide)
  simp [hne, N, rxn, cX_eq, cY_eq, Network.reactionVector, Network.singletonComplex,
    Fin.sum_univ_two]

/-- The coefficient `c_{Y,X}` of the linear steady-state system. -/
theorem singletonSourceCoeff_YX (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Y X = κ.k bwd := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = Network.singletonComplex Y then 1 else 0)
    * (κ.k r * N.reactionVector r X)) = _
  have hne : Network.singletonComplex X ≠ Network.singletonComplex Y :=
    Network.singletonComplex_ne (by decide)
  simp [hne, N, rxn, cX_eq, cY_eq, Network.reactionVector, Network.singletonComplex,
    Fin.sum_univ_two]

/-- The coefficient `c_{Y,Y}` of the linear steady-state system. -/
theorem singletonSourceCoeff_YY (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Y Y = -(κ.k bwd) := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = Network.singletonComplex Y then 1 else 0)
    * (κ.k r * N.reactionVector r Y)) = _
  have hne : Network.singletonComplex X ≠ Network.singletonComplex Y :=
    Network.singletonComplex_ne (by decide)
  simp [hne, N, rxn, cX_eq, cY_eq, Network.reactionVector, Network.singletonComplex,
    Fin.sum_univ_two]

/-- **The steady states of `X ⇌ Y` are the points with `κ₁ x_X = κ₂ x_Y`.**  This is the
specialisation of the SingletonSource theorem: the steady-state variety of a SingletonSource network is a
linear subspace, here the line through the origin of slope `κ₁/κ₂`. -/
theorem steadyState_iff (κ : Network.RateConstants N) (x : Concentration Species) :
    N.IsMassActionSteadyState κ x ↔ κ.k fwd * x X = κ.k bwd * x Y := by
  rw [Network.singletonSource_steadyState_iff_linear N κ N_singletonSource x]
  constructor
  · intro h
    have hX := h X
    have hY := h Y
    simp only [Fin.sum_univ_two, singletonSourceCoeff_XX, singletonSourceCoeff_YX] at hX
    simp only [Fin.sum_univ_two, singletonSourceCoeff_XY, singletonSourceCoeff_YY] at hY
    linarith
  · intro h
    have hX : (∑ i, N.singletonSourceCoeff κ i X * x i) = 0 := by
      simp only [Fin.sum_univ_two, singletonSourceCoeff_XX, singletonSourceCoeff_YX]
      linarith
    have hY : (∑ i, N.singletonSourceCoeff κ i Y * x i) = 0 := by
      simp only [Fin.sum_univ_two, singletonSourceCoeff_XY, singletonSourceCoeff_YY]
      linarith
    intro s
    fin_cases s
    · exact hX
    · exact hY

/-- The stoichiometric subspace of `X ⇌ Y` is the line spanned by the forward reaction
vector. -/
theorem stoichSubspace_eq :
    N.stoichSubspace = Submodule.span ℝ {N.reactionVector fwd} := by
  have hbwd : N.reactionVector bwd = -N.reactionVector fwd := by
    funext s
    fin_cases s <;> simp [N, rxn, cX, cY, Network.reactionVector]
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro v ⟨r, rfl⟩
    fin_cases r
    · exact Submodule.subset_span rfl
    · show N.reactionVector bwd ∈ _
      rw [hbwd]
      exact Submodule.neg_mem _ (Submodule.subset_span rfl)
  · apply Submodule.span_le.2
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact N.reactionVector_mem_stoichSubspace fwd

/-- Two functions on `Fin 2` that agree at `0` and at `1` are equal. -/
lemma finTwo_ext {f g : Fin 2 → ℝ} (h0 : f 0 = g 0) (h1 : f 1 = g 1) : f = g := by
  funext s
  fin_cases s
  · exact h0
  · exact h1

/-- **The unique positive steady state of `X ⇌ Y` in the class of `c`.**  The
stoichiometric class of `c` meets the steady-state variety in exactly one point, and that
point is positive whenever `c` is.  (So `X ⇌ Y` is not multistationary at all: it has a
unique positive equilibrium in every positive class.) -/
theorem unique_positiveSteadyState_in_class (κ : Network.RateConstants N)
    (h₁ : 0 < κ.k fwd) (h₂ : 0 < κ.k bwd) {c : Concentration Species} (hc : c.Positive) :
    ∃! x : Concentration Species,
      x.Positive ∧ N.IsMassActionSteadyState κ x ∧ (x - c) ∈ N.stoichSubspace := by
  have hsum : 0 < κ.k fwd + κ.k bwd := by linarith
  have hcxy : 0 < c X + c Y := by linarith [hc X, hc Y]
  have hApos : 0 < κ.k bwd * (c X + c Y) / (κ.k fwd + κ.k bwd) :=
    div_pos (mul_pos h₂ hcxy) hsum
  have hBpos : 0 < κ.k fwd * (c X + c Y) / (κ.k fwd + κ.k bwd) :=
    div_pos (mul_pos h₁ hcxy) hsum
  have hAB : κ.k bwd * (c X + c Y) / (κ.k fwd + κ.k bwd)
      + κ.k fwd * (c X + c Y) / (κ.k fwd + κ.k bwd) = c X + c Y := by
    field_simp; ring
  have hbal : κ.k fwd * (κ.k bwd * (c X + c Y) / (κ.k fwd + κ.k bwd))
      = κ.k bwd * (κ.k fwd * (c X + c Y) / (κ.k fwd + κ.k bwd)) := by
    field_simp
  have hne : X ≠ Y := by decide
  -- the candidate equilibrium
  set A : ℝ := κ.k bwd * (c X + c Y) / (κ.k fwd + κ.k bwd) with hA
  set B : ℝ := κ.k fwd * (c X + c Y) / (κ.k fwd + κ.k bwd) with hB
  set x₀ : Concentration Species := fun s => if s = X then A else B with hx₀
  have hx₀X : x₀ X = A := by simp [hx₀]
  have hx₀Y : x₀ Y = B := by simp [hx₀]
  refine ⟨x₀, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro s
      fin_cases s
      · show 0 < x₀ X
        rw [hx₀X]
        exact hApos
      · show 0 < x₀ Y
        rw [hx₀Y]
        exact hBpos
    · refine (steadyState_iff κ x₀).2 ?_
      rw [hx₀X, hx₀Y]
      exact hbal
    · rw [stoichSubspace_eq]
      refine Submodule.mem_span_singleton.mpr ⟨c X - A, ?_⟩
      have hclass : x₀ - c = (c X - A) • N.reactionVector fwd := by
        refine finTwo_ext ?_ ?_
        · show x₀ 0 - c 0 = (c X - A) * N.reactionVector fwd 0
          simp [hx₀, reactionVector_fwd_X]
        · show x₀ 1 - c 1 = (c X - A) * N.reactionVector fwd 1
          simp [hx₀, reactionVector_fwd_Y]
          have h1 : B - c Y = c X - A := by linarith
          linarith
      exact hclass.symm
  · intro x hx
    rcases hx with ⟨hx, hss, hxc⟩
    have hxy : κ.k fwd * x X = κ.k bwd * x Y := (steadyState_iff κ x).mp hss
    rw [stoichSubspace_eq] at hxc
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hxc
    have hX : x X - c X = -a := by
      have h1 := congrFun ha X
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, reactionVector_fwd_X] at h1
      linarith
    have hY : x Y - c Y = a := by
      have h2 := congrFun ha Y
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, reactionVector_fwd_Y] at h2
      linarith
    have ha' : a = (κ.k fwd * c X - κ.k bwd * c Y) / (κ.k fwd + κ.k bwd) := by
      have h1 : x X = c X - a := by linarith
      have h2 : x Y = c Y + a := by linarith
      rw [h1, h2] at hxy
      field_simp; linarith
    have hxX : x X = A := by
      have h1 : x X = c X - a := by linarith
      rw [h1, ha', hA]
      field_simp; ring
    have hxY : x Y = B := by
      have h2 : x Y = c Y + a := by linarith
      rw [h2, ha', hB]
      field_simp; ring
    funext s
    fin_cases s
    · show x 0 = x₀ 0
      rw [hxX, hx₀X, hA]
    · show x 1 = x₀ 1
      rw [hxY, hx₀Y, hB]

/-- The weight vector `(κ₁, −κ₂)`: the annihilator of the steady-state variety of
`X ⇌ Y`. -/
def invariantWeight (κ : Network.RateConstants N) : Concentration Species :=
  fun s => if s = X then κ.k fwd else -(κ.k bwd)

/-- **The weight `(κ₁, −κ₂)` is a steady-state invariant of `X ⇌ Y`.**  It annihilates the
steady-state variety `κ₁ x_X = κ₂ x_Y`, and hence is one of the *conservation laws of the
steady-state variety*. -/
theorem invariantWeight_isSteadyStateInvariant (κ : Network.RateConstants N) :
    Network.IsSteadyStateInvariant N κ (invariantWeight κ) := by
  rw [Network.singletonSource_linearInvariant_iff N κ N_singletonSource]
  intro x hx
  have hxy : κ.k fwd * x X = κ.k bwd * x Y :=
    (steadyState_iff κ x).mp ((Network.singletonSource_steadyState_iff_linear N κ N_singletonSource x).mpr hx)
  simp [invariantWeight]
  linarith

/-- **The weight `(κ₁, −κ₂)` is *not* a conservation law of the network `X ⇌ Y`.**  The two
spaces — the conservation laws of the *network* and the conservation laws of the
*steady-state variety* — are different: the network conserves the total `x_X + x_Y`,
whereas the steady-state variety is preserved by `κ₁ x_X − κ₂ x_Y`. -/
theorem invariantWeight_not_conservationLaw (κ : Network.RateConstants N)
    (h₁ : 0 < κ.k fwd) (h₂ : 0 < κ.k bwd) :
    invariantWeight κ ∉ N.conservationLawSpace := by
  intro hw
  have horth := (mem_orthSum.mp hw) (N.reactionVector fwd) (N.reactionVector_mem_stoichSubspace fwd)
  have hval : (∑ i, invariantWeight κ i * N.reactionVector fwd i) = 0 := by
    simpa using horth
  simp [invariantWeight, reactionVector_fwd_X, reactionVector_fwd_Y] at hval
  linarith

/-- The total concentration `x_X + x_Y` is a conservation law of the network `X ⇌ Y`. -/
theorem totalWeight_isConservationLaw :
    (fun s => if s = X then (1 : ℝ) else 1) ∈ N.conservationLawSpace := by
  rw [Network.mem_conservationLawSpace_iff, Network.IsPInvariant, mem_orthSum]
  refine mem_orthSum_span ?_
  intro g hg
  obtain ⟨r, rfl⟩ := hg
  fin_cases r
  · simp [N, rxn, cX, cY, Network.reactionVector]
  · simp [N, rxn, cX, cY, Network.reactionVector]

/-- **The conservation law `x_X + x_Y` is *not* a steady-state invariant of `X ⇌ Y`.**
The conservation laws of the network and the invariants of the steady-state variety are
two different spaces. -/
theorem totalWeight_not_steadyStateInvariant (κ : Network.RateConstants N)
    (h₁ : 0 < κ.k fwd) (h₂ : 0 < κ.k bwd) :
    ¬ Network.IsSteadyStateInvariant N κ (fun s => if s = X then (1 : ℝ) else 1) := by
  intro hinv
  have h := (Network.singletonSource_linearInvariant_iff N κ N_singletonSource _).mp hinv
  have hx : N.IsMassActionSteadyState κ (fun s => if s = X then κ.k bwd else κ.k fwd) := by
    refine (steadyState_iff κ _).2 ?_
    simp
    ring
  have hlin : ∀ s, ∑ i, Network.singletonSourceCoeff N κ i s
      * (fun s => if s = X then κ.k bwd else κ.k fwd) i = 0 :=
    (Network.singletonSource_steadyState_iff_linear N κ N_singletonSource _).mp hx
  have hval := h _ hlin
  simp at hval
  linarith

/-! ### The chain `X → Y → Z`: more invariants than conservation laws

The chain `X → Y → Z` is a SingletonSource network whose steady-state variety is the line
`{x_X = x_Y = 0}`.  That variety has **two** linear invariants (`w` with `w_Z = 0`),
whereas the network has only **one** conservation law (`w_X = w_Y = w_Z`): here the
steady-state variety really does have *strictly more* invariants than the network has
conservation laws. -/
namespace Chain

/-- The three species of the chain. -/
abbrev Species : Type := Fin 3

/-- The species `X`. -/
abbrev X : Species := 0

/-- The species `Y`. -/
abbrev Y : Species := 1

/-- The species `Z`. -/
abbrev Z : Species := 2

/-- The two channels of the chain. -/
abbrev Rxn : Type := Fin 2

/-- The channel `X → Y`. -/
abbrev r₁ : Rxn := 0

/-- The channel `Y → Z`. -/
abbrev r₂ : Rxn := 1

/-- The complex `X`. -/
def cX : Complex Species := Network.singletonComplex X

/-- The complex `Y`. -/
def cY : Complex Species := Network.singletonComplex Y

/-- The complex `Z`. -/
def cZ : Complex Species := Network.singletonComplex Z

/-- The reaction map of the chain `X → Y → Z`. -/
def rxn : Rxn → Reaction Species :=
  ![{ source := cX, target := cY }, { source := cY, target := cZ }]

/-- The network `X → Y → Z`. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The rate constants of the chain. -/
def rates (k₁ k₂ : ℝ) (h₁ : 0 < k₁) (h₂ : 0 < k₂) : Network.RateConstants N where
  k := ![k₁, k₂]
  positive := by
    intro r
    fin_cases r
    · simpa using h₁
    · simpa using h₂

/-- The source of the first channel is `X`. -/
theorem source_r₁ : (N.reaction r₁).source = cX := rfl

/-- The source of the second channel is `Y`. -/
theorem source_r₂ : (N.reaction r₂).source = cY := rfl

/-- **The chain `X → Y → Z` is a SingletonSource network.** -/
theorem N_singletonSource : N.SingletonSource := by
  intro r
  fin_cases r
  · refine ⟨X, ?_⟩
    show Network.IsSingleton (N.reaction r₁).source X
    rw [source_r₁]
    exact Network.isSingleton_singletonComplex X
  · refine ⟨Y, ?_⟩
    show Network.IsSingleton (N.reaction r₂).source Y
    rw [source_r₂]
    exact Network.isSingleton_singletonComplex Y

/-- The value of the complex `X` at the species `X`. -/
theorem cX_X : cX X = 1 := by simp [cX, Network.singletonComplex]

/-- The value of the complex `X` at the species `Y`. -/
theorem cX_Y : cX Y = 0 := by decide

/-- The value of the complex `X` at the species `Z`. -/
theorem cX_Z : cX Z = 0 := by decide

/-- The value of the complex `Y` at the species `X`. -/
theorem cY_X : cY X = 0 := by decide

/-- The value of the complex `Y` at the species `Y`. -/
theorem cY_Y : cY Y = 1 := by simp [cY, Network.singletonComplex]

/-- The value of the complex `Y` at the species `Z`. -/
theorem cY_Z : cY Z = 0 := by decide

/-- The value of the complex `Z` at the species `X`. -/
theorem cZ_X : cZ X = 0 := by decide

/-- The value of the complex `Z` at the species `Y`. -/
theorem cZ_Y : cZ Y = 0 := by decide

/-- The value of the complex `Z` at the species `Z`. -/
theorem cZ_Z : cZ Z = 1 := by simp [cZ, Network.singletonComplex]

/-- The first reaction vector is `Y − X`. -/
theorem reactionVector_r₁_X : N.reactionVector r₁ X = -1 := by
  simp [N, rxn, Network.reactionVector, Reaction.vector, cY_X, cX_X]

/-- The first reaction vector has entry `1` at `Y`. -/
theorem reactionVector_r₁_Y : N.reactionVector r₁ Y = 1 := by
  simp [N, rxn, Network.reactionVector, Reaction.vector, cY_Y, cX_Y]

/-- The first reaction vector vanishes at `Z`. -/
theorem reactionVector_r₁_Z : N.reactionVector r₁ Z = 0 := by
  simp [N, rxn, Network.reactionVector, Reaction.vector, cY_Z, cX_Z]

/-- The second reaction vector vanishes at `X`. -/
theorem reactionVector_r₂_X : N.reactionVector r₂ X = 0 := by
  simp [N, rxn, Network.reactionVector, Reaction.vector, cZ_X, cY_X]

/-- The second reaction vector is `Z − Y`. -/
theorem reactionVector_r₂_Y : N.reactionVector r₂ Y = -1 := by
  simp [N, rxn, Network.reactionVector, Reaction.vector, cZ_Y, cY_Y]

/-- The second reaction vector has entry `1` at `Z`. -/
theorem reactionVector_r₂_Z : N.reactionVector r₂ Z = 1 := by
  simp [N, rxn, Network.reactionVector, Reaction.vector, cZ_Z, cY_Z]

/-- The complex `X` is the singleton complex at `X`. -/
theorem cX_eq : cX = Network.singletonComplex X := rfl

/-- The complex `Y` is the singleton complex at `Y`. -/
theorem cY_eq : cY = Network.singletonComplex Y := rfl

/-- The complex `Z` is the singleton complex at `Z`. -/
theorem cZ_eq : cZ = Network.singletonComplex Z := rfl

/-- The complexes `X` and `Y` differ. -/
theorem cY_ne_cX : cY ≠ cX := by
  intro h
  rw [cY_eq, cX_eq] at h
  exact absurd (Network.singletonComplex_inj h) (by decide)

/-- The complexes `X` and `Z` differ. -/
theorem cZ_ne_cX : cZ ≠ cX := by
  intro h
  rw [cZ_eq, cX_eq] at h
  exact absurd (Network.singletonComplex_inj h) (by decide)

/-- The complexes `X` and `Y` differ. -/
theorem cX_ne_cY : cX ≠ cY := by
  intro h
  rw [cX_eq, cY_eq] at h
  exact absurd (Network.singletonComplex_inj h) (by decide)

/-- The complexes `Y` and `Z` differ. -/
theorem cZ_ne_cY : cZ ≠ cY := by
  intro h
  rw [cZ_eq, cY_eq] at h
  exact absurd (Network.singletonComplex_inj h) (by decide)

/-- The complexes `X` and `Z` differ. -/
theorem cX_ne_cZ : cX ≠ cZ := by
  intro h
  rw [cX_eq, cZ_eq] at h
  exact absurd (Network.singletonComplex_inj h) (by decide)

/-- The complexes `Y` and `Z` differ. -/
theorem cY_ne_cZ : cY ≠ cZ := by
  intro h
  rw [cY_eq, cZ_eq] at h
  exact absurd (Network.singletonComplex_inj h) (by decide)

/-- The coefficient `c_X,X` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_XX (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ X X = -(κ.k r₁) := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cX then 1 else 0)
    * (κ.k r * N.reactionVector r X)) = _
  simp [cX_X, cY_X, cZ_X, cY_ne_cX, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_X,Y` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_XY (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ X Y = κ.k r₁ := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cX then 1 else 0)
    * (κ.k r * N.reactionVector r Y)) = _
  simp [cX_Y, cY_Y, cZ_Y, cY_ne_cX, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_X,Z` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_XZ (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ X Z = 0 := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cX then 1 else 0)
    * (κ.k r * N.reactionVector r Z)) = _
  simp [cX_Z, cY_Z, cZ_Z, cY_ne_cX, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_Y,X` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_YX (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Y X = 0 := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cY then 1 else 0)
    * (κ.k r * N.reactionVector r X)) = _
  simp [cX_X, cY_X, cZ_X, cX_ne_cY, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_Y,Y` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_YY (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Y Y = -(κ.k r₂) := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cY then 1 else 0)
    * (κ.k r * N.reactionVector r Y)) = _
  simp [cX_Y, cY_Y, cZ_Y, cX_ne_cY, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_Y,Z` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_YZ (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Y Z = κ.k r₂ := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cY then 1 else 0)
    * (κ.k r * N.reactionVector r Z)) = _
  simp [cX_Z, cY_Z, cZ_Z, cX_ne_cY, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_Z,X` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_ZX (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Z X = 0 := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cZ then 1 else 0)
    * (κ.k r * N.reactionVector r X)) = _
  simp [cX_X, cY_X, cZ_X, cX_ne_cZ, cY_ne_cZ, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_Z,Y` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_ZY (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Z Y = 0 := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cZ then 1 else 0)
    * (κ.k r * N.reactionVector r Y)) = _
  simp [cX_Y, cY_Y, cZ_Y, cX_ne_cZ, cY_ne_cZ, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The coefficient `c_Z,Z` of the linear steady-state system of the chain. -/
theorem singletonSourceCoeff_ZZ (κ : Network.RateConstants N) :
    Network.singletonSourceCoeff N κ Z Z = 0 := by
  unfold Network.singletonSourceCoeff Network.singletonSourceIndicator
  change (∑ r : Fin 2, (if (N.reaction r).source = cZ then 1 else 0)
    * (κ.k r * N.reactionVector r Z)) = _
  simp [cX_Z, cY_Z, cZ_Z, cX_ne_cZ, cY_ne_cZ, N, rxn, Network.reactionVector, Reaction.vector,
    Fin.sum_univ_two]

/-- The value of the unit vector at `X` in the species `X`. -/
theorem unitVector_X_X : Network.unitVector X X = 1 := by
  show (if X = X then 1 else 0) = 1
  rw [ite_eq_left rfl]

/-- The value of the unit vector at `X` in the species `Y`. -/
theorem unitVector_X_Y : Network.unitVector X Y = 0 := by
  show (if Y = X then 1 else 0) = 0
  rw [ite_eq_right (by decide : ¬(Y = X))]

/-- The value of the unit vector at `X` in the species `Z`. -/
theorem unitVector_X_Z : Network.unitVector X Z = 0 := by
  show (if Z = X then 1 else 0) = 0
  rw [ite_eq_right (by decide : ¬(Z = X))]

/-- The value of the unit vector at `Y` in the species `X`. -/
theorem unitVector_Y_X : Network.unitVector Y X = 0 := by
  show (if X = Y then 1 else 0) = 0
  rw [ite_eq_right (by decide : ¬(X = Y))]

/-- The value of the unit vector at `Y` in the species `Y`. -/
theorem unitVector_Y_Y : Network.unitVector Y Y = 1 := by
  show (if Y = Y then 1 else 0) = 1
  rw [ite_eq_left rfl]

/-- The value of the unit vector at `Y` in the species `Z`. -/
theorem unitVector_Y_Z : Network.unitVector Y Z = 0 := by
  show (if Z = Y then 1 else 0) = 0
  rw [ite_eq_right (by decide : ¬(Z = Y))]

/-- The value of the unit vector at `Z` in the species `X`. -/
theorem unitVector_Z_X : Network.unitVector Z X = 0 := by
  show (if X = Z then 1 else 0) = 0
  rw [ite_eq_right (by decide : ¬(X = Z))]

/-- The value of the unit vector at `Z` in the species `Y`. -/
theorem unitVector_Z_Y : Network.unitVector Z Y = 0 := by
  show (if Y = Z then 1 else 0) = 0
  rw [ite_eq_right (by decide : ¬(Y = Z))]

/-- The value of the unit vector at `Z` in the species `Z`. -/
theorem unitVector_Z_Z : Network.unitVector Z Z = 1 := by
  show (if Z = Z then 1 else 0) = 1
  rw [ite_eq_left rfl]

/-- **The steady states of the chain `X → Y → Z` are the points with `x_X = x_Y = 0`.**
The variety is a line (the `Z` coordinate is free), and the chain has no positive steady
state at all, as every species is eventually drained. -/
theorem steadyState_iff (κ : Network.RateConstants N) (x : Concentration Species) :
    N.IsMassActionSteadyState κ x ↔ x X = 0 ∧ x Y = 0 := by
  rw [Network.singletonSource_steadyState_iff_linear N κ N_singletonSource x]
  constructor
  · intro h
    have hX := h X
    have hY := h Y
    simp only [Fin.sum_univ_three, singletonSourceCoeff_XX, singletonSourceCoeff_YX, singletonSourceCoeff_ZX] at hX
    simp only [Fin.sum_univ_three, singletonSourceCoeff_XY, singletonSourceCoeff_YY, singletonSourceCoeff_ZY] at hY
    have hpos₁ : 0 < κ.k r₁ := κ.positive r₁
    have hpos₂ : 0 < κ.k r₂ := κ.positive r₂
    have hX0 : x 0 = 0 := by
      have hX' : κ.k r₁ * x 0 = 0 := by linarith
      rcases mul_eq_zero.mp hX' with hk | hk
      · exact absurd hk (ne_of_gt hpos₁)
      · exact hk
    have hY0 : x 1 = 0 := by
      have hY' : κ.k r₂ * x 1 = 0 := by linarith
      rcases mul_eq_zero.mp hY' with hk | hk
      · exact absurd hk (ne_of_gt hpos₂)
      · exact hk
    have hX' : x X = 0 := hX0
    have hY' : x Y = 0 := hY0
    exact ⟨hX', hY'⟩
  · intro h
    have hxX0 : x 0 = 0 := h.1
    have hxY0 : x 1 = 0 := h.2
    intro s
    fin_cases s
    · show (∑ i, Network.singletonSourceCoeff N κ i X * x i) = 0
      simp only [Fin.sum_univ_three, singletonSourceCoeff_XX, singletonSourceCoeff_YX, singletonSourceCoeff_ZX, zero_mul]
      linear_combination (-κ.k r₁) * hxX0
    · show (∑ i, Network.singletonSourceCoeff N κ i Y * x i) = 0
      simp only [Fin.sum_univ_three, singletonSourceCoeff_XY, singletonSourceCoeff_YY, singletonSourceCoeff_ZY, zero_mul]
      linear_combination (κ.k r₁) * hxX0 + (-κ.k r₂) * hxY0
    · show (∑ i, Network.singletonSourceCoeff N κ i Z * x i) = 0
      simp only [Fin.sum_univ_three, singletonSourceCoeff_XZ, singletonSourceCoeff_YZ, singletonSourceCoeff_ZZ, zero_mul]
      linear_combination (κ.k r₂) * hxY0

/-- **The conservation laws of the chain `X → Y → Z` are the vectors with
`w_X = w_Y = w_Z`**: there is exactly one of them (up to scaling). -/
theorem conservationLaw_iff (w : Concentration Species) :
    w ∈ N.conservationLawSpace ↔ w X = w Y ∧ w Y = w Z := by
  rw [Network.mem_conservationLawSpace_iff, Network.IsPInvariant, mem_orthSum]
  constructor
  · intro h
    have h1 := h (N.reactionVector r₁) (N.reactionVector_mem_stoichSubspace r₁)
    have h2 := h (N.reactionVector r₂) (N.reactionVector_mem_stoichSubspace r₂)
    simp only [Fin.sum_univ_three] at h1 h2
    simp only [reactionVector_r₁_X, reactionVector_r₁_Y, reactionVector_r₁_Z] at h1
    simp only [reactionVector_r₂_X, reactionVector_r₂_Y, reactionVector_r₂_Z] at h2
    ring_nf at h1 h2
    constructor
    · linarith
    · linarith
  · intro h
    have h0 : w 0 = w 1 := h.1
    have h1 : w 1 = w 2 := h.2
    refine mem_orthSum_span ?_
    intro g hg
    obtain ⟨r, rfl⟩ := hg
    fin_cases r
    · show (∑ i, w i * N.reactionVector r₁ i) = 0
      simp only [Fin.sum_univ_three]
      simp only [reactionVector_r₁_X, reactionVector_r₁_Y, reactionVector_r₁_Z]
      linarith
    · show (∑ i, w i * N.reactionVector r₂ i) = 0
      simp only [Fin.sum_univ_three]
      simp only [reactionVector_r₂_X, reactionVector_r₂_Y, reactionVector_r₂_Z]
      linarith

/-- **The steady-state invariants of the chain `X → Y → Z` are the vectors with
`w_Z = 0`**: there are two of them (up to scaling), strictly more than the single
conservation law of the network. -/
theorem steadyStateInvariant_iff (κ : Network.RateConstants N) (w : Concentration Species) :
    Network.IsSteadyStateInvariant N κ w ↔ w Z = 0 := by
  rw [Network.singletonSource_linearInvariant_iff N κ N_singletonSource]
  constructor
  · intro h
    have hx : N.IsMassActionSteadyState κ (Network.unitVector Z) := by
      refine (steadyState_iff κ _).2 ⟨?_, ?_⟩
      · simp [unitVector_Z_X]
      · simp [unitVector_Z_Y]
    have hval := h _ ((Network.singletonSource_steadyState_iff_linear N κ N_singletonSource _).mp hx)
    simp only [Fin.sum_univ_three] at hval
    simp only [unitVector_Z_X, unitVector_Z_Y, unitVector_Z_Z] at hval
    have h2 : w 2 = 0 := by linarith
    have h2' : w Z = 0 := h2
    exact h2'
  · intro h x hx
    have hx' : x 0 = 0 ∧ x 1 = 0 := (steadyState_iff κ x).mp
      ((Network.singletonSource_steadyState_iff_linear N κ N_singletonSource x).mpr hx)
    simp only [Fin.sum_univ_three]
    have hz : w 2 = 0 := h
    simp [hx'.1, hx'.2, hz]

/-- **The steady-state variety of the chain has strictly more invariants than the
network has conservation laws**: two of the former, one of the latter.  The two unit
vectors `e_X` and `e_Y` are steady-state invariants (they annihilate the variety
`{x_X = x_Y = 0}`), while neither of them is a conservation law of the network (whose
only conservation law is the total `w_X = w_Y = w_Z`). -/
theorem more_invariants_than_conservationLaws (κ : Network.RateConstants N) :
    (Network.IsSteadyStateInvariant N κ (Network.unitVector X))
      ∧ (Network.IsSteadyStateInvariant N κ (Network.unitVector Y))
      ∧ (Network.unitVector X) ∉ N.conservationLawSpace
      ∧ (Network.unitVector Y) ∉ N.conservationLawSpace := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (steadyStateInvariant_iff κ _).2 ?_
    simp [unitVector_X_Z]
  · refine (steadyStateInvariant_iff κ _).2 ?_
    simp [unitVector_Y_Z]
  · intro h
    rw [conservationLaw_iff] at h
    simp only [unitVector_X_X, unitVector_X_Y, unitVector_X_Z] at h
    linarith
  · intro h
    rw [conservationLaw_iff] at h
    simp only [unitVector_Y_X, unitVector_Y_Y, unitVector_Y_Z] at h
    linarith

end Chain

end Examples.SingletonSource



end CRNT
