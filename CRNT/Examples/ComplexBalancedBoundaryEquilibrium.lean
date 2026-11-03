import Mathlib.Tactic.DeriveFintype
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import CRNT.Basic.Complex
import CRNT.Basic.Reaction
import CRNT.Basic.Network
import CRNT.Kinetics.MassAction
import CRNT.Stoich.Vector
import CRNT.Stoich.Subspace
import CRNT.Dynamics.Siphon
import CRNT.Dynamics.FacetRepulsionAndersonShiu
import CRNT.Graph.Reachability
import CRNT.Graph.WeakReversibility
import CRNT.Graph.LinkageClass
import CRNT.Deficiency.Definition
import CRNT.Theorems.DeficiencyZero.Statement
import CRNT.Theorems.DeficiencyZero.Lyapunov
import CRNT.Equilibria.WegscheiderConverse

/-!
# A complex-balanced boundary equilibrium on a codimension-two face

The Global Attractor residual (`CRNT.Dynamics.HighCodimensionSiphonFace`) asks whether a
positive, bounded, complex-balanced trajectory can have a boundary ω-point whose zero set
`Pmax` is maximal of cardinality ≥ 2 with `finrank (stoichSubspace.map (projOn Pmax)) ≥ 2`.
The module header records that *no static argument can close the residual* — the ω-skeleton
(zero set, maximality, codimension, conservation, stationarity) is consistent with the goal
being false, and only the dynamical content (Craciun v3 Theorem B) carries the proof.  That
claim was previously an `[INFERENCE]` model-consistency argument; this file makes its
network-side core machine-checked on a concrete two-species network:

* `A → A + B`, `A + B → A`, `B → A + B`, `A + B → B` — the mutually-catalytic pair in which
  each species is produced only in the presence of the other and consumed by the other;

* `xstar_isComplexBalanced` — the network is **detailed balanced**, hence complex balanced,
  at the positive concentration `(k₂/k₃, k₀/k₁)` for every positive rate vector (`k₀ k₁ k₂ k₃`):

* `origin_massActionVectorField_eq_zero` — the **origin is an equilibrium**: every source
  complex carries at least one species, so at zero concentration every reaction fires at rate
  zero (no zeroth-order source exists).  A boundary equilibrium of a *complex-balanced*
  network is therefore not a contradiction — complex balance of `xstar` coexists perfectly
  well with a boundary steady state.  What forbids the origin from being the ω-limit set of a
  positive trajectory is dynamics (the origin is a saddle there `[INFERENCE]`, hand-computed
  Jacobian `[[0, k₀],[k₂, 0]]` at the origin, eigenvalues `±√(k₀ k₂)`), not thermodynamics;

* `stoichSubspace_eq_top` — the reaction vectors `e_B` and `e_A` span the whole species space,
  so the origin lies in the stoichiometric compatibility class of **every** point, positive or
  not (`origin_compatible`), and the class meets the open orthant;

* `codim_two`, `stoichRank_ne_one`, `card_univ_two`, `origin_isSiphon` — the static hypotheses
  of the residual at `Pmax = Finset.univ` hold verbatim: `hcodim` (the `Pmax`-projection of the
  stoichiometric subspace has rank 2), `hcard` (2 ≤ Pmax.card), `hrank` (stoichRank ≠ 1),
  `hPmaxne`, `hzeroMax` (the zero set of the origin *is* `Pmax`), and the siphon shape of
  `Pmax`.  The maximality facts `hmaxExact`/`hzcard` are the one-line `ω = {origin}`
  instantiation of `exists_maximal_zeroSet_omegaPoint`'s premises (every point of the
  singleton vanishes exactly on its zero set, and no point of it has a larger zero set) — they
  are statements about a ω-*set*, and the singleton `{origin}` satisfies them on paper; what
  cannot be exhibited, by the very theorem under proof, is a genuine bounded trajectory whose
  ω-limit set *is* that singleton.

* `relEntropy_xstar_origin` — the boundary value of the Lyapunov function there is finite and
  equals the total reference mass `xstar A + xstar B`, the exact content of
  `CRNT.Network.relEntropy_ge_sum_zeroSet` (entropy does not blow up at the boundary; it rises
  by the reference value of each extinct coordinate).

Chemical reading: at the origin both species are extinct and the network is deadlocked —
every reaction channel requires at least one molecule as a catalyst/reactant.  The deadlock
is an equilibrium of the same network that has a positive complex-balanced equilibrium, and
it sits in the compatibility class of every positive start (full stoichiometric rank), so no
conservation law separates it from the interior.  Excluding it from ω-limits of positive
trajectories is exactly the dynamical content of the Global Attractor Conjecture.
-/

namespace CRNT.Examples.ComplexBalancedBoundaryEquilibrium

open CRNT

/-- Two species, `A` and `B`. -/
inductive Species
  | A
  | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by intro s; cases s <;> simp

open Species

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | A => 1 | B => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | A => 0 | B => 1

/-- The complex `A + B`. -/
def cAB : Complex Species := fun s => match s with | A => 1 | B => 1

/-- Four reaction channels: `A → A + B`, `A + B → A`, `B → A + B`, `A + B → B`. -/
inductive Rxn
  | aToAB
  | abToA
  | bToAB
  | abToB
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.aToAB, Rxn.abToA, Rxn.bToAB, Rxn.abToB}
  complete := by intro r; cases r <;> simp

/-- The reaction map. -/
def rxn : Rxn → Reaction Species
  | .aToAB => { source := cA, target := cAB }
  | .abToA => { source := cAB, target := cA }
  | .bToAB => { source := cB, target := cAB }
  | .abToB => { source := cAB, target := cB }

/-- The network `A ⇄ A + B ⇄ …` with the parallel `B` pair. -/
def N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := rxn }

/-- The dead state: both species extinct. -/
def origin : Concentration Species := fun _ => 0

/-- Sums over the two-element species type expand to a single addition. -/
theorem sum_univ_species (f : Species → ℝ) : (∑ s : Species, f s) = f A + f B := by
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_singleton]

/-- Products over the two-element species type expand to a single multiplication. -/
theorem prod_univ_species (f : Species → ℝ) : (∏ s : Species, f s) = f A * f B := by
  have huniv : (Finset.univ : Finset Species) = {A, B} := by decide
  rw [huniv, Finset.prod_insert (by decide), Finset.prod_singleton]

/-! ## Thermodynamics: the network is complex balanced at a positive concentration -/

/-- The pairing `A → A + B` ⇄ `A + B → A` and `B → A + B` ⇄ `A + B → B`. -/
def revStruct : Network.ReversiblePairing N where
  rev := fun r => match r with
    | .aToAB => .abToA
    | .abToA => .aToAB
    | .bToAB => .abToB
    | .abToB => .bToAB
  involutive := by intro r; cases r <;> rfl
  source_rev := by intro r; cases r <;> rfl
  target_rev := by intro r; cases r <;> rfl

/-- Rate constants `k₀ k₁ k₂ k₃` for the four channels, all strictly positive. -/
def rates {k₀ k₁ k₂ k₃ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (h₃ : 0 < k₃) : Network.RateConstants N where
  k := fun r => match r with
    | .aToAB => k₀
    | .abToA => k₁
    | .bToAB => k₂
    | .abToB => k₃
  positive := by intro r; cases r <;> assumption

/-- The positive concentration `(k₂ / k₃, k₀ / k₁)` — reciprocal to the rate constants,
which is the detailed-balance condition for both reversible pairs simultaneously. -/
noncomputable def xstar {k₀ k₁ k₂ k₃ : ℝ} : Concentration Species :=
  fun s => match s with | A => k₂ / k₃ | B => k₀ / k₁

/-- The reference concentration is strictly positive. -/
theorem xstar_positive {k₀ k₁ k₂ k₃ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁) (h₂ : 0 < k₂)
    (h₃ : 0 < k₃) : (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)).Positive := by
  intro s
  cases s
  · exact div_pos h₂ h₃
  · exact div_pos h₀ h₁

/-- **The witness.** On each paired channel the forward flux `k · xstar^source` equals the
reverse flux `k' · xstar^target`: for the `A`-pair `k₀ · xstar_A = k₁ · xstar_A · xstar_B`
reduces to `xstar_B = k₀ / k₁`, and for the `B`-pair `k₂ · xstar_B = k₃ · xstar_A · xstar_B`
reduces to `xstar_A = k₂ / k₃` — both hold by construction of `xstar`. -/
theorem xstar_reactionwiseDetailedBalanced {k₀ k₁ k₂ k₃ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (h₂ : 0 < k₂) (h₃ : 0 < k₃) :
    N.IsReactionwiseDetailedBalanced revStruct (rates h₀ h₁ h₂ h₃)
      (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) := by
  intro r
  cases r <;>
    simp [Network.massActionRate, Complex.massActionMonomial, revStruct, rates, xstar,
      N, rxn, cA, cB, cAB, prod_univ_species] <;>
    field_simp [h₀.ne', h₁.ne', h₂.ne', h₃.ne']

/-- Hence the positive reference is detailed balanced. -/
theorem xstar_isDetailedBalanced {k₀ k₁ k₂ k₃ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (h₂ : 0 < k₂) (h₃ : 0 < k₃) :
    N.IsDetailedBalanced (rates h₀ h₁ h₂ h₃)
      (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) :=
  N.isDetailedBalanced_of_reactionwiseDetailedBalanced revStruct _ _
    (xstar_reactionwiseDetailedBalanced h₀ h₁ h₂ h₃)

/-- **Complex balance.** The network is complex balanced at the positive `xstar` for every
positive rate vector — so the network-side hypothesis `hcb` of the residual holds here. -/
theorem xstar_isComplexBalanced {k₀ k₁ k₂ k₃ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (h₂ : 0 < k₂) (h₃ : 0 < k₃) :
    N.IsComplexBalanced (rates h₀ h₁ h₂ h₃)
      (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) :=
  N.isComplexBalanced_of_isDetailedBalanced _ _ (xstar_isDetailedBalanced h₀ h₁ h₂ h₃)

/-- And `xstar` is a genuine steady state of the mass-action dynamics. -/
theorem xstar_isSteadyState {k₀ k₁ k₂ k₃ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (h₂ : 0 < k₂) (h₃ : 0 < k₃) :
    N.IsMassActionSteadyState (rates h₀ h₁ h₂ h₃)
      (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) :=
  (xstar_isComplexBalanced h₀ h₁ h₂ h₃).isMassActionSteadyState N _

/-! ## The boundary equilibrium -/

/-- The dead state is nonnegative. -/
theorem origin_Nonnegative : Concentration.Nonnegative origin := fun _ => by simp [origin]

/-- Its zero set is the whole species set. -/
theorem origin_zero (s : Species) : origin s = 0 := rfl

/-- Every mass-action rate vanishes at the dead state, for arbitrary rate constants: each
source complex carries at least one species. -/
theorem massActionRate_origin_zero (κ : Network.RateConstants N) (r : Rxn) :
    N.massActionRate κ r origin = 0 := by
  cases r <;>
    simp [Network.massActionRate, Complex.massActionMonomial, origin, N, rxn, cA, cB, cAB,
      prod_univ_species]

/-- **The origin is an equilibrium.** Every source complex (`A`, `B`, `A + B`) carries at
least one species, so every mass-action rate vanishes at the origin and the vector field is
zero: a complex-balanced network *does* admit a boundary steady state. -/
theorem origin_massActionVectorField_eq_zero {k₀ k₁ k₂ k₃ : ℝ} (h₀ : 0 < k₀) (h₁ : 0 < k₁)
    (h₂ : 0 < k₂) (h₃ : 0 < k₃) :
    N.massActionVectorField (rates h₀ h₁ h₂ h₃) origin = 0 := by
  funext s
  rw [Network.massActionVectorField_apply]
  apply Finset.sum_eq_zero
  intro r _
  rw [massActionRate_origin_zero _ r, zero_mul]

/-! ## The geometry: full stoichiometric rank, codimension two at `Pmax = univ` -/

/-- The unit vector on `A`. -/
def eA : Species → ℝ := fun s => match s with | A => 1 | B => 0

/-- The unit vector on `B`. -/
def eB : Species → ℝ := fun s => match s with | A => 0 | B => 1

/-- The `B → A + B` channel moves exactly `+e_A`. -/
theorem reactionVector_bToAB : N.reactionVector .bToAB = eA := by
  funext s
  cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cB, cAB, eA]

/-- The `A → A + B` channel moves exactly `+e_B`. -/
theorem reactionVector_aToAB : N.reactionVector .aToAB = eB := by
  funext s
  cases s <;> simp [Network.reactionVector, N, rxn, Reaction.vector, cA, cAB, eB]

/-- **The stoichiometric subspace is everything.** The reaction vectors `e_A`, `e_B` span
the whole species space, so `stoichSubspace = ⊤` and the compatibility class of the origin
is the entire state space. -/
theorem stoichSubspace_eq_top : N.stoichSubspace = ⊤ := by
  apply le_antisymm
  · exact le_top
  · have heA : eA ∈ N.stoichSubspace := by
      rw [← reactionVector_bToAB]
      exact N.reactionVector_mem_stoichSubspace _
    have heB : eB ∈ N.stoichSubspace := by
      rw [← reactionVector_aToAB]
      exact N.reactionVector_mem_stoichSubspace _
    intro x hx
    have hx : x = x A • eA + x B • eB := by
      funext s
      cases s <;> simp [eA, eB]
    rw [hx]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ heA)
      (Submodule.smul_mem _ _ heB)

/-- **`hrank` of the residual**: the stoichiometric rank is 2, not 1. -/
theorem stoichRank_eq_two : N.stoichRank = 2 := by
  rw [Network.stoichRank, stoichSubspace_eq_top, finrank_top ℝ (Species → ℝ),
    Module.finrank_pi ℝ]
  decide

/-- `hrank`: `N.stoichRank ≠ 1`. -/
theorem stoichRank_ne_one : N.stoichRank ≠ 1 := by
  rw [stoichRank_eq_two]
  omega

/-- `hcard` of the residual: `2 ≤ Pmax.card` for `Pmax = Finset.univ`. -/
theorem card_univ_two : 2 ≤ (Finset.univ : Finset Species).card := by
  rw [show (Finset.univ : Finset Species) = {A, B} by decide,
    Finset.card_insert_of_notMem (by decide), Finset.card_singleton]

/-- `hPmaxne` of the residual: `Pmax = Finset.univ` is nonempty. -/
theorem univ_nonempty : (Finset.univ : Finset Species).Nonempty :=
  ⟨Species.A, Finset.mem_univ _⟩

/-- **`hcodim` of the residual**: the `Pmax`-projection of the stoichiometric subspace has
dimension 2 for `Pmax = Finset.univ` (the projection is the identity, the image is `⊤`). -/
theorem codim_two :
    2 ≤ Module.finrank ℝ (N.stoichSubspace.map (Network.projOn (Finset.univ : Finset Species))) := by
  rw [stoichSubspace_eq_top, Submodule.map_top]
  have hrange : (Network.projOn (Finset.univ : Finset Species)).range = ⊤ := by
    rw [LinearMap.range_eq_top]
    intro p
    exact ⟨p, by funext s; simp⟩
  rw [hrange, finrank_top ℝ (Species → ℝ), Module.finrank_pi ℝ]
  decide

/-- **`hzeroMax` of the residual**: the zero set of the origin is exactly `Pmax =
Finset.univ`. -/
theorem origin_zeroSet : ∀ s, s ∈ (Finset.univ : Finset Species) ↔ origin s = 0 :=
  fun s => by simp [origin]

/-- **`hωaff` of the residual**: the origin lies in the compatibility class of *every*
point — with `stoichSubspace = ⊤` no conservation law separates the dead state from the
interior of any class. -/
theorem origin_compatible (x : Concentration Species) :
    (origin - x : Concentration Species) ∈ N.stoichSubspace := by
  rw [stoichSubspace_eq_top]
  exact Submodule.mem_top

/-- The siphon shape of `Pmax`: every channel that produces a species produces one from a
source that already contains a species (all four sources are nonempty complexes). -/
theorem origin_isSiphon : N.IsSiphon (Finset.univ : Finset Species) := by
  intro r h
  obtain ⟨_, _, _⟩ := h
  cases r with
  | aToAB =>
      exact ⟨Species.A, Finset.mem_univ _, by simp [Network.IsReactant, N, rxn, cA]⟩
  | abToA =>
      exact ⟨Species.A, Finset.mem_univ _, by simp [Network.IsReactant, N, rxn, cAB]⟩
  | bToAB =>
      exact ⟨Species.B, Finset.mem_univ _, by simp [Network.IsReactant, N, rxn, cB]⟩
  | abToB =>
      exact ⟨Species.A, Finset.mem_univ _, by simp [Network.IsReactant, N, rxn, cAB]⟩

/-! ## The Lyapunov function at the dead state -/

/-- **Entropy is finite at the boundary and equals the total reference mass.** Every summand
of `relEntropy xstar origin` is `0 * log 0 - 0 + xstar s = xstar s`, so the value is exactly
`xstar A + xstar B` — the machine-checked form of "no blow-up at zero concentration":
`relEntropy xstar origin = ∑ s ∈ univ, xstar s`, saturating
`CRNT.Network.relEntropy_ge_sum_zeroSet`. -/
theorem relEntropy_xstar_origin {k₀ k₁ k₂ k₃ : ℝ} :
    relEntropy (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) origin
      = xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) A
        + xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃) B := by
  unfold relEntropy
  rw [sum_univ_species]
  simp [origin]

/-- The cap lemma instantiated at the dead state: the extinct set's reference weight is the
*whole* reference mass, and the entropy sits exactly at that value. -/
theorem sum_xstar_univ_eq_relEntropy_origin {k₀ k₁ k₂ k₃ : ℝ} :
    ∑ s ∈ (Finset.univ : Finset Species),
        (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) s
      = relEntropy (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) origin := by
  rw [relEntropy_xstar_origin]
  rw [show ∑ s ∈ (Finset.univ : Finset Species),
      (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) s
      = ∑ s : Species, (xstar (k₀ := k₀) (k₁ := k₁) (k₂ := k₂) (k₃ := k₃)) s by simp]
  rw [sum_univ_species]

end CRNT.Examples.ComplexBalancedBoundaryEquilibrium
