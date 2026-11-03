import CRNT.Basic.Isomorphism
import CRNT.Equilibria.ComplexBalanced
import CRNT.Equilibria.DetailedBalanced
import CRNT.Multistationarity.Capacity

/-!
# Kinetic invariance under CRN isomorphism

A network isomorphism is a pure relabeling.  Transporting rate constants through the
reaction bijection and concentrations through the species bijection therefore conjugates
the mass-action systems exactly.  All structural dynamical properties that only depend on
the reaction system--steady states, complex balance, detailed balance, and
multistationarity--are invariant.
-/

namespace CRNT
namespace Network
namespace Isomorphism

open scoped BigOperators

variable {S T : Type} [DecidableEq S] [Fintype S] [DecidableEq T] [Fintype T]
variable {N : Network S} {M : Network T}

/-- Rename a concentration vector. -/
def mapConcentration (F : N.Isomorphism M) (x : Concentration S) : Concentration T :=
  fun t => x (F.speciesEquiv.symm t)

/-- Inverse concentration renaming. -/
def invConcentration (F : N.Isomorphism M) (y : Concentration T) : Concentration S :=
  fun s => y (F.speciesEquiv s)

@[simp] theorem invConcentration_mapConcentration (F : N.Isomorphism M)
    (x : Concentration S) : F.invConcentration (F.mapConcentration x) = x := by
  funext s
  simp [mapConcentration, invConcentration]

@[simp] theorem mapConcentration_invConcentration (F : N.Isomorphism M)
    (y : Concentration T) : F.mapConcentration (F.invConcentration y) = y := by
  funext t
  simp [mapConcentration, invConcentration]

/-- Positivity is invariant under species renaming. -/
theorem mapConcentration_positive_iff (F : N.Isomorphism M) (x : Concentration S) :
    (F.mapConcentration x).Positive ↔ x.Positive := by
  constructor
  · intro h s
    simpa [mapConcentration] using h (F.speciesEquiv s)
  · intro h t
    exact h (F.speciesEquiv.symm t)

/-- Nonnegativity is invariant under species renaming. -/
theorem mapConcentration_nonnegative_iff (F : N.Isomorphism M) (x : Concentration S) :
    (F.mapConcentration x).Nonnegative ↔ x.Nonnegative := by
  constructor
  · intro h s
    simpa [mapConcentration] using h (F.speciesEquiv s)
  · intro h t
    exact h (F.speciesEquiv.symm t)

/-- Transport positive rate constants through the reaction-channel bijection. -/
def mapRateConstants (F : N.Isomorphism M) (κ : N.RateConstants) : M.RateConstants where
  k := fun q => κ.k (F.reactionEquiv.symm q)
  positive := fun q => κ.positive (F.reactionEquiv.symm q)

@[simp] theorem mapRateConstants_apply (F : N.Isomorphism M) (κ : N.RateConstants)
    (r : N.R) :
    (F.mapRateConstants κ).k (F.reactionEquiv r) = κ.k r := by
  simp [mapRateConstants]

/-- Complex monomials commute with a species permutation. -/
theorem massActionMonomial_rename (F : N.Isomorphism M)
    (y : Complex S) (x : Concentration S) :
    (Complex.rename F.speciesEquiv y).massActionMonomial (F.mapConcentration x) =
      y.massActionMonomial x := by
  unfold Complex.massActionMonomial
  symm
  apply Fintype.prod_equiv F.speciesEquiv
  intro s
  simp [mapConcentration, Complex.rename]

/-- Individual reaction rates are preserved by relabeling. -/
theorem massActionRate_map (F : N.Isomorphism M) (κ : N.RateConstants)
    (x : Concentration S) (r : N.R) :
    M.massActionRate (F.mapRateConstants κ) (F.reactionEquiv r)
        (F.mapConcentration x) =
      N.massActionRate κ r x := by
  simp [massActionRate, F.mapRateConstants_apply, F.map_reaction,
    F.massActionMonomial_rename]

/-- The mass-action vector fields commute exactly with species relabeling. -/
theorem massActionVectorField_map (F : N.Isomorphism M)
    (κ : N.RateConstants) (x : Concentration S) :
    M.massActionVectorField (F.mapRateConstants κ) (F.mapConcentration x) =
      F.mapConcentration (N.massActionVectorField κ x) := by
  funext t
  rw [M.massActionVectorField_apply]
  simp only [mapConcentration]
  rw [N.massActionVectorField_apply]
  symm
  apply Fintype.sum_equiv F.reactionEquiv
  intro r
  rw [← F.massActionRate_map κ x r]
  congr 1
  have hv := congrFun (F.map_reactionVector r) t
  simpa [speciesLinearEquiv] using hv

/-- Steady states are transported bijectively. -/
theorem massActionSteadyState_iff (F : N.Isomorphism M)
    (κ : N.RateConstants) (x : Concentration S) :
    N.IsMassActionSteadyState κ x ↔
      M.IsMassActionSteadyState (F.mapRateConstants κ) (F.mapConcentration x) := by
  constructor
  · intro hx
    unfold IsMassActionSteadyState IsSteadyState at hx ⊢
    intro t
    rw [F.massActionVectorField_map]
    exact hx (F.speciesEquiv.symm t)
  · intro hm
    unfold IsMassActionSteadyState IsSteadyState at hm ⊢
    intro s
    have hs := hm (F.speciesEquiv s)
    rw [F.massActionVectorField_map] at hs
    simpa [mapConcentration] using hs

/-- Stoichiometric compatibility is preserved by network isomorphism. -/
theorem stoichCompatible_iff (F : N.Isomorphism M) (x y : Concentration S) :
    N.StoichCompatible x y ↔
      M.StoichCompatible (F.mapConcentration x) (F.mapConcentration y) := by
  unfold Network.StoichCompatible
  rw [← F.map_stoichSubspace, Submodule.mem_map_equiv]
  have hmap : F.speciesLinearEquiv.symm
      (F.mapConcentration y - F.mapConcentration x) = y - x := by
    funext s
    simp [speciesLinearEquiv, mapConcentration]
  rw [hmap]

/-- Positive compatibility classes correspond bijectively. -/
theorem positiveCompatibilityClass_mem_iff (F : N.Isomorphism M)
    (x₀ x : Concentration S) :
    x ∈ N.positiveCompatibilityClass x₀ ↔
      F.mapConcentration x ∈ M.positiveCompatibilityClass (F.mapConcentration x₀) := by
  simp [positiveCompatibilityClass, F.stoichCompatible_iff,
    F.mapConcentration_positive_iff]

/-- Complex balance is invariant under relabeling. -/
theorem complexBalanced_iff (F : N.Isomorphism M)
    (κ : N.RateConstants) (x : Concentration S) :
    N.IsComplexBalanced κ x ↔
      M.IsComplexBalanced (F.mapRateConstants κ) (F.mapConcentration x) := by
  have hinflow (c : Complex S) :
      M.inflow (F.mapRateConstants κ) (F.mapConcentration x)
          (Complex.rename F.speciesEquiv c) = N.inflow κ x c := by
    unfold Network.inflow
    symm
    apply Fintype.sum_equiv F.reactionEquiv
    intro r
    have ht : (M.reaction (F.reactionEquiv r)).target = Complex.rename F.speciesEquiv c ↔
        (N.reaction r).target = c := by
      rw [F.map_reaction]
      change Complex.rename F.speciesEquiv (N.reaction r).target =
          Complex.rename F.speciesEquiv c ↔ _
      exact (Complex.renameEquiv F.speciesEquiv).injective.eq_iff
    by_cases hrc : (N.reaction r).target = c
    · simp [hrc, ht, F.massActionRate_map]
    · simp [hrc, ht]
  have houtflow (c : Complex S) :
      M.outflow (F.mapRateConstants κ) (F.mapConcentration x)
          (Complex.rename F.speciesEquiv c) = N.outflow κ x c := by
    unfold Network.outflow
    symm
    apply Fintype.sum_equiv F.reactionEquiv
    intro r
    have hs : (M.reaction (F.reactionEquiv r)).source = Complex.rename F.speciesEquiv c ↔
        (N.reaction r).source = c := by
      rw [F.map_reaction]
      change Complex.rename F.speciesEquiv (N.reaction r).source =
          Complex.rename F.speciesEquiv c ↔ _
      exact (Complex.renameEquiv F.speciesEquiv).injective.eq_iff
    by_cases hrc : (N.reaction r).source = c
    · simp [hrc, hs, F.massActionRate_map]
    · simp [hrc, hs]
  constructor
  · intro h c hc
    let d : Complex S := Complex.rename F.speciesEquiv.symm c
    have hd : Complex.rename F.speciesEquiv d = c := by
      ext t
      simp [d, Complex.rename]
    rw [← hd, hinflow d, houtflow d]
    apply h d
    exact (F.complex_mem_iff d).2 (by simpa [hd] using hc)
  · intro h c hc
    have hm := h (Complex.rename F.speciesEquiv c) ((F.complex_mem_iff c).1 hc)
    rw [hinflow c, houtflow c] at hm
    exact hm

/-- Aggregate detailed balance is invariant under relabeling. -/
theorem detailedBalanced_iff (F : N.Isomorphism M)
    (κ : N.RateConstants) (x : Concentration S) :
    N.IsDetailedBalanced κ x ↔
      M.IsDetailedBalanced (F.mapRateConstants κ) (F.mapConcentration x) := by
  have hpair (c d : Complex S) :
      M.pairFlux (F.mapRateConstants κ) (F.mapConcentration x)
          (Complex.rename F.speciesEquiv c) (Complex.rename F.speciesEquiv d) =
        N.pairFlux κ x c d := by
    unfold Network.pairFlux
    symm
    apply Fintype.sum_equiv F.reactionEquiv
    intro r
    have hs : (M.reaction (F.reactionEquiv r)).source = Complex.rename F.speciesEquiv c ↔
        (N.reaction r).source = c := by
      rw [F.map_reaction]
      change Complex.rename F.speciesEquiv (N.reaction r).source =
          Complex.rename F.speciesEquiv c ↔ _
      exact (Complex.renameEquiv F.speciesEquiv).injective.eq_iff
    have ht : (M.reaction (F.reactionEquiv r)).target = Complex.rename F.speciesEquiv d ↔
        (N.reaction r).target = d := by
      rw [F.map_reaction]
      change Complex.rename F.speciesEquiv (N.reaction r).target =
          Complex.rename F.speciesEquiv d ↔ _
      exact (Complex.renameEquiv F.speciesEquiv).injective.eq_iff
    by_cases hrc : (N.reaction r).source = c ∧ (N.reaction r).target = d
    · simp [hrc, hs, ht, F.massActionRate_map]
    · simp [hrc, hs, ht]
  constructor
  · intro h c hc d hd
    let c₀ : Complex S := Complex.rename F.speciesEquiv.symm c
    let d₀ : Complex S := Complex.rename F.speciesEquiv.symm d
    have hc₀ : Complex.rename F.speciesEquiv c₀ = c := by
      ext t
      simp [c₀, Complex.rename]
    have hd₀ : Complex.rename F.speciesEquiv d₀ = d := by
      ext t
      simp [d₀, Complex.rename]
    rw [← hc₀, ← hd₀, hpair c₀ d₀, hpair d₀ c₀]
    apply h c₀
    · exact (F.complex_mem_iff c₀).2 (by simpa [hc₀] using hc)
    · exact (F.complex_mem_iff d₀).2 (by simpa [hd₀] using hd)
  · intro h c hc d hd
    have hm := h (Complex.rename F.speciesEquiv c) ((F.complex_mem_iff c).1 hc)
      (Complex.rename F.speciesEquiv d) ((F.complex_mem_iff d).1 hd)
    rw [hpair c d, hpair d c] at hm
    exact hm

/-- Two distinct compatible positive steady states transport to two distinct compatible
positive steady states. -/
theorem map_multistationary_pair (F : N.Isomorphism M)
    (κ : N.RateConstants) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive)
    (hxy : N.StoichCompatible x y)
    (hssx : N.IsMassActionSteadyState κ x)
    (hssy : N.IsMassActionSteadyState κ y)
    (hne : x ≠ y) :
    (F.mapConcentration x).Positive ∧
    (F.mapConcentration y).Positive ∧
    M.StoichCompatible (F.mapConcentration x) (F.mapConcentration y) ∧
    M.IsMassActionSteadyState (F.mapRateConstants κ) (F.mapConcentration x) ∧
    M.IsMassActionSteadyState (F.mapRateConstants κ) (F.mapConcentration y) ∧
    F.mapConcentration x ≠ F.mapConcentration y := by
  refine ⟨(F.mapConcentration_positive_iff x).2 hx,
    (F.mapConcentration_positive_iff y).2 hy,
    (F.stoichCompatible_iff x y).1 hxy,
    (F.massActionSteadyState_iff κ x).1 hssx,
    (F.massActionSteadyState_iff κ y).1 hssy, ?_⟩
  intro hmap
  apply hne
  -- `simpa [← ...]` loops: the reversed rewrites keep re-expanding `x` and `y`.
  -- Rewrite forwards in the hypothesis instead.
  have hinv := congrArg F.invConcentration hmap
  rwa [F.invConcentration_mapConcentration x,
    F.invConcentration_mapConcentration y] at hinv

end Isomorphism
end Network
end CRNT
