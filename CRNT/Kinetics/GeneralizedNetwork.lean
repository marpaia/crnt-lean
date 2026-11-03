import CRNT.Decision.Linkage
import CRNT.Kinetics.Generalized
import CRNT.Deficiency.KernelDimension
import CRNT.Equilibria.CompatibilityClass
import Mathlib.Analysis.SpecialFunctions.Exp
import CRNT.Deficiency.DeficiencyOne

/-!
# Generalized mass-action reaction networks

A generalized mass-action system carries two complex embeddings on the same reaction
graph:

* the ordinary stoichiometric complex `Y_c`, and
* a real kinetic-order complex `Y~_c`.

The graph incidence map composed with these embeddings gives respectively the
stoichiometric and kinetic-order reaction maps.  Their ranks yield the stoichiometric
and kinetic-order deficiencies used in Müller--Regensburger theory.
-/

namespace CRNT
namespace Network

open scoped Matrix BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A real kinetic-order complex. -/
abbrev KineticComplex (S : Type) := S → ℝ

/-- Generalized mass-action data on a fixed CRN graph. -/
structure GeneralizedMassActionData (N : Network S) where
  kineticComplex : N.ComplexIdx → KineticComplex S

namespace GeneralizedMassActionData

variable {N : Network S}

/-- Linear map sending formal complex coefficients to the corresponding linear
combination of kinetic-order complexes. -/
noncomputable def kineticComplexMap (G : N.GeneralizedMassActionData) :
    (N.ComplexIdx → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := fun a s => ∑ c : N.ComplexIdx, a c * G.kineticComplex c s
  map_add' := by intros; ext s; simp [Finset.sum_add_distrib, add_mul]
  map_smul' := by intros; ext s; simp [Finset.mul_sum, mul_assoc]

/-- Kinetic-order reaction map `Y~ ∘ I`. -/
noncomputable def kineticOrderMap (G : N.GeneralizedMassActionData) :
    (N.R → ℝ) →ₗ[ℝ] (S → ℝ) :=
  G.kineticComplexMap.comp N.incidenceMap

/-- Matrix of kinetic-order complexes, with species as rows and complexes as columns. -/
noncomputable def kineticComplexMatrix (G : N.GeneralizedMassActionData) :
    Matrix S N.ComplexIdx ℝ :=
  fun s c => G.kineticComplex c s

/-- The kinetic-complex linear map is matrix multiplication by `kineticComplexMatrix`. -/
theorem kineticComplexMap_eq_mulVecLin (G : N.GeneralizedMassActionData) :
    G.kineticComplexMap = G.kineticComplexMatrix.mulVecLin := by
  apply LinearMap.ext
  intro v
  funext s
  rw [Matrix.mulVecLin_apply]
  simp only [Matrix.mulVec, dotProduct, kineticComplexMatrix, kineticComplexMap]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- Generalized kinetic-order reaction matrix `Y~ · ∂`. -/
noncomputable def kineticOrderMatrix (G : N.GeneralizedMassActionData) :
    Matrix S N.R ℝ :=
  G.kineticComplexMatrix * N.incidenceMatrix

/-- Matrix realization of the kinetic-order reaction map. -/
theorem kineticOrderMatrix_mulVecLin (G : N.GeneralizedMassActionData) :
    G.kineticOrderMatrix.mulVecLin = G.kineticOrderMap := by
  rw [kineticOrderMatrix, Matrix.mulVecLin_mul, ← kineticComplexMap_eq_mulVecLin,
    ← N.incidenceMap_eq_mulVecLin]
  rfl

/-- Coordinate formula for the transpose kinetic-order reaction matrix. -/
theorem kineticOrderTranspose_apply (G : N.GeneralizedMassActionData)
    (p : S → ℝ) (r : N.R) :
    G.kineticOrderMatrixᵀ.mulVecLin p r =
      ∑ s : S, (G.kineticComplex (N.targetIdx r) s -
        G.kineticComplex (N.sourceIdx r) s) * p s := by
  have hT : G.kineticOrderMatrixᵀ = N.incidenceMatrixᵀ * G.kineticComplexMatrixᵀ := by
    rw [kineticOrderMatrix, Matrix.transpose_mul]
  rw [hT, Matrix.mulVecLin_mul, LinearMap.comp_apply, N.incidenceTranspose_apply]
  change (∑ s : S, G.kineticComplex (N.targetIdx r) s * p s) -
      (∑ s : S, G.kineticComplex (N.sourceIdx r) s * p s) = _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- Coordinate expansion of the kinetic-order reaction map. -/
theorem kineticOrderMap_apply (G : N.GeneralizedMassActionData)
    (a : N.R → ℝ) (s : S) :
    G.kineticOrderMap a s =
      ∑ r : N.R, a r *
        (G.kineticComplex (N.targetIdx r) s -
          G.kineticComplex (N.sourceIdx r) s) := by
  unfold kineticOrderMap
  change (∑ c : N.ComplexIdx, N.incidenceMap a c * G.kineticComplex c s) = _
  simp only [N.incidenceMap_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hexpand : ∀ c : N.ComplexIdx,
      a r * ((if N.targetIdx r = c then (1 : ℝ) else 0) -
        (if N.sourceIdx r = c then 1 else 0)) * G.kineticComplex c s =
      a r * ((if N.targetIdx r = c then (1 : ℝ) else 0) * G.kineticComplex c s -
        (if N.sourceIdx r = c then (1 : ℝ) else 0) * G.kineticComplex c s) :=
    fun c => by ring
  simp only [hexpand]
  rw [← Finset.mul_sum, Finset.sum_sub_distrib]
  have ht :
      (∑ c : N.ComplexIdx,
        (if N.targetIdx r = c then (1 : ℝ) else 0) * G.kineticComplex c s) =
        G.kineticComplex (N.targetIdx r) s := by
    rw [Finset.sum_eq_single (N.targetIdx r)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  have hs :
      (∑ c : N.ComplexIdx,
        (if N.sourceIdx r = c then (1 : ℝ) else 0) * G.kineticComplex c s) =
        G.kineticComplex (N.sourceIdx r) s := by
    rw [Finset.sum_eq_single (N.sourceIdx r)]
    · simp
    · intro c _ hc
      simp [Ne.symm hc]
    · simp
  rw [ht, hs]

/-- Kinetic-order subspace. -/
noncomputable def kineticOrderSubspace (G : N.GeneralizedMassActionData) :
    Submodule ℝ (S → ℝ) :=
  LinearMap.range G.kineticOrderMap

/-- Every kinetic-order reaction difference belongs to the kinetic-order subspace. -/
theorem kineticOrderReaction_mem_subspace (G : N.GeneralizedMassActionData) (r : N.R) :
    (fun s => G.kineticComplex (N.targetIdx r) s -
      G.kineticComplex (N.sourceIdx r) s) ∈ G.kineticOrderSubspace := by
  refine ⟨Pi.single r 1, ?_⟩
  funext s
  rw [G.kineticOrderMap_apply]
  rw [Finset.sum_eq_single r]
  · simp
  · intro r' _ hr'
    simp [Pi.single, hr']
  · simp

/-- Kinetic complexes of linked stoichiometric complexes differ by a vector in the
kinetic-order subspace.  This is the path-telescoping bridge used by generalized toric
complex-balance geometry. -/
theorem kineticComplex_sub_mem_of_linked
    (G : N.GeneralizedMassActionData) {i j : N.ComplexIdx}
    (hij : N.Linked i.1 j.1) :
    (fun s => G.kineticComplex j s - G.kineticComplex i s) ∈ G.kineticOrderSubspace := by
  have hprop : ∀ {a b : N.ComplexIdx},
      Relation.ReflTransGen N.linkageGraph.Adj a b →
      (fun s => G.kineticComplex b s - G.kineticComplex a s) ∈ G.kineticOrderSubspace := by
    intro a b h
    induction h using Relation.ReflTransGen.trans_induction_on with
    | refl a =>
        have hz : (fun s => G.kineticComplex a s - G.kineticComplex a s) = (0 : S → ℝ) := by
          funext s
          simp
        rw [hz]
        exact G.kineticOrderSubspace.zero_mem
    | @single a b hab =>
        rcases hab.2 with hab | hab
        · rcases hab with ⟨r, hs, ht⟩
          have hr := G.kineticOrderReaction_mem_subspace r
          have hsrc : N.sourceIdx r = a := by
            apply Subtype.ext
            exact hs
          have htgt : N.targetIdx r = b := by
            apply Subtype.ext
            exact ht
          simpa [hsrc, htgt] using hr
        · rcases hab with ⟨r, hs, ht⟩
          have hr := G.kineticOrderReaction_mem_subspace r
          have hneg := G.kineticOrderSubspace.neg_mem hr
          have hsrc : N.sourceIdx r = b := by
            apply Subtype.ext
            exact hs
          have htgt : N.targetIdx r = a := by
            apply Subtype.ext
            exact ht
          have heq :
              (fun s => G.kineticComplex b s - G.kineticComplex a s) =
                -(fun s => G.kineticComplex a s - G.kineticComplex b s) := by
            funext s
            simp
          rw [heq]
          simpa [hsrc, htgt] using hneg
    | @trans a b c hab hbc ihab ihbc =>
        have hsum := G.kineticOrderSubspace.add_mem ihab ihbc
        have heq :
            (fun s => G.kineticComplex c s - G.kineticComplex a s) =
              (fun s => G.kineticComplex b s - G.kineticComplex a s) +
              (fun s => G.kineticComplex c s - G.kineticComplex b s) := by
          funext s
          simp only [Pi.add_apply]
          ring
        rw [heq]
        exact hsum
  exact hprop (N.reflTransGen_adj_of_linked hij i.2 j.2)

/-- Kinetic-order rank `s~`. -/
noncomputable def kineticOrderRank (G : N.GeneralizedMassActionData) : ℕ :=
  Module.finrank ℝ G.kineticOrderSubspace

/-- The kinetic-order rank cannot exceed incidence rank. -/
theorem kineticOrderRank_le_incidenceRank (G : N.GeneralizedMassActionData) :
    G.kineticOrderRank ≤ N.incidenceRank := by
  unfold kineticOrderRank kineticOrderSubspace kineticOrderMap Network.incidenceRank
  rw [LinearMap.range_comp]
  exact Submodule.finrank_map_le G.kineticComplexMap (LinearMap.range N.incidenceMap)

/-- Kinetic-order deficiency `δ~ = n - ℓ - s~ = rank(I) - rank(Y~ I)`. -/
noncomputable def kineticDeficiency (G : N.GeneralizedMassActionData) : ℕ :=
  N.incidenceRank - G.kineticOrderRank

/-- Rank form of the kinetic-order deficiency. -/
theorem incidenceRank_eq_kineticOrderRank_add_kineticDeficiency
    (G : N.GeneralizedMassActionData) :
    N.incidenceRank = G.kineticOrderRank + G.kineticDeficiency := by
  unfold kineticDeficiency
  have hle := G.kineticOrderRank_le_incidenceRank
  omega

/-- Both deficiency numbers vanish. -/
def BothDeficienciesZero (G : N.GeneralizedMassActionData) : Prop :=
  N.deficiency = 0 ∧ G.kineticDeficiency = 0

/-- Positive generalized monomial `x^α := exp(<α, log x>)`.  This definition supports
arbitrary real kinetic orders while agreeing with ordinary mass action for natural
complexes. -/
noncomputable def kineticMonomial (G : N.GeneralizedMassActionData)
    (α : KineticComplex S) (x : Concentration S) : ℝ :=
  Real.exp (∑ s : S, α s * Real.log (x s))

/-- Generalized mass-action reaction rate. -/
noncomputable def generalizedRate (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) (r : N.R) : ℝ :=
  κ.k r * G.kineticMonomial (G.kineticComplex (N.sourceIdx r)) x

/-- Generalized mass-action vector field. -/
noncomputable def vectorField (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) : S → ℝ :=
  fun s => ∑ r : N.R, G.generalizedRate κ x r * N.reactionVector r s

/-- Positive generalized monomials. -/
theorem kineticMonomial_pos (G : N.GeneralizedMassActionData)
    (α : KineticComplex S) (x : Concentration S) : 0 < G.kineticMonomial α x := by
  exact Real.exp_pos _

/-- Generalized inflow into a stoichiometric complex. -/
noncomputable def inflow (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) (c : N.ComplexIdx) : ℝ :=
  ∑ r : N.R, if N.targetIdx r = c then G.generalizedRate κ x r else 0

/-- Generalized outflow from a stoichiometric complex. -/
noncomputable def outflow (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) (c : N.ComplexIdx) : ℝ :=
  ∑ r : N.R, if N.sourceIdx r = c then G.generalizedRate κ x r else 0

/-- Generalized complex balance. -/
def IsComplexBalanced (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) : Prop :=
  ∀ c : N.ComplexIdx, G.inflow κ x c = G.outflow κ x c

/-- Generalized steady state. -/
def IsSteadyState (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) : Prop :=
  G.vectorField κ x = 0

/-- Complex balance implies steady state for generalized mass action just as in ordinary
mass action. -/
theorem isSteadyState_of_complexBalanced (G : N.GeneralizedMassActionData)
    (κ : N.RateConstants) (x : Concentration S)
    (hcb : G.IsComplexBalanced κ x) : G.IsSteadyState κ x := by
  let v : N.R → ℝ := fun r => G.generalizedRate κ x r
  have hinc : N.incidenceMap v = 0 := by
    funext c
    have hc := hcb c
    unfold inflow outflow at hc
    rw [N.incidenceMap_apply]
    change (∑ r : N.R, G.generalizedRate κ x r *
      ((if N.targetIdx r = c then 1 else 0) -
       (if N.sourceIdx r = c then 1 else 0))) = (0 : ℝ)
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    have heq :
        (∑ r : N.R, G.generalizedRate κ x r *
          (if N.targetIdx r = c then 1 else 0)) = G.inflow κ x c := by
      unfold inflow
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : N.targetIdx r = c <;> simp [hr]
    have heq' :
        (∑ r : N.R, G.generalizedRate κ x r *
          (if N.sourceIdx r = c then 1 else 0)) = G.outflow κ x c := by
      unfold outflow
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : N.sourceIdx r = c <;> simp [hr]
    rw [heq, heq']
    exact sub_eq_zero.mpr (hcb c)
  have hstoich : N.stoichMap v = 0 := by
    rw [← N.complexMap_comp_incidenceMap]
    change N.complexMap (N.incidenceMap v) = 0
    rw [hinc]
    exact map_zero N.complexMap
  unfold IsSteadyState
  rw [show G.vectorField κ x = N.stoichMap v by
    funext s
    simp [vectorField, N.stoichMap_apply, v]]
  exact hstoich

/-- Classical kinetic-order data: the kinetic complex equals the ordinary stoichiometric
complex. -/
noncomputable def classical (N : Network S) : N.GeneralizedMassActionData where
  kineticComplex := fun c s => (c.val s : ℝ)

/-- Classical kinetic-order map coincides with the ordinary stoichiometric map. -/
theorem classical_kineticOrderMap_eq_stoichMap (N : Network S) :
    (GeneralizedMassActionData.classical N).kineticOrderMap = N.stoichMap := by
  rw [← N.complexMap_comp_incidenceMap]
  apply LinearMap.ext
  intro v
  funext s
  rfl

/-- Hence classical and kinetic-order subspaces coincide. -/
theorem classical_kineticOrderSubspace_eq_stoichSubspace (N : Network S) :
    (GeneralizedMassActionData.classical N).kineticOrderSubspace = N.stoichSubspace := by
  unfold kineticOrderSubspace
  rw [classical_kineticOrderMap_eq_stoichMap N, N.range_stoichMap]

/-- Classical kinetic-order deficiency is the ordinary CRNT deficiency. -/
theorem classical_kineticDeficiency_eq_deficiency (N : Network S) :
    (GeneralizedMassActionData.classical N).kineticDeficiency = N.deficiency := by
  unfold kineticDeficiency kineticOrderRank
  rw [classical_kineticOrderSubspace_eq_stoichSubspace N]
  have h := N.incidenceRank_eq_stoichRank_add
  change N.incidenceRank - N.stoichRank = N.deficiency
  unfold Network.deficiency at *
  omega

/-- Classical generalized monomial agrees with the ordinary complex monomial at positive
concentrations. -/
theorem classical_kineticMonomial_eq_massActionMonomial
    (N : Network S) (c : N.ComplexIdx) {x : Concentration S} (hx : x.Positive) :
    (GeneralizedMassActionData.classical N).kineticMonomial
      ((GeneralizedMassActionData.classical N).kineticComplex c) x =
      c.val.massActionMonomial x := by
  have hlog : Real.log (c.val.massActionMonomial x) =
      ∑ s : S, (c.val s : ℝ) * Real.log (x s) := by
    unfold Complex.massActionMonomial
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro s _
      exact Real.log_pow (x s) (c.val s)
    · intro s _
      exact pow_ne_zero _ (hx s).ne'
  unfold kineticMonomial classical
  rw [← hlog]
  exact Real.exp_log (Complex.massActionMonomial_pos hx c.val)

end GeneralizedMassActionData
end Network
end CRNT
