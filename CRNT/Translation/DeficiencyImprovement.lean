import CRNT.Translation.ResolvedComplexBalance
import CRNT.Kinetics.GeneralizedDeficiencyZeroExistence
import CRNT.Translation.StructuralInvariants

/-!
# Deficiency-improving network translations

A principal use of network translation is to replace a difficult mass-action realization
by a dynamically equivalent generalized realization whose translated graph is weakly
reversible and has smaller (often zero) structural/kinetic deficiency.  This module
packages the corresponding transfer theorem back to the original CRN.

For an improper translation, the translation map alone does **not** determine generalized
kinetic-complex data.  A certificate therefore carries an actual
`GeneralizedMassActionData` on the translated graph together with a proof that its kinetic
complex at every translated reaction source is the source complex selected by the chosen
`KineticRepresentative`.  Kinetic data at complexes that never occur as reaction sources
are intentionally not fabricated.

`SteadyStateFaithfulOn` explicitly supplies the forward implication from original
steady states to generalized complex balance. The later equivalence consumes
that hypothesis; a general structural criterion deriving it is not proved here.

-/

namespace CRNT
namespace Network
namespace ReactionTranslation

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- A generalized monomial whose kinetic-order vector is the real coercion of an ordinary
complex agrees with the ordinary mass-action monomial on the positive orthant. -/
private theorem kineticMonomial_natCast_eq_massActionMonomial
    {M : Network S} (G : M.GeneralizedMassActionData) (y : Complex S)
    {x : Concentration S} (hx : x.Positive) :
    G.kineticMonomial (fun s => (y s : ℝ)) x = y.massActionMonomial x := by
  have hlog : Real.log (y.massActionMonomial x) =
      ∑ s : S, (y s : ℝ) * Real.log (x s) := by
    unfold Complex.massActionMonomial
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro s _
      exact Real.log_pow (x s) (y s)
    · intro s _
      exact pow_ne_zero _ (hx s).ne'
  unfold GeneralizedMassActionData.kineticMonomial
  rw [← hlog]
  exact Real.exp_log (Complex.massActionMonomial_pos hx y)

/-- A resolved translation certificate whose translated generalized system satisfies the
network-level generalized deficiency-zero hypotheses.

The explicit `generalizedData`/`kineticSource_eq` pair is essential: an improper reaction
translation does not canonically specify kinetic complexes. -/
structure DeficiencyZeroResolution (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (κ : N.RateConstants) where
  generalizedData : T.network.GeneralizedMassActionData
  kineticSource_eq : ∀ r : N.R,
    generalizedData.kineticComplex (T.network.sourceIdx r) =
      (fun s => (K.kineticComplex (T.translatedSourceSubtype r) s : ℝ))
  κhat : N.R → ℝ
  κhat_pos : ∀ r, 0 < κhat r
  resolutionSet : Set (Concentration S)
  resolves : T.ResolvesRatesOn K κ κhat resolutionSet
  translatedWR : T.network.WeaklyReversible
  translatedDeficiencyZero : T.network.deficiency = 0
  kineticDeficiencyZero : generalizedData.kineticDeficiency = 0

/-- Positive resolved rate constants, now typed as rate constants of the translated graph. -/
def DeficiencyZeroResolution.translatedRates
    {T : N.ReactionTranslation} {K : T.KineticRepresentative} {κ : N.RateConstants}
    (H : T.DeficiencyZeroResolution K κ) : T.network.RateConstants where
  k := H.κhat
  positive := H.κhat_pos

/-- At a positive concentration, the actual generalized realization carried by the
certificate has exactly the representative-resolved reaction rates. -/
theorem DeficiencyZeroResolution.generalizedRate_eq_resolvedRate
    {T : N.ReactionTranslation} {K : T.KineticRepresentative} {κ : N.RateConstants}
    (H : T.DeficiencyZeroResolution K κ)
    {x : Concentration S} (hx : x.Positive) (r : N.R) :
    H.generalizedData.generalizedRate H.translatedRates x r =
      T.resolvedRate K H.κhat x r := by
  unfold GeneralizedMassActionData.generalizedRate resolvedRate
  rw [H.kineticSource_eq r]
  rw [kineticMonomial_natCast_eq_massActionMonomial H.generalizedData
    (K.kineticComplex (T.translatedSourceSubtype r)) hx]
  rfl

/-- Complex balance of the explicit generalized datum gives representative-resolved complex
balance.  This is the bridge needed before the existing exact rate-resolution transfer to the
original mass-action system can be used. -/
theorem DeficiencyZeroResolution.isResolvedComplexBalanced_of_generalized
    {T : N.ReactionTranslation} {K : T.KineticRepresentative} {κ : N.RateConstants}
    (H : T.DeficiencyZeroResolution K κ)
    {x : Concentration S} (hx : x.Positive)
    (hcb : H.generalizedData.IsComplexBalanced H.translatedRates x) :
    T.IsResolvedComplexBalanced K H.κhat x := by
  intro c hc
  let ci : T.network.ComplexIdx := ⟨c, hc⟩
  calc
    T.resolvedInflow K H.κhat x c =
        H.generalizedData.inflow H.translatedRates x ci := by
      unfold resolvedInflow GeneralizedMassActionData.inflow
      apply Finset.sum_congr rfl
      intro r _
      by_cases ht : T.target r = c
      · have hti : T.network.targetIdx r = ci := by
          apply Subtype.ext
          exact ht
        simp [ht, hti, H.generalizedRate_eq_resolvedRate hx r]
      · have hti : T.network.targetIdx r ≠ ci := by
          intro h
          apply ht
          exact congrArg Subtype.val h
        simp [ht, hti]
    _ = H.generalizedData.outflow H.translatedRates x ci := hcb ci
    _ = T.resolvedOutflow K H.κhat x c := by
      unfold resolvedOutflow GeneralizedMassActionData.outflow
      apply Finset.sum_congr rfl
      intro r _
      by_cases hs : T.source r = c
      · have hsi : T.network.sourceIdx r = ci := by
          apply Subtype.ext
          exact hs
        simp [hs, hsi, H.generalizedRate_eq_resolvedRate hx r]
      · have hsi : T.network.sourceIdx r ≠ ci := by
          intro h
          apply hs
          exact congrArg Subtype.val h
        simp [hs, hsi]

/-- Any resolved generalized complex-balanced point is an original steady state. -/
theorem originalSteadyState_of_deficiencyZeroResolution
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (H : T.DeficiencyZeroResolution K κ)
    {x : Concentration S} (hx : x ∈ H.resolutionSet)
    (hcb : T.IsResolvedComplexBalanced K H.κhat x) :
    N.IsMassActionSteadyState κ x := by
  exact T.originalSteadyState_of_resolvedComplexBalanced K κ H.κhat H.resolves hx hcb

/-- If generalized deficiency-zero existence produces a translated balanced point inside
an exact resolution set containing the positive compatibility class, then the original
network has a positive steady state in that class. -/
theorem exists_originalSteadyState_via_translation
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (H : T.DeficiencyZeroResolution K κ)
    (hclosure : GeneralizedClosureCondition
      T.network.stoichSubspace H.generalizedData.kineticOrderSubspace)
    (hface : GeneralizedFaceCondition
      T.network.stoichSubspace H.generalizedData.kineticOrderSubspace)
    {x₀ : Concentration S} (hx₀ : x₀.Positive)
    (hclass : N.positiveCompatibilityClass x₀ ⊆ H.resolutionSet)
    (hcompat : T.network.stoichSubspace = N.stoichSubspace) :
    ∃ x ∈ N.positiveCompatibilityClass x₀, N.IsMassActionSteadyState κ x := by
  let HG : H.generalizedData.GeneralizedDeficiencyZeroExistenceHypotheses :=
    { weaklyReversible := H.translatedWR
      kineticDeficiencyZero := H.kineticDeficiencyZero
      closureCondition := hclosure
      faceCondition := hface }
  obtain ⟨x, hxT, hcb⟩ :=
    H.generalizedData.exists_complexBalanced_in_every_positiveClass
      H.translatedRates HG hx₀
  have hxN : x ∈ N.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hxT.2⟩
    change x - x₀ ∈ N.stoichSubspace
    rw [← hcompat]
    exact hxT.1
  have hxres : x ∈ H.resolutionSet := hclass hxN
  have hresolved : T.IsResolvedComplexBalanced K H.κhat x :=
    H.isResolvedComplexBalanced_of_generalized hxT.2 hcb
  exact ⟨x, hxN,
    T.originalSteadyState_of_deficiencyZeroResolution K κ H hxres hresolved⟩

/-- A translated generalized realization is steady-state faithful on `X` when every
original steady state in `X` is also complex-balanced for the explicit translated datum.
The reverse implication on positive points of the resolution set follows from
`isResolvedComplexBalanced_of_generalized` and exact rate resolution. -/
def SteadyStateFaithfulOn
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (H : T.DeficiencyZeroResolution K κ)
    (X : Set (Concentration S)) : Prop :=
  ∀ x ∈ X, N.IsMassActionSteadyState κ x →
    H.generalizedData.IsComplexBalanced H.translatedRates x

/-- On positive points in the resolution set, steady-state faithfulness identifies original
steady states with generalized complex-balanced states of the translated realization. -/
theorem steadyState_iff_generalizedComplexBalanced_of_faithful
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (H : T.DeficiencyZeroResolution K κ)
    {X : Set (Concentration S)}
    (hfaithful : T.SteadyStateFaithfulOn K κ H X)
    {x : Concentration S} (hx : x ∈ X) (hxpos : x.Positive)
    (hxres : x ∈ H.resolutionSet) :
    N.IsMassActionSteadyState κ x ↔
      H.generalizedData.IsComplexBalanced H.translatedRates x := by
  constructor
  · exact hfaithful x hx
  · intro hcb
    have hresolved := H.isResolvedComplexBalanced_of_generalized hxpos hcb
    exact T.originalSteadyState_of_deficiencyZeroResolution K κ H hxres hresolved

/-- With the full generalized uniqueness hypotheses, a steady-state-faithful translated
realization proves monostationarity of the original network in each positive compatibility
class. -/
theorem original_uniqueSteadyState_via_translation
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (H : T.DeficiencyZeroResolution K κ)
    (hclosure : GeneralizedClosureCondition
      T.network.stoichSubspace H.generalizedData.kineticOrderSubspace)
    (hface : GeneralizedFaceCondition
      T.network.stoichSubspace H.generalizedData.kineticOrderSubspace)
    (hsign : SignCompatible T.network.stoichSubspace
      (orthSum H.generalizedData.kineticOrderSubspace))
    {x₀ : Concentration S}
    (hcompat : T.network.stoichSubspace = N.stoichSubspace)
    (hfaithful : T.SteadyStateFaithfulOn K κ H
      (N.positiveCompatibilityClass x₀)) :
    ∀ x y, x ∈ N.positiveCompatibilityClass x₀ → y ∈ N.positiveCompatibilityClass x₀ →
      N.IsMassActionSteadyState κ x → N.IsMassActionSteadyState κ y → x = y := by
  let HU : H.generalizedData.GeneralizedDeficiencyZeroUniquenessHypotheses :=
    { weaklyReversible := H.translatedWR
      kineticDeficiencyZero := H.kineticDeficiencyZero
      closureCondition := hclosure
      faceCondition := hface
      signCompatible := hsign }
  intro x y hx hy hsx hsy
  have hxT : x ∈ T.network.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hx.2⟩
    change x - x₀ ∈ T.network.stoichSubspace
    rw [hcompat]
    exact hx.1
  have hyT : y ∈ T.network.positiveCompatibilityClass x₀ := by
    refine ⟨?_, hy.2⟩
    change y - x₀ ∈ T.network.stoichSubspace
    rw [hcompat]
    exact hy.1
  exact H.generalizedData.unique_complexBalanced_in_positiveClass
    H.translatedRates HU hxT hyT
    (hfaithful x hx hsx) (hfaithful y hy hsy)

end ReactionTranslation
end Network
end CRNT
