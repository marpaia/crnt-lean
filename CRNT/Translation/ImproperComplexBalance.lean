import CRNT.Translation.Improper
import CRNT.Translation.ComplexBalance

/-!
# Complex-balanced improper translations

An improper translation merges distinct original source complexes.  After choosing one
kinetic representative per translated source, a fixed positive adjusted rate vector gives a
generalized mass-action realization on the translated graph.  If the adjusted rates resolve
the original reaction rates on a set `X`, generalized complex balance of that representative
realization at any `x ∈ X` implies that `x` is a steady state of the original mass-action
system.

This is the precise steady-state transfer theorem used by improper network translations.
-/

namespace CRNT
namespace Network
namespace ReactionTranslation

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Generalized rate using one kinetic representative per translated source. -/
def representativeRate (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (κhat : N.R → ℝ)
    (x : Concentration S) (r : N.R) : ℝ :=
  κhat r *
    (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x

/-- Representative-kinetic inflow at a translated complex. -/
def representativeInflow (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (κhat : N.R → ℝ)
    (x : Concentration S) (c : Complex S) : ℝ :=
  ∑ r : N.R, if T.target r = c then T.representativeRate K κhat x r else 0

/-- Representative-kinetic outflow at a translated complex. -/
def representativeOutflow (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (κhat : N.R → ℝ)
    (x : Concentration S) (c : Complex S) : ℝ :=
  ∑ r : N.R, if T.source r = c then T.representativeRate K κhat x r else 0

/-- Complex balance of the generalized representative realization. -/
def IsRepresentativeComplexBalanced (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (κhat : N.R → ℝ)
    (x : Concentration S) : Prop :=
  ∀ c ∈ T.network.complexes,
    T.representativeInflow K κhat x c =
      T.representativeOutflow K κhat x c

/-- Pointwise rate resolution identifies every representative reaction rate with the
original mass-action reaction rate. -/
theorem representativeRate_eq_original_of_resolvesRatesOn
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ)
    {X : Set (Concentration S)}
    (hres : T.ResolvesRatesOn K κ κhat X)
    {x : Concentration S} (hx : x ∈ X) (r : N.R) :
    T.representativeRate K κhat x r = N.massActionRate κ r x := by
  exact hres x hx r

/-- On a resolved set, representative complex balance is identical to translated
generalized complex balance using the original source monomials. -/
theorem representativeComplexBalanced_iff_generalizedComplexBalanced
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ)
    {X : Set (Concentration S)}
    (hres : T.ResolvesRatesOn K κ κhat X)
    {x : Concentration S} (hx : x ∈ X) :
    T.IsRepresentativeComplexBalanced K κhat x ↔
      T.IsGeneralizedComplexBalanced κ x := by
  have hrate : ∀ r : N.R,
      T.representativeRate K κhat x r = N.generalizedRate T κ x r := by
    intro r
    exact hres x hx r
  constructor
  · intro hcb c hc
    have hin : T.representativeInflow K κhat x c = N.generalizedInflow T κ x c := by
      unfold representativeInflow Network.generalizedInflow
      apply Finset.sum_congr rfl
      intro r hr
      change (if T.target r = c then T.representativeRate K κhat x r else 0) =
        (if T.target r = c then N.generalizedRate T κ x r else 0)
      by_cases ht : T.target r = c <;> simp [ht, hrate r]
    have hout : T.representativeOutflow K κhat x c = N.generalizedOutflow T κ x c := by
      unfold representativeOutflow Network.generalizedOutflow
      apply Finset.sum_congr rfl
      intro r hr
      change (if T.source r = c then T.representativeRate K κhat x r else 0) =
        (if T.source r = c then N.generalizedRate T κ x r else 0)
      by_cases hs : T.source r = c <;> simp [hs, hrate r]
    rw [← hin, ← hout]
    exact hcb c hc
  · intro hcb c hc
    have hin : T.representativeInflow K κhat x c = N.generalizedInflow T κ x c := by
      unfold representativeInflow Network.generalizedInflow
      apply Finset.sum_congr rfl
      intro r hr
      change (if T.target r = c then T.representativeRate K κhat x r else 0) =
        (if T.target r = c then N.generalizedRate T κ x r else 0)
      by_cases ht : T.target r = c <;> simp [ht, hrate r]
    have hout : T.representativeOutflow K κhat x c = N.generalizedOutflow T κ x c := by
      unfold representativeOutflow Network.generalizedOutflow
      apply Finset.sum_congr rfl
      intro r hr
      change (if T.source r = c then T.representativeRate K κhat x r else 0) =
        (if T.source r = c then N.generalizedRate T κ x r else 0)
      by_cases hs : T.source r = c <;> simp [hs, hrate r]
    rw [hin, hout]
    exact hcb c hc

/-- **Improper translation steady-state transfer.** -/
theorem original_steadyState_of_resolved_representativeComplexBalanced
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ)
    {X : Set (Concentration S)}
    (hres : T.ResolvesRatesOn K κ κhat X)
    {x : Concentration S} (hx : x ∈ X)
    (hcb : T.IsRepresentativeComplexBalanced K κhat x) :
    N.IsMassActionSteadyState κ x := by
  apply T.original_isMassActionSteadyState_of_generalizedComplexBalanced κ x
  exact (T.representativeComplexBalanced_iff_generalizedComplexBalanced
    K κ κhat hres hx).1 hcb

/-- Strong resolvability packages a positive adjusted rate vector usable simultaneously
throughout the set. -/
theorem exists_fixed_representative_rates_of_stronglyResolvableOn
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) {X : Set (Concentration S)}
    (h : T.StronglyResolvableOn K κ X) :
    ∃ κhat : N.R → ℝ,
      (∀ r, 0 < κhat r) ∧
      ∀ x ∈ X,
        (T.IsRepresentativeComplexBalanced K κhat x →
          N.IsMassActionSteadyState κ x) := by
  rcases h with ⟨κhat, hkpos, hres⟩
  refine ⟨κhat, hkpos, ?_⟩
  intro x hx hcb
  exact T.original_steadyState_of_resolved_representativeComplexBalanced
    K κ κhat hres hx hcb

/-- A translated representative realization is steady-state faithful on `X` when original
steady states in `X` are *also* representative complex-balanced. -/
def RepresentativeSteadyStateFaithfulOn
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ)
    (X : Set (Concentration S)) : Prop :=
  T.ResolvesRatesOn K κ κhat X ∧
  ∀ x ∈ X,
    N.IsMassActionSteadyState κ x →
      T.IsRepresentativeComplexBalanced K κhat x

/-- Under steady-state faithfulness, original steady states on `X` are exactly translated
representative complex-balanced states. -/
theorem steadyState_iff_representativeComplexBalanced_of_faithful
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ)
    {X : Set (Concentration S)}
    (h : T.RepresentativeSteadyStateFaithfulOn K κ κhat X)
    {x : Concentration S} (hx : x ∈ X) :
    N.IsMassActionSteadyState κ x ↔
      T.IsRepresentativeComplexBalanced K κhat x := by
  exact ⟨h.2 x hx,
    T.original_steadyState_of_resolved_representativeComplexBalanced
      K κ κhat h.1 hx⟩

/-- **Toric improper resolvability theorem.**  Orthogonality of every source-fibre
difference to the log directions of a toric set gives one fixed positive representative
rate vector valid over that entire set. -/
theorem stronglyResolvableOn_toricSet_of_fiberOrthogonality
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (L : Submodule ℝ (S → ℝ))
    (horth : T.FiberDifferencesOrthogonalTo K L) :
    T.StronglyResolvableOn K κ
      {x | x.Positive ∧
        (fun s => Real.log (x s) - Real.log (xstar s)) ∈ L} := by
  apply T.stronglyResolvableOn_of_fiberRatiosConstant K κ
  exact T.fiberRatiosConstantOn_of_orthogonal_logDirections K hxs L horth

/-- If a translated representative realization is weakly reversible and deficiency zero,
then its complex-balanced toric set can be pulled back to original steady states whenever
the source fibres are orthogonal to the translated toric log directions. -/
theorem original_steadyStates_from_improper_deficiencyZero_translation
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants)
    (hwr : T.network.WeaklyReversible)
    (hδ : T.network.DeficiencyZero)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (L : Submodule ℝ (S → ℝ))
    (horth : T.FiberDifferencesOrthogonalTo K L) :
    ∃ κhat : N.R → ℝ, (∀ r, 0 < κhat r) ∧
      ∀ x, x.Positive →
        (fun s => Real.log (x s) - Real.log (xstar s)) ∈ L →
        T.IsRepresentativeComplexBalanced K κhat x →
        N.IsMassActionSteadyState κ x := by
  have hres := T.stronglyResolvableOn_toricSet_of_fiberOrthogonality
    K κ hxs L horth
  rcases hres with ⟨κhat, hkpos, hrates⟩
  refine ⟨κhat, hkpos, ?_⟩
  intro x hx hlog hcb
  exact T.original_steadyState_of_resolved_representativeComplexBalanced
    K κ κhat hrates ⟨hx, hlog⟩ hcb

end ReactionTranslation
end Network
end CRNT
