import CRNT.Translation.Improper
import CRNT.Translation.ComplexBalance

/-!
# Complex balance of resolvable improper translations

An improper translation chooses one kinetic representative for every translated source.  When a
fixed positive adjusted rate vector resolves the source-monomial ratios on a set `X`, generalized
complex balance computed with those representatives is exactly generalized complex balance of the
original translated realization on `X`.  Hence every such balanced point is an original mass-action
steady state.
-/

namespace CRNT
namespace Network
namespace ReactionTranslation

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Resolved generalized rate using one representative kinetic complex per translated source. -/
def resolvedRate (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κhat : N.R → ℝ) (x : Concentration S) (r : N.R) : ℝ :=
  κhat r * (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x

/-- Resolved inflow at a translated complex. -/
def resolvedInflow (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κhat : N.R → ℝ) (x : Concentration S) (c : Complex S) : ℝ :=
  ∑ r : N.R, if T.target r = c then T.resolvedRate K κhat x r else 0

/-- Resolved outflow at a translated complex. -/
def resolvedOutflow (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κhat : N.R → ℝ) (x : Concentration S) (c : Complex S) : ℝ :=
  ∑ r : N.R, if T.source r = c then T.resolvedRate K κhat x r else 0

/-- Complex balance of a representative-resolved translated system. -/
def IsResolvedComplexBalanced (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κhat : N.R → ℝ) (x : Concentration S) : Prop :=
  ∀ c ∈ T.network.complexes,
    T.resolvedInflow K κhat x c = T.resolvedOutflow K κhat x c

/-- On a resolved set, every resolved representative rate equals the original generalized
translated reaction rate. -/
theorem resolvedRate_eq_generalizedRate_of_resolvesRatesOn
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ) {X : Set (Concentration S)}
    (hres : T.ResolvesRatesOn K κ κhat X) {x : Concentration S} (hx : x ∈ X)
    (r : N.R) :
    T.resolvedRate K κhat x r = T.generalizedRate κ x r := by
  exact hres x hx r

/-- Resolved complex balance transfers to generalized complex balance of the original translated
realization. -/
theorem generalizedComplexBalanced_of_resolved
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ) {X : Set (Concentration S)}
    (hres : T.ResolvesRatesOn K κ κhat X) {x : Concentration S} (hx : x ∈ X)
    (hcb : T.IsResolvedComplexBalanced K κhat x) :
    T.IsGeneralizedComplexBalanced κ x := by
  intro c hc
  have hrate : ∀ r : N.R, T.resolvedRate K κhat x r = N.generalizedRate T κ x r := by
    intro r
    exact hres x hx r
  have hin : T.resolvedInflow K κhat x c = N.generalizedInflow T κ x c := by
    unfold resolvedInflow Network.generalizedInflow
    apply Finset.sum_congr rfl
    intro r hr
    change (if T.target r = c then T.resolvedRate K κhat x r else 0) =
      (if T.target r = c then N.generalizedRate T κ x r else 0)
    by_cases ht : T.target r = c <;> simp [ht, hrate r]
  have hout : T.resolvedOutflow K κhat x c = N.generalizedOutflow T κ x c := by
    unfold resolvedOutflow Network.generalizedOutflow
    apply Finset.sum_congr rfl
    intro r hr
    change (if T.source r = c then T.resolvedRate K κhat x r else 0) =
      (if T.source r = c then N.generalizedRate T κ x r else 0)
    by_cases hs : T.source r = c <;> simp [hs, hrate r]
  rw [← hin, ← hout]
  apply hcb c
  exact hc

/-- **Resolved translated complex balance gives an original steady state.** -/
theorem originalSteadyState_of_resolvedComplexBalanced
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ) {X : Set (Concentration S)}
    (hres : T.ResolvesRatesOn K κ κhat X) {x : Concentration S} (hx : x ∈ X)
    (hcb : T.IsResolvedComplexBalanced K κhat x) :
    N.IsMassActionSteadyState κ x :=
  T.original_isMassActionSteadyState_of_generalizedComplexBalanced κ x
    (T.generalizedComplexBalanced_of_resolved K κ κhat hres hx hcb)

/-- Strong resolvability packages a fixed positive resolved translated realization on `X`. -/
theorem exists_positive_resolved_realization
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) {X : Set (Concentration S)}
    (hstrong : T.StronglyResolvableOn K κ X) :
    ∃ κhat : N.R → ℝ, (∀ r, 0 < κhat r) ∧
      ∀ x ∈ X,
        T.IsResolvedComplexBalanced K κhat x → N.IsMassActionSteadyState κ x := by
  rcases hstrong with ⟨κhat, hkpos, hres⟩
  refine ⟨κhat, hkpos, ?_⟩
  intro x hx hcb
  exact T.originalSteadyState_of_resolvedComplexBalanced K κ κhat hres hx hcb

end ReactionTranslation
end Network
end CRNT
