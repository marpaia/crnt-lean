import CRNT.Translation.SourceComplexes
import CRNT.Kinetics.Concentration
import CRNT.Equilibria.Wegscheider
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Improper translations and kinetic resolvability

An improper translation may merge several original source complexes into one translated
source.  To represent the translated system as a generalized mass-action system with one
kinetic complex per translated source, choose a kinetic representative in every source
fibre.  The mismatch between an original source monomial and the chosen representative
monomial is then an explicit multiplicative adjustment factor.
-/

namespace CRNT
namespace Network
namespace ReactionTranslation

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- A choice of one reaction, hence one original kinetic/source complex, for every
translated source complex. -/
structure KineticRepresentative (T : N.ReactionTranslation) where
  reaction : {c // c ∈ T.translatedSourceComplexes} → N.R
  source_eq : ∀ c, T.source (reaction c) = c.val

namespace KineticRepresentative

variable {T : N.ReactionTranslation}

/-- The original source complex chosen as kinetic complex for translated source `c`. -/
def kineticComplex (K : T.KineticRepresentative)
    (c : {c // c ∈ T.translatedSourceComplexes}) : Complex S :=
  (N.reaction (K.reaction c)).source

/-- Every finite translation admits a kinetic representative. -/
noncomputable def choose (T : N.ReactionTranslation) : T.KineticRepresentative where
  reaction := fun c => Classical.choose (T.exists_reaction_of_mem_translatedSourceComplexes c.property)
  source_eq := fun c => Classical.choose_spec (T.exists_reaction_of_mem_translatedSourceComplexes c.property)

end KineticRepresentative

/-- Package the translated source of a reaction as an element of the finite translated
source set. -/
def translatedSourceSubtype (T : N.ReactionTranslation) (r : N.R) :
    {c // c ∈ T.translatedSourceComplexes} :=
  ⟨T.source r, Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩⟩

/-- Multiplicative source-monomial correction relative to a chosen kinetic representative. -/
noncomputable def kineticAdjustmentFactor (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (x : Concentration S) (r : N.R) : ℝ :=
  (N.reaction r).source.massActionMonomial x /
    (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x

/-- Adjusted rate constants at a concentration. -/
noncomputable def adjustedRateConstantsAt (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (κ : N.RateConstants) (x : Concentration S) : N.R → ℝ :=
  fun r => κ.k r * T.kineticAdjustmentFactor K x r

/-- Exact factorization of each original generalized translated rate through the selected
kinetic representative. -/
theorem adjustedRate_mul_representativeMonomial
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) (r : N.R) :
    T.adjustedRateConstantsAt K κ x r *
      (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x =
      κ.k r * (N.reaction r).source.massActionMonomial x := by
  have hrep : 0 <
      (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x :=
    Complex.massActionMonomial_pos hx _
  unfold adjustedRateConstantsAt kineticAdjustmentFactor
  field_simp [ne_of_gt hrep]

/-- A family of adjusted constants resolves the source merging on a set of concentrations
when one representative monomial per translated source reproduces every original rate. -/
def ResolvedOn (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κhat : N.R → ℝ) (X : Set (Concentration S)) : Prop :=
  ∀ x ∈ X, ∀ r : N.R,
    κhat r * (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x =
      κhat r / T.kineticAdjustmentFactor K x r *
        (N.reaction r).source.massActionMonomial x

/-- More direct rate-resolution predicate relative to original rate constants. -/
def ResolvesRatesOn (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (κhat : N.R → ℝ) (X : Set (Concentration S)) : Prop :=
  ∀ x ∈ X, ∀ r : N.R,
    κhat r * (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x =
      κ.k r * (N.reaction r).source.massActionMonomial x

/-- Pointwise every positive concentration is resolvable by concentration-dependent rate
adjustments.  The substantive translation question is whether the same adjustments work
on an entire steady-state/toric set. -/
theorem exists_pointwise_rate_resolution
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) {x : Concentration S} (hx : x.Positive) :
    ∃ κhat : N.R → ℝ,
      ∀ r : N.R,
        κhat r * (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x =
          κ.k r * (N.reaction r).source.massActionMonomial x := by
  refine ⟨T.adjustedRateConstantsAt K κ x, ?_⟩
  exact T.adjustedRate_mul_representativeMonomial K κ hx

/-- Strong resolvability on a set means one fixed positive adjusted-rate vector works
throughout that set. -/
def StronglyResolvableOn (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) (X : Set (Concentration S)) : Prop :=
  ∃ κhat : N.R → ℝ, (∀ r, 0 < κhat r) ∧ T.ResolvesRatesOn K κ κhat X

/-- Proper translations are trivially resolvable by choosing the original source in every
source fibre; no kinetic adjustment is required. -/
theorem stronglyResolvableOn_of_proper
    (T : N.ReactionTranslation) (hproper : T.Proper)
    (κ : N.RateConstants) (X : Set (Concentration S)) :
    ∃ K : T.KineticRepresentative, T.StronglyResolvableOn K κ X := by
  let K := KineticRepresentative.choose T
  refine ⟨K, κ.k, κ.positive, ?_⟩
  intro x hx r
  have htrans : T.source (K.reaction (T.translatedSourceSubtype r)) = T.source r := by
    rw [K.source_eq]
    rfl
  have hsrc : (N.reaction (K.reaction (T.translatedSourceSubtype r))).source =
      (N.reaction r).source := (hproper _ _).1 htrans
  change κ.k r * (N.reaction (K.reaction (T.translatedSourceSubtype r))).source.massActionMonomial x =
    κ.k r * (N.reaction r).source.massActionMonomial x
  rw [hsrc]

end ReactionTranslation
end Network
end CRNT

namespace CRNT.Network.ReactionTranslation

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S} {T : N.ReactionTranslation}

/-- The monomial ratio of every original source to its chosen kinetic representative is constant
on `X`.  This is the intrinsic resolvability condition for an improper source fibre. -/
def FiberRatiosConstantOn (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (X : Set (Concentration S)) : Prop :=
  ∀ r : N.R, ∃ a : ℝ, 0 < a ∧
    ∀ x ∈ X,
      (N.reaction r).source.massActionMonomial x =
        a * (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x

/-- Equivalent formulation using the explicit kinetic adjustment factor. -/
def AdjustmentFactorsConstantOn (T : N.ReactionTranslation)
    (K : T.KineticRepresentative) (X : Set (Concentration S)) : Prop :=
  ∀ r : N.R, ∃ a : ℝ, 0 < a ∧
    ∀ x ∈ X, T.kineticAdjustmentFactor K x r = a

/-- On a positive set, constant source-monomial ratios are exactly constant adjustment factors. -/
theorem fiberRatiosConstantOn_iff_adjustmentFactorsConstantOn
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    {X : Set (Concentration S)} (hX : ∀ x ∈ X, x.Positive) :
    T.FiberRatiosConstantOn K X ↔ T.AdjustmentFactorsConstantOn K X := by
  constructor
  · intro h r
    obtain ⟨a, ha, hra⟩ := h r
    refine ⟨a, ha, ?_⟩
    intro x hx
    unfold kineticAdjustmentFactor
    rw [hra x hx]
    have hp : 0 < (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x :=
      Complex.massActionMonomial_pos (hX x hx) _
    field_simp [ne_of_gt hp]
  · intro h r
    obtain ⟨a, ha, hra⟩ := h r
    refine ⟨a, ha, ?_⟩
    intro x hx
    have hp : 0 < (K.kineticComplex (T.translatedSourceSubtype r)).massActionMonomial x :=
      Complex.massActionMonomial_pos (hX x hx) _
    have hh := hra x hx
    unfold kineticAdjustmentFactor at hh
    field_simp [ne_of_gt hp] at hh
    simpa [mul_comm] using hh

/-- Constant source-fibre ratios give one fixed positive adjusted rate vector that resolves the
improper translation on all of `X`. -/
theorem stronglyResolvableOn_of_fiberRatiosConstant
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) {X : Set (Concentration S)}
    (hconst : T.FiberRatiosConstantOn K X) :
    T.StronglyResolvableOn K κ X := by
  choose a haPos ha using hconst
  let κhat : N.R → ℝ := fun r => κ.k r * a r
  refine ⟨κhat, ?_, ?_⟩
  · intro r
    exact mul_pos (κ.positive r) (haPos r)
  · intro x hx r
    dsimp [κhat]
    rw [ha r x hx]
    ring

/-- If two original reactions merge to the same translated source, strong resolvability forces the
ratio of their original source monomials to be constant on the resolved set. -/
theorem sourceRatio_constant_of_stronglyResolvableOn
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (κ : N.RateConstants) {X : Set (Concentration S)}
    (hX : ∀ x ∈ X, x.Positive)
    (hres : T.StronglyResolvableOn K κ X)
    {r q : N.R} (hmerge : T.source r = T.source q) :
    ∃ a : ℝ, 0 < a ∧ ∀ x ∈ X,
      (N.reaction r).source.massActionMonomial x =
        a * (N.reaction q).source.massActionMonomial x := by
  rcases hres with ⟨κhat, hκhat, hresolve⟩
  let a : ℝ := (κhat r * κ.k q) / (κ.k r * κhat q)
  refine ⟨a, ?_, ?_⟩
  · dsimp [a]
    exact div_pos (mul_pos (hκhat r) (κ.positive q))
      (mul_pos (κ.positive r) (hκhat q))
  · intro x hx
    have hr := hresolve x hx r
    have hq := hresolve x hx q
    have hsub : T.translatedSourceSubtype r = T.translatedSourceSubtype q := by
      apply Subtype.ext
      exact hmerge
    rw [hsub] at hr
    dsimp [a]
    have hkr : κ.k r ≠ 0 := ne_of_gt (κ.positive r)
    have hhq : κhat q ≠ 0 := ne_of_gt (hκhat q)
    let P := (K.kineticComplex (T.translatedSourceSubtype q)).massActionMonomial x
    have hMr : (N.reaction r).source.massActionMonomial x =
        (κhat r / κ.k r) * P := by
      dsimp [P]
      field_simp [hkr]
      nlinarith [hr]
    have hP : P = (κ.k q / κhat q) *
        (N.reaction q).source.massActionMonomial x := by
      dsimp [P]
      field_simp [hhq]
      nlinarith [hq]
    rw [hMr, hP]
    field_simp [hkr, hhq]

/-- **Toric resolvability criterion.**  If every source difference inside an improper fibre is
orthogonal to the logarithmic directions of a positive toric set, then all source-monomial ratios
are constant on that set. -/
def FiberDifferencesOrthogonalTo
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    (L : Submodule ℝ (S → ℝ)) : Prop :=
  ∀ r : N.R, ∀ z ∈ L,
    ∑ s : S,
      (((N.reaction r).source s : ℝ) -
        ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) * z s = 0

/-- Orthogonality of every source-fibre difference to toric log-directions makes the fibre ratios
constant on the corresponding multiplicative torus. -/
theorem fiberRatiosConstantOn_of_orthogonal_logDirections
    (T : N.ReactionTranslation) (K : T.KineticRepresentative)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (L : Submodule ℝ (S → ℝ))
    (horth : T.FiberDifferencesOrthogonalTo K L) :
    T.FiberRatiosConstantOn K
      {x | x.Positive ∧ (fun s => Real.log (x s) - Real.log (xstar s)) ∈ L} := by
  intro r
  let A := (N.reaction r).source
  let B := K.kineticComplex (T.translatedSourceSubtype r)
  let a : ℝ := A.massActionMonomial xstar / B.massActionMonomial xstar
  refine ⟨a, ?_, ?_⟩
  · dsimp [a]
    exact div_pos (Complex.massActionMonomial_pos hxs _)
      (Complex.massActionMonomial_pos hxs _)
  · intro x hx
    have hxpos := hx.1
    have hz := hx.2
    have ho := horth r (fun s => Real.log (x s) - Real.log (xstar s)) hz
    have hsum :
        (∑ s : S,
          (((N.reaction r).source s : ℝ) -
            ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) * Real.log (x s)) =
        ∑ s : S,
          (((N.reaction r).source s : ℝ) -
            ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) * Real.log (xstar s) := by
      rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
      calc
        (∑ s : S,
            ((((N.reaction r).source s : ℝ) -
              ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) * Real.log (x s) -
             (((N.reaction r).source s : ℝ) -
              ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) * Real.log (xstar s))) =
            (∑ s : S,
              (((N.reaction r).source s : ℝ) -
                ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) *
                (Real.log (x s) - Real.log (xstar s))) := by
                  apply Finset.sum_congr rfl
                  intro s hs
                  ring
        _ = 0 := ho
    have hlog : Real.log (A.massActionMonomial x) - Real.log (B.massActionMonomial x) =
        Real.log (A.massActionMonomial xstar) - Real.log (B.massActionMonomial xstar) := by
      rw [CRNT.Network.log_massActionMonomial_eq hxpos A,
          CRNT.Network.log_massActionMonomial_eq hxpos B,
          CRNT.Network.log_massActionMonomial_eq hxs A,
          CRNT.Network.log_massActionMonomial_eq hxs B]
      dsimp [A, B]
      calc
        (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (x s)) -
            (∑ s : S, ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ) * Real.log (x s)) =
          ∑ s : S,
            (((N.reaction r).source s : ℝ) -
              ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) * Real.log (x s) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro s hs
                ring
        _ = ∑ s : S,
            (((N.reaction r).source s : ℝ) -
              ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ)) * Real.log (xstar s) := hsum
        _ = (∑ s : S, ((N.reaction r).source s : ℝ) * Real.log (xstar s)) -
            (∑ s : S, ((K.kineticComplex (T.translatedSourceSubtype r)) s : ℝ) * Real.log (xstar s)) := by
                rw [← Finset.sum_sub_distrib]
                apply Finset.sum_congr rfl
                intro s hs
                ring
    have hAx : 0 < A.massActionMonomial x := Complex.massActionMonomial_pos hxpos _
    have hBx : 0 < B.massActionMonomial x := Complex.massActionMonomial_pos hxpos _
    have hAs : 0 < A.massActionMonomial xstar := Complex.massActionMonomial_pos hxs _
    have hBs : 0 < B.massActionMonomial xstar := Complex.massActionMonomial_pos hxs _
    dsimp [a]
    have hratio : Real.log (A.massActionMonomial x / B.massActionMonomial x) =
        Real.log (A.massActionMonomial xstar / B.massActionMonomial xstar) := by
      rw [Real.log_div hAx.ne' hBx.ne', Real.log_div hAs.ne' hBs.ne']
      exact hlog
    have hdiv : A.massActionMonomial x / B.massActionMonomial x =
        A.massActionMonomial xstar / B.massActionMonomial xstar := by
      calc
        A.massActionMonomial x / B.massActionMonomial x =
            Real.exp (Real.log (A.massActionMonomial x / B.massActionMonomial x)) :=
          (Real.exp_log (div_pos hAx hBx)).symm
        _ = Real.exp (Real.log (A.massActionMonomial xstar / B.massActionMonomial xstar)) :=
          congrArg Real.exp hratio
        _ = A.massActionMonomial xstar / B.massActionMonomial xstar :=
          Real.exp_log (div_pos hAs hBs)
    field_simp [ne_of_gt hBx, ne_of_gt hBs] at hdiv ⊢
    nlinarith [hdiv]

end CRNT.Network.ReactionTranslation
