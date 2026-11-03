import Scaffold.CRNTExpansion.HigherDeficiencySteadyStates

/-!
# Canonical linkage-class deficiency modes at steady state

The higher-deficiency localization theorem says that, under tight linkage deficiency, each
linkage-class restriction of `A_k Psi(x)` lies in that class's deficiency subspace.  This file
packages those restrictions as actual elements of the finite-dimensional local subspaces.

No basis is chosen.  This keeps the representation canonical while giving later higher-deficiency
algorithms a typed object on which bases/coordinates may be introduced locally.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The canonical local deficiency mode carried by linkage class `q` at a mass-action steady
state. -/
noncomputable def steadyStateLinkageMode
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x)
    (q : Quotient N.linkedSetoid) : N.linkageDeficiencySubspace q :=
  ⟨N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)),
    N.restrictToClass_kineticImage_mem_linkageDeficiencySubspace_of_tight h κ hss q⟩

@[simp] theorem coe_steadyStateLinkageMode
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x)
    (q : Quotient N.linkedSetoid) :
    ((N.steadyStateLinkageMode h κ hss q : N.linkageDeficiencySubspace q) :
      N.ComplexIdx → ℝ) =
      N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) :=
  rfl

/-- Nondeficient linkage classes carry the zero local mode automatically. -/
theorem steadyStateLinkageMode_eq_zero_of_not_mem_deficient
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x)
    (q : Quotient N.linkedSetoid) (hq : q ∉ N.deficientLinkageClasses) :
    N.steadyStateLinkageMode h κ hss q = 0 := by
  apply Subtype.ext
  exact N.steadyState_kineticImage_zero_off_deficientClasses_of_tight h κ hss q hq

/-- The genuinely nontrivial higher-deficiency steady-state datum: all local modes on deficient
linkage classes vanish. -/
def DeficientSteadyStateModesVanish
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) : Prop :=
  ∀ q : Quotient N.linkedSetoid, q ∈ N.deficientLinkageClasses →
    N.steadyStateLinkageMode h κ hss q = 0

/-- For a mass-action steady state of a tight network, complex balance is exactly vanishing of the
canonical local deficiency modes on the deficient classes. -/
theorem isComplexBalanced_iff_deficientSteadyStateModesVanish
    (N : Network S) (h : N.TightLinkageDeficiency) (κ : N.RateConstants)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    N.IsComplexBalanced κ x ↔ N.DeficientSteadyStateModesVanish h κ hss := by
  rw [N.isComplexBalanced_iff_zero_on_deficientClasses_of_tight h κ hss]
  constructor
  · intro hz q hq
    apply Subtype.ext
    simpa [steadyStateLinkageMode] using hz q hq
  · intro hz q hq
    have hmode := hz q hq
    simpa [steadyStateLinkageMode] using
      congrArg (fun z : N.linkageDeficiencySubspace q =>
        (z : N.ComplexIdx → ℝ)) hmode

end Network
end CRNT
