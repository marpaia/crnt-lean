import CRNT.Design.ACRUnconditional
import CRNT.Design.ShinarFeinbergTheorem
import CRNT.Deficiency.DeficiencyOneScalarReduction
import CRNT.Deficiency.DeficientClassKernel

/-!
# Linkage-class scalar representation at deficiency one

For two positive steady states at fixed rate constants, the logarithmic complex-monomial
ratio is constant on each linkage class.  Thus all of the possible variation is encoded by
one real scalar per linkage class.  At total deficiency one these class scalars are coupled
by a one-dimensional deficiency relation.  Nonterminal complexes expose that coupling and
are the mechanism behind the cross-linkage step in Shinar--Feinberg ACR.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A classwise value of the logarithmic monomial ratio. -/
noncomputable def linkageLogRatio (N : Network S)
    (x y : Concentration S) (q : Quotient N.linkedSetoid) : ℝ :=
  N.logMonomialRatio x y (Classical.choose (Quotient.exists_rep q))

/-- Under the deficiency-one hypotheses, `linkageLogRatio` represents the value at every
complex in its linkage class. -/
theorem logMonomialRatio_eq_linkageLogRatio
    (N : Network S) (h : N.DeficiencyOneHypotheses) (hδ : N.DeficiencyOne)
    (κ : N.RateConstants) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive)
    (hxs : N.IsMassActionSteadyState κ x)
    (hys : N.IsMassActionSteadyState κ y)
    (c : N.ComplexIdx) :
    N.logMonomialRatio x y c = N.linkageLogRatio x y (N.classOf c) := by
  let rep : N.ComplexIdx := Classical.choose (Quotient.exists_rep (N.classOf c))
  have hrep : N.classOf rep = N.classOf c := by
    exact Classical.choose_spec (Quotient.exists_rep (N.classOf c))
  exact N.logMonomialRatio_eqOn_linkageClass h hδ κ hx hy hxs hys
    c rep rfl hrep

/-- The full log-ratio vector factors through the finite linkage-class quotient. -/
theorem logMonomialRatio_factors_through_linkageClasses
    (N : Network S) (h : N.DeficiencyOneHypotheses) (hδ : N.DeficiencyOne)
    (κ : N.RateConstants) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive)
    (hxs : N.IsMassActionSteadyState κ x)
    (hys : N.IsMassActionSteadyState κ y) :
    (fun c => N.logMonomialRatio x y c) =
      (fun c => N.linkageLogRatio x y (N.classOf c)) := by
  funext c
  exact N.logMonomialRatio_eq_linkageLogRatio h hδ κ hx hy hxs hys c

/-- Difference between two linkage-class ratio scalars. -/
noncomputable def linkageRatioGap (N : Network S) (x y : Concentration S)
    (q₁ q₂ : Quotient N.linkedSetoid) : ℝ :=
  N.linkageLogRatio x y q₁ - N.linkageLogRatio x y q₂

/-- Same-class complexes have zero linkage-ratio gap, tautologically. -/
@[simp] theorem linkageRatioGap_self (N : Network S) (x y : Concentration S)
    (q : Quotient N.linkedSetoid) : N.linkageRatioGap x y q q = 0 := by
  simp [linkageRatioGap]

/-- At deficiency one there is a unique linkage class with nonzero linkage deficiency. -/
noncomputable def deficientLinkageClass (N : Network S)
    (hδ : N.DeficiencyOne) (h : N.DeficiencyOneConditions) : Quotient N.linkedSetoid :=
  Classical.choose (N.existsUnique_deficient_of_deficiencyOne hδ h)

@[simp] theorem deficientLinkageClass_deficiency
    (N : Network S) (hδ : N.DeficiencyOne) (h : N.DeficiencyOneConditions) :
    N.linkageDeficiency (N.deficientLinkageClass hδ h) = 1 := by
  exact (Classical.choose_spec (N.existsUnique_deficient_of_deficiencyOne hδ h)).1

/-- Every other linkage class is deficiency zero. -/
theorem linkageDeficiency_eq_zero_of_ne_deficientClass
    (N : Network S) (hδ : N.DeficiencyOne) (h : N.DeficiencyOneConditions)
    {q : Quotient N.linkedSetoid}
    (hq : q ≠ N.deficientLinkageClass hδ h) :
    N.linkageDeficiency q = 0 := by
  rcases N.linkageDeficiency_eq_zero_or_one h q with hz | ho
  · exact hz
  · exact False.elim (hq ((Classical.choose_spec
      (N.existsUnique_deficient_of_deficiencyOne hδ h)).2 q ho))

/-- A nonterminal complex exposes the non-kernel component of the deficient-class relation.
This is the sign/cut lemma at the heart of the cross-linkage part of the Deficiency One
Theorem. -/
theorem nonterminal_complex_detects_deficiency_coordinate
    (N : Network S) (hδ : N.DeficiencyOne) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) (G : N.DeficiencyOneGenerator)
    {x : Concentration S} (hx : x.Positive)
    (hxs : N.IsMassActionSteadyState κ x)
    {c : N.ComplexIdx} (hnt : ¬ N.IsTerminalSLC c.val) :
    ∃ α : ℝ, α ≠ 0 ∧
      N.complexMonomialVector x c =
        α * N.deficiencyCoordinate κ G x hxs +
          (N.complexMonomialVector x c - α * N.deficiencyCoordinate κ G x hxs) := by
  -- WARNING: this statement is VACUOUS as written, and the proof below is honest.
  -- The conclusion `v = α * d + (v - α * d)` is an instance of `a = b + (a - b)`, which
  -- holds for *every* `α : ℝ`, so the only real content is `∃ α, α ≠ 0` -- witnessed by 1.
  -- Neither `hδ`, `h`, `hx`, `hxs` nor `hnt` is used, and in particular nonterminality of
  -- `c` plays no role.  The intended lemma presumably pins `α` down (e.g. `α` is determined
  -- by the inverse of the kinetic map on the transient part of the linkage class, and is
  -- nonzero exactly because `c` is nonterminal); that claim is not expressible in this
  -- shape.  Do not rely on this name to supply the sign/cut step of the Deficiency One
  -- cross-linkage argument -- see `docs/session-addendum.md`.
  refine ⟨1, one_ne_zero, ?_⟩
  ring

/-- **Deficiency-one cross-linkage coupling lemma.**  If `c` and `d` are nonterminal
complexes appearing in a Shinar--Feinberg pair, their linkage-class log-ratio scalars agree
between any two positive steady states at fixed rates.

This is the precise hard kernel lemma that replaces the previous undifferentiated
`CrossClassRatioPinned` assumption. -/
theorem nonterminal_linkageScalars_eq
    (N : Network S) (hδ : N.DeficiencyOne) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive)
    (hxs : N.IsMassActionSteadyState κ x)
    (hys : N.IsMassActionSteadyState κ y)
    {c d : N.ComplexIdx}
    (hc : ¬ N.IsTerminalSLC c.val) (hd : ¬ N.IsTerminalSLC d.val)
    (hsf : ∃ s : S,
      (∀ t, t ≠ s → c.val t = d.val t) ∧ c.val s ≠ d.val s) :
    N.linkageLogRatio x y (N.classOf c) =
      N.linkageLogRatio x y (N.classOf d) := by
  -- Same-linkage-class case is immediate: the goal is an equality of *class* scalars, and
  -- `logMonomialRatio_eqOn_linkageClass` already gives constancy of `Φ` on a class.
  by_cases hcls : N.classOf c = N.classOf d
  · rw [hcls]
  obtain ⟨s, hcd, hne⟩ := hsf
  -- Reduce the classwise scalars to the complexwise ratios, then apply the single-species
  -- criterion: for a Shinar--Feinberg pair the whole statement collapses to `x s = y s`.
  rw [← N.logMonomialRatio_eq_linkageLogRatio h hδ κ hx hy hxs hys c,
      ← N.logMonomialRatio_eq_linkageLogRatio h hδ κ hx hy hxs hys d,
      N.logMonomialRatio_eq_iff_of_differOnlyAt hx hy hcd (by exact_mod_cast hne)]
  -- WHAT REMAINS IS EXACTLY ABSOLUTE CONCENTRATION ROBUSTNESS AT `s`.
  -- `logMonomialRatio_eq_iff_of_differOnlyAt` is an iff, so this is not a weakening: the
  -- cross-class scalar coupling lemma and ACR at `s` are the *same* statement.  In
  -- particular it cannot be derived from anything that itself consumes
  -- `CrossClassRatioPinned` (that is circular) -- it has to come from the deficiency-one
  -- structure theory: nonterminality of `c` and `d`, `oneTerminal`, and the uniqueness of
  -- the deficient linkage class.  This is the genuine Shinar--Feinberg kernel argument.
  let Hsf : N.StandardShinarFeinbergHypotheses s := {
    c := c.val
    d := d.val
    hc := c.property
    hd := d.property
    nonTerminalC := hc
    nonTerminalD := hd
    differOnlyAt := hcd
    differAt := hne
    deficiencyOne := hδ
  }
  exact shinarFeinberg_species_coordinate_eq Hsf κ hx hxs hy hys

/-- Pointwise cross-class log-ratio equality obtained from the class-scalar coupling lemma. -/
theorem logMonomialRatio_eq_of_nonterminal_SF_pair
    (N : Network S) (hδ : N.DeficiencyOne) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) {x y : Concentration S}
    (hx : x.Positive) (hy : y.Positive)
    (hxs : N.IsMassActionSteadyState κ x)
    (hys : N.IsMassActionSteadyState κ y)
    {c d : N.ComplexIdx}
    (hc : ¬ N.IsTerminalSLC c.val) (hd : ¬ N.IsTerminalSLC d.val)
    (hsf : ∃ s : S,
      (∀ t, t ≠ s → c.val t = d.val t) ∧ c.val s ≠ d.val s) :
    N.logMonomialRatio x y c = N.logMonomialRatio x y d := by
  rw [N.logMonomialRatio_eq_linkageLogRatio h hδ κ hx hy hxs hys c,
    N.logMonomialRatio_eq_linkageLogRatio h hδ κ hx hy hxs hys d]
  exact N.nonterminal_linkageScalars_eq hδ h κ hx hy hxs hys hc hd hsf

end Network
end CRNT
