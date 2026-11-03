import CRNT.Deficiency.DeficiencyOneLine
import CRNT.Deficiency.DeficiencyOneLocalize
import CRNT.Deficiency.ClassConservation
import CRNT.Deficiency.TerminalKernelCone
import CRNT.Equilibria.CompatibilityClass

/-!
# Scalar reduction of the deficiency-one steady-state equations

At deficiency one the kinetic image of every positive steady state lies on a fixed line
`ℝ g` inside the deficiency subspace.  The remaining steady-state equations can therefore
be separated into a positive kinetic-kernel component plus one scalar deficiency
coordinate.  This is the algebraic backbone of the Deficiency One Theorem and the
Shinar--Feinberg ACR theorem.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A chosen generator of the one-dimensional deficiency space. -/
structure DeficiencyOneGenerator (N : Network S) where
  g : N.ComplexIdx → ℝ
  mem : g ∈ N.deficiencySubspace
  ne_zero : g ≠ 0
  spans : ∀ w ∈ N.deficiencySubspace, ∃ a : ℝ, w = a • g

/-- Every deficiency-one network admits a generator. -/
theorem exists_deficiencyOneGenerator (N : Network S)
    (hδ : N.DeficiencyOne) : Nonempty N.DeficiencyOneGenerator := by
  obtain ⟨g, hg, hg0, hspan⟩ := N.exists_spanning_deficiencySubspace_of_deficiencyOne hδ
  refine ⟨{ g := g, mem := hg, ne_zero := hg0, spans := ?_ }⟩
  intro w hw
  obtain ⟨a, ha⟩ := hspan w hw
  exact ⟨a, ha.symm⟩

/-- Scalar deficiency coordinate of a steady state relative to a chosen generator. -/
def HasDeficiencyCoordinate (N : Network S) (κ : N.RateConstants)
    (G : N.DeficiencyOneGenerator) (x : Concentration S) (a : ℝ) : Prop :=
  N.kineticMap κ (N.complexMonomialVector x) = a • G.g

/-- Every positive mass-action steady state has a scalar deficiency coordinate. -/
theorem exists_deficiencyCoordinate_of_steadyState (N : Network S)
    (κ : N.RateConstants) (G : N.DeficiencyOneGenerator)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    ∃ a : ℝ, N.HasDeficiencyCoordinate κ G x a := by
  have hmem := N.kineticMap_complexMonomial_mem_deficiencySubspace κ hss
  obtain ⟨a, ha⟩ := G.spans _ hmem
  exact ⟨a, ha⟩

/-- The deficiency coordinate is unique for a nonzero generator. -/
theorem deficiencyCoordinate_unique (N : Network S)
    (κ : N.RateConstants) (G : N.DeficiencyOneGenerator)
    {x : Concentration S} {a b : ℝ}
    (ha : N.HasDeficiencyCoordinate κ G x a)
    (hb : N.HasDeficiencyCoordinate κ G x b) : a = b := by
  have h : a • G.g = b • G.g := ha.symm.trans hb
  by_contra hab
  have : (a - b) • G.g = 0 := by
    rw [sub_smul, h, sub_self]
  have hs : a - b = 0 := by
    exact (smul_eq_zero.mp this).resolve_right G.ne_zero
  exact hab (sub_eq_zero.mp hs)

/-- Canonical scalar coordinate, chosen by existence/uniqueness. -/
noncomputable def deficiencyCoordinate (N : Network S) (κ : N.RateConstants)
    (G : N.DeficiencyOneGenerator) (x : Concentration S)
    (hss : N.IsMassActionSteadyState κ x) : ℝ :=
  Classical.choose (N.exists_deficiencyCoordinate_of_steadyState κ G hss)

/-- Defining equation for the canonical coordinate. -/
theorem kineticImage_eq_deficiencyCoordinate (N : Network S)
    (κ : N.RateConstants) (G : N.DeficiencyOneGenerator)
    {x : Concentration S} (hss : N.IsMassActionSteadyState κ x) :
    N.kineticMap κ (N.complexMonomialVector x) =
      N.deficiencyCoordinate κ G x hss • G.g := by
  exact Classical.choose_spec (N.exists_deficiencyCoordinate_of_steadyState κ G hss)

/-- Deficiency-one uniqueness reduces to injectivity of the scalar branch together with
classwise kinetic-kernel uniqueness. -/
def DeficiencyScalarInjective (N : Network S) (κ : N.RateConstants)
    (G : N.DeficiencyOneGenerator) : Prop :=
  ∀ {x y : Concentration S}
    (hx : N.IsMassActionSteadyState κ x)
    (hy : N.IsMassActionSteadyState κ y),
    x.Positive → y.Positive → N.StoichCompatible x y →
    N.deficiencyCoordinate κ G x hx = N.deficiencyCoordinate κ G y hy → x = y

/-- Scalar reduction principle for the Deficiency One Theorem. -/
theorem deficiencyOne_uniqueness_of_scalarInjective (N : Network S)
    (κ : N.RateConstants) (G : N.DeficiencyOneGenerator)
    (hscalar : N.DeficiencyScalarInjective κ G) :
    ∀ {x y : Concentration S},
      x.Positive → y.Positive → N.StoichCompatible x y →
      -- these must be *named* binders: `‹_›` cannot resolve an anonymous arrow
      -- hypothesis while the statement is being elaborated.
      ∀ (hssx : N.IsMassActionSteadyState κ x) (hssy : N.IsMassActionSteadyState κ y),
      N.deficiencyCoordinate κ G x hssx =
        N.deficiencyCoordinate κ G y hssy → x = y := by
  intro x y hx hy hcomp hssx hssy hcoord
  exact hscalar hssx hssy hx hy hcomp hcoord

end Network
end CRNT
