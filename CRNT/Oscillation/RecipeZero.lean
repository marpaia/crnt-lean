import CRNT.Oscillation.ParameterRich
import CRNT.Oscillation.MatrixCriteria
import CRNT.Deficiency.Consistent

/-!
# Recipe 0: stability change along an invertible symbolic-Jacobian path

The 2026 parameter-rich framework includes a route to periodic behavior that does not require an
oscillatory core.  A principal block of the symbolic Jacobian remains nonsingular while parameters
move between a Hurwitz-stable and a Hurwitz-unstable configuration.  A global-Hopf continuation
argument then yields a nonstationary periodic orbit.

This file formalizes a strong, explicit certificate form of that recipe.  Instead of an arbitrary
partially specified parameter set, the certificate supplies two strict reactivity matrices and uses
their straight-line interpolation.  The interpolation remains a strict reactivity matrix on
`[0,1]`; the certificate checks nonsingularity of one principal block all along that path.

The final global-Hopf implication remains an explicit theorem target.  No axiom or numerical orbit
is substituted for it.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Straight-line reactivity interpolation starts at its left endpoint. -/
@[simp] theorem interpolateReactivity_zero (N : Network S) (R₀ R₁ : N.ReactivityMatrix) :
    N.interpolateReactivity R₀ R₁ 0 = R₀ := by
  funext r s
  simp [interpolateReactivity]

/-- Straight-line reactivity interpolation ends at its right endpoint. -/
@[simp] theorem interpolateReactivity_one (N : Network S) (R₀ R₁ : N.ReactivityMatrix) :
    N.interpolateReactivity R₀ R₁ 1 = R₁ := by
  funext r s
  simp [interpolateReactivity]

/-- A finite Recipe-0 certificate on a principal species block.

The path is the convex interpolation from `stableR` to `unstableR`.  Requiring both endpoints to be
strict reactivity matrices guarantees that every interior point is also admissible. -/
structure RecipeZeroCertificate (N : Network S) : Type where
  species : Finset S
  nonempty : species.Nonempty
  rankSized : species.card = N.stoichRank
  stableR : N.ReactivityMatrix
  unstableR : N.ReactivityMatrix
  stableR_admissible : N.IsReactivityMatrix stableR
  unstableR_admissible : N.IsReactivityMatrix unstableR
  stable : ((N.symbolicJacobian stableR).principalSubmatrix species).IsHurwitzReal
  unstable : ((N.symbolicJacobian unstableR).principalSubmatrix species).HasUnstableEigenvalue
  path_invertible : ∀ μ : ℝ, μ ∈ Set.Icc (0 : ℝ) 1 →
    (((N.symbolicJacobian (N.interpolateReactivity stableR unstableR μ)).principalSubmatrix
      species).det ≠ 0)

namespace RecipeZeroCertificate

variable {N : Network S}

/-- Every point of the certified Recipe-0 interpolation is a strict reactivity matrix. -/
theorem path_admissible (C : RecipeZeroCertificate N) {μ : ℝ}
    (hμ : μ ∈ Set.Icc (0 : ℝ) 1) :
    N.IsReactivityMatrix (N.interpolateReactivity C.stableR C.unstableR μ) :=
  C.stableR_admissible.interpolate C.unstableR_admissible hμ.1 hμ.2

/-- The stable endpoint block is nonsingular, as a consequence of the path certificate. -/
theorem stable_det_ne_zero (C : RecipeZeroCertificate N) :
    ((N.symbolicJacobian C.stableR).principalSubmatrix C.species).det ≠ 0 := by
  simpa using C.path_invertible 0 ⟨le_rfl, zero_le_one⟩

/-- The unstable endpoint block is also nonsingular. -/
theorem unstable_det_ne_zero (C : RecipeZeroCertificate N) :
    ((N.symbolicJacobian C.unstableR).principalSubmatrix C.species).det ≠ 0 := by
  simpa using C.path_invertible 1 ⟨zero_le_one, le_rfl⟩

/-- Every Recipe-0 certificate is already a witness of symbolic nondegeneracy: its stable endpoint
provides an admissible nonsingular principal block of exactly the stoichiometric rank. -/
theorem isSymbolicallyNondegenerate (C : RecipeZeroCertificate N) :
    N.IsSymbolicallyNondegenerate :=
  N.isSymbolicallyNondegenerate_of_witness C.stableR_admissible C.rankSized C.stable_det_ne_zero

end RecipeZeroCertificate

/-- Exact analytic frontier for Recipe 0 in a specified parameter-rich family.

`SupportsSmoothReactivityPaths` supplies one coherent smooth kinetic realization of the straight
reactivity path.  `IsConsistent` supplies steady-state compatibility.  Rank-reduced nondegeneracy is
already carried by `RecipeZeroCertificate.rankSized` plus `path_invertible`; the remaining theorem is
the global-Hopf continuation from nonsingular stability change to a periodic orbit. -/
def ParameterRichRecipeZeroRealizationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T] (N : Network T)
    (F : N.SteadyStateParameterRichFamily),
    N.SupportsSmoothReactivityPaths F → N.IsConsistent →
      Nonempty (RecipeZeroCertificate N) → N.ParameterRichOscillatoryCapacity F

/-- Consume a proved Recipe-0 global-Hopf theorem. -/
theorem RecipeZeroCertificate.parameterRichOscillatoryCapacity
    {N : Network S} (hRealize : ParameterRichRecipeZeroRealizationTarget)
    (F : N.SteadyStateParameterRichFamily) (hpaths : N.SupportsSmoothReactivityPaths F)
    (hcons : N.IsConsistent) (C : RecipeZeroCertificate N) :
    N.ParameterRichOscillatoryCapacity F :=
  hRealize N F hpaths hcons ⟨C⟩

end Network

end CRNT
