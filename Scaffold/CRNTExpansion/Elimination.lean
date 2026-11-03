import CRNT.Algebra.SteadyStateIdeal

/-!
# Elimination-ideal scaffold for CRNT polynomial systems

Mathlib already supplies ideal `comap` and multivariate-polynomial variable renaming.  For a chosen
set `U` of retained species, the inclusion `U -> S` embeds `R[U]` into `R[S]`; comapping an ideal
along that embedding is the corresponding elimination/intersection ideal.

This is the algebraic interface needed before formalizing concrete CRNT elimination results.  A
future Gröbner-basis layer can prove effective descriptions of these ideals without changing the
semantic API here.
-/

namespace CRNT
namespace Network

open MvPolynomial

variable {S : Type}

/-- Elimination/intersection ideal obtained by retaining only variables in `U`. -/
noncomputable def eliminationIdeal (I : Ideal (MvPolynomial S ℝ)) (U : Set S) :
    Ideal (MvPolynomial U ℝ) :=
  I.comap (MvPolynomial.rename (fun u : U => u.1))

/-- Membership in the elimination ideal is exactly membership of the renamed polynomial in the
ambient ideal. -/
theorem mem_eliminationIdeal_iff (I : Ideal (MvPolynomial S ℝ)) (U : Set S)
    (p : MvPolynomial U ℝ) :
    p ∈ eliminationIdeal I U <-> MvPolynomial.rename (fun u : U => u.1) p ∈ I :=
  Iff.rfl

/-- Elimination is monotone in the ambient ideal. -/
theorem eliminationIdeal_mono {I J : Ideal (MvPolynomial S ℝ)} (h : I ≤ J) (U : Set S) :
    eliminationIdeal I U ≤ eliminationIdeal J U := by
  intro p hp
  exact h hp


/-- Elimination ideal of the mass-action steady-state equations after retaining only species in
`U`.  This packages the generic `eliminationIdeal` construction at the main CRNT polynomial
system. -/
noncomputable def steadyStateEliminationIdeal
    [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants) (U : Set S) :
    Ideal (MvPolynomial U ℝ) :=
  eliminationIdeal (N.steadyStateIdeal κ) U

/-- Elimination ideal of the complex-balance equations. -/
noncomputable def complexBalanceEliminationIdeal
    [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants) (U : Set S) :
    Ideal (MvPolynomial U ℝ) :=
  eliminationIdeal (N.complexBalanceIdeal κ) U

/-- Elimination ideal of the tree-constant binomial equations. -/
noncomputable def treeBinomialEliminationIdeal
    [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants) (U : Set S) :
    Ideal (MvPolynomial U ℝ) :=
  eliminationIdeal (N.treeBinomialIdeal κ) U

/-- A retained-species polynomial belongs to the steady-state elimination ideal exactly when its
ambient renaming belongs to the full steady-state ideal. -/
theorem mem_steadyStateEliminationIdeal_iff
    [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (U : Set S) (p : MvPolynomial U ℝ) :
    p ∈ N.steadyStateEliminationIdeal κ U ↔
      MvPolynomial.rename (fun u : U => u.1) p ∈ N.steadyStateIdeal κ :=
  Iff.rfl

/-- The structural containment `I_ss <= I_cb` survives elimination to any retained set of
species.  Thus every polynomial consequence visible after elimination from the steady-state ideal
is also a consequence of the complex-balance ideal. -/
theorem steadyStateEliminationIdeal_le_complexBalanceEliminationIdeal
    [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants) (U : Set S) :
    N.steadyStateEliminationIdeal κ U ≤ N.complexBalanceEliminationIdeal κ U := by
  exact eliminationIdeal_mono (N.steadyStateIdeal_le_complexBalanceIdeal κ) U

/-- Membership in the tree-binomial elimination ideal has the expected ambient interpretation. -/
theorem mem_treeBinomialEliminationIdeal_iff
    [DecidableEq S] [Fintype S] (N : Network S) (κ : N.RateConstants)
    (U : Set S) (p : MvPolynomial U ℝ) :
    p ∈ N.treeBinomialEliminationIdeal κ U ↔
      MvPolynomial.rename (fun u : U => u.1) p ∈ N.treeBinomialIdeal κ :=
  Iff.rfl

end Network
end CRNT
