import CRNT.Translation.ReactionTranslation
import CRNT.Dynamics.MassActionAlgebra

/-!
# Generalized complex balance on translated networks

A reaction-wise translation keeps the original source complexes as kinetic complexes while
replacing the stoichiometry with the translated one. *Generalized complex balance* is ordinary
complex balance on the translated reaction graph, with fluxes still computed from the original
kinetics.

## Rewritten against the real API

An earlier draft of this module was written against a structure `N.ReactionTranslation` carrying
fields `source`, `target`, `network`, `generalizedVectorField` and
`generalizedVectorField_eq_original`. No such structure exists anywhere in the repository: the
translation API in `CRNT/Translation/ReactionTranslation.lean` is a bare function
`τ : N.R → Complex S`, with `N.translate τ` producing the translated `Network`. Every declaration
in that draft failed to elaborate, and its central theorem was `sorry`.

This version is phrased on `τ` directly, and the central result is proved rather than assumed, by
reduction to two facts that already exist:

* `IsComplexBalanced.isMassActionSteadyState` (`CRNT/Dynamics/MassActionAlgebra.lean`) -- complex
  balance kills the mass-action field, via regrouping by complex;
* `translatedGeneralizedVectorField_eq_massActionVectorField`
  (`CRNT/Translation/ReactionTranslation.lean`) -- the dynamical-equivalence theorem.

The observation that makes it go through is that the generalized rate
`κ.k r * (N.reaction r).source.massActionMonomial x` is *definitionally* the original network's
`massActionRate`, so generalized in/outflow on the translated graph are the translated network's
own in/outflow at the translated rate constants.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- Generalized reaction rate: translated stoichiometry, original kinetic complex. -/
def generalizedRate (N : Network S) (τ : N.R → Complex S) (κ : RateConstants N)
    (x : Concentration S) (r : N.R) : ℝ :=
  N.translatedGeneralizedRate τ κ r x

/-- Generalized outflow from a complex of the translated graph. -/
def generalizedOutflow (N : Network S) (τ : N.R → Complex S) (κ : RateConstants N)
    (x : Concentration S) (c : Complex S) : ℝ :=
  ∑ r : N.R, if ((N.translate τ).reaction r).source = c then
    N.generalizedRate τ κ x r else 0

/-- Generalized inflow into a complex of the translated graph. -/
def generalizedInflow (N : Network S) (τ : N.R → Complex S) (κ : RateConstants N)
    (x : Concentration S) (c : Complex S) : ℝ :=
  ∑ r : N.R, if ((N.translate τ).reaction r).target = c then
    N.generalizedRate τ κ x r else 0

/-- **Generalized complex balance**: balance on the translated reaction graph, with fluxes still
taken from the original kinetics. -/
def IsGeneralizedComplexBalanced (N : Network S) (τ : N.R → Complex S)
    (κ : RateConstants N) (x : Concentration S) : Prop :=
  ∀ c ∈ (N.translate τ).complexes,
    N.generalizedInflow τ κ x c = N.generalizedOutflow τ κ x c

/-- The generalized rate is the original network's mass-action rate; the translation changes
stoichiometry, not kinetics. -/
theorem generalizedRate_eq_massActionRate (N : Network S) (τ : N.R → Complex S)
    (κ : RateConstants N) (x : Concentration S) (r : N.R) :
    N.generalizedRate τ κ x r = N.massActionRate κ r x := rfl

/-! ### Regrouping a weighted reaction sum by complex

Generalized balance is **not** complex balance of the translated network: the translated network's
kinetic complex is its own (shifted) source, whereas the generalized rate keeps the *original*
source as kinetic complex. Trying to bridge the two directly fails, and Lean rejects it. So the
vanishing of the field is proved from scratch, for an arbitrary weight function on reactions. -/

/-- A weighted reaction sum regroups as a sum over complexes of the total weight landing on
(respectively leaving) that complex. -/
theorem sum_weight_regroup (M : Network S) (w : M.R → ℝ) (g : M.R → Complex S)
    (hg : ∀ r, g r ∈ M.complexes) (s : S) :
    (∑ c ∈ M.complexes, (∑ r : M.R, if g r = c then w r else 0) * (c s : ℝ))
      = ∑ r : M.R, w r * ((g r) s : ℝ) := by
  classical
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_ite_eq M.complexes (g r) (fun c => w r * (c s : ℝ))]
  simp [hg r]

/-- **Graph balance kills the weighted reaction-vector sum.** Stated for an arbitrary weight, so
it applies to generalized as well as ordinary mass-action fluxes. -/
theorem sum_weight_reactionVector_eq_zero_of_balanced (M : Network S) (w : M.R → ℝ)
    (h : ∀ c ∈ M.complexes,
      (∑ r : M.R, if (M.reaction r).target = c then w r else 0)
        = ∑ r : M.R, if (M.reaction r).source = c then w r else 0)
    (s : S) : (∑ r : M.R, w r * M.reactionVector r s) = 0 := by
  classical
  simp only [reactionVector_apply]
  have hsplit : ∀ r : M.R,
      w r * (((M.reaction r).target s : ℝ) - ((M.reaction r).source s : ℝ))
        = w r * ((M.reaction r).target s : ℝ) - w r * ((M.reaction r).source s : ℝ) :=
    fun r => by ring
  simp only [hsplit]
  rw [Finset.sum_sub_distrib,
    ← M.sum_weight_regroup w (fun r => (M.reaction r).target) M.target_mem_complexes s,
    ← M.sum_weight_regroup w (fun r => (M.reaction r).source) M.source_mem_complexes s,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_eq_zero fun c hc => ?_
  rw [h c hc, sub_self]

/-- **Generalized complex balance annihilates the translated generalized vector field.** -/
theorem translatedGeneralizedVectorField_eq_zero_of_isGeneralizedComplexBalanced
    (N : Network S) (τ : N.R → Complex S) (κ : RateConstants N) (x : Concentration S)
    (hcb : N.IsGeneralizedComplexBalanced τ κ x) :
    N.translatedGeneralizedVectorField τ κ x = 0 := by
  funext s
  simp only [translatedGeneralizedVectorField]
  exact (N.translate τ).sum_weight_reactionVector_eq_zero_of_balanced
    (fun r => N.translatedGeneralizedRate τ κ r x) (fun c hc => hcb c hc) s

/-- **A generalized complex-balanced state is a steady state of the original network.**

This is the payoff of dynamical equivalence: balance is checked on the translated graph, but the
conclusion is about the original mass-action system. -/
theorem isMassActionSteadyState_of_isGeneralizedComplexBalanced
    (N : Network S) (τ : N.R → Complex S) (κ : RateConstants N) (x : Concentration S)
    (hcb : N.IsGeneralizedComplexBalanced τ κ x) :
    N.IsMassActionSteadyState κ x := by
  have hz := N.translatedGeneralizedVectorField_eq_zero_of_isGeneralizedComplexBalanced τ κ x hcb
  rw [N.translatedGeneralizedVectorField_eq_massActionVectorField τ κ] at hz
  intro s
  exact congrFun hz s

end Network

namespace Network.ReactionTranslation

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- Translation-level wrapper for the generalized reaction rate. -/
def generalizedRate (T : N.ReactionTranslation) (κ : RateConstants N)
    (x : Concentration S) (r : N.R) : ℝ :=
  N.generalizedRate T κ x r

/-- Translation-level wrapper for generalized complex balance. -/
abbrev IsGeneralizedComplexBalanced (T : N.ReactionTranslation)
    (κ : RateConstants N) (x : Concentration S) : Prop :=
  N.IsGeneralizedComplexBalanced T κ x

/-- Generalized complex balance of a translation yields an original steady state. -/
theorem original_isMassActionSteadyState_of_generalizedComplexBalanced
    (T : N.ReactionTranslation) (κ : RateConstants N) (x : Concentration S)
    (hcb : T.IsGeneralizedComplexBalanced κ x) :
    N.IsMassActionSteadyState κ x :=
  N.isMassActionSteadyState_of_isGeneralizedComplexBalanced T κ x hcb

end Network.ReactionTranslation

end CRNT
