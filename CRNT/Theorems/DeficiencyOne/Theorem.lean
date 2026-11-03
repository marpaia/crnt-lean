import CRNT.Theorems.DeficiencyOne.Statement
import CRNT.Theorems.DeficiencyOne.MultiClass
import CRNT.Theorems.DeficiencyOne.JacobianOnStoich
import CRNT.Deficiency.DeficiencyOneLocalize
import CRNT.Deficiency.DeficiencyOneStructure
import CRNT.Theorems.DeficiencyOne.DegreeExistence
import CRNT.Theorems.DeficiencyZero.Toric
import CRNT.Deficiency.DeficiencyOneDecomp
import CRNT.Deficiency.KineticBlock
import CRNT.Deficiency.SteadyStateKernel

/-!
# Feinberg's Deficiency One Theorem

This module promotes the existing statement API to the actual classical theorem.
The long deficiency-one sign/kernel argument is isolated in the theorem proof rather
than being propagated as an extra assumption to downstream developments.

Hypotheses:
1. every linkage-class deficiency is at most one;
2. the class deficiencies sum to the network deficiency;
3. every linkage class has exactly one terminal strong linkage class.

Conclusions:
* at most one positive mass-action steady state per stoichiometric class, for every
  positive rate vector;
* if the network is weakly reversible, exactly one positive steady state occurs in
  every positive stoichiometric class;
* at every positive steady state, the Jacobian is nonsingular on the
  stoichiometric tangent space.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Feinberg Deficiency One Theorem: uniqueness.** -/
theorem deficiencyOne_uniqueness
    (N : Network S) (h : N.DeficiencyOneHypotheses) :
    N.DeficiencyOneUniqueness :=
  -- `deficiencyOneUniqueness_multiClass` in `MultiClass.lean` proves exactly this statement,
  -- and in fact without assuming `δ = 1`; that module is `sorry`-free.
  N.deficiencyOneUniqueness_multiClass h

/-- Named implication form for downstream theorem search. -/
theorem DeficiencyOneHypotheses.uniqueness
    {N : Network S} (h : N.DeficiencyOneHypotheses) :
    N.DeficiencyOneUniqueness :=
  N.deficiencyOne_uniqueness h

/-- **Feinberg Deficiency One Theorem: weakly reversible existence and uniqueness.** -/
theorem deficiencyOne_existence_of_weaklyReversible
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (hwr : N.WeaklyReversible) : N.DeficiencyOneExistence := by
  intro κ x₀ hx₀
  -- Weak reversibility supplies positive terminal-class kernel vectors.  The
  -- deficiency-one existence argument solves the class scaling equations and
  -- Birch-type intersection with the positive stoichiometric class.  Uniqueness
  -- is the preceding theorem.
  have hex : ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x :=
    N.deficiencyOne_exists_positiveSteadyState_via_degree h hwr κ hx₀
  rcases hex with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact N.deficiencyOne_uniqueness h κ x₀ hx₀ hy.1 hy.2 hx.1 hx.2

/-- Weakly reversible networks satisfying the hypotheses have exactly one positive
steady state in every positive stoichiometric class for **every** positive rate vector. -/
theorem DeficiencyOneHypotheses.existence
    {N : Network S} (h : N.DeficiencyOneHypotheses)
    (hwr : N.WeaklyReversible) : N.DeficiencyOneExistence :=
  N.deficiencyOne_existence_of_weaklyReversible h hwr

private noncomputable def toricClassScale (N : Network S)
    (x xstar : Concentration S) (q : Quotient N.linkedSetoid) : ℝ :=
  Real.exp (∑ s, ((Classical.choose (Quotient.exists_rep q)).val s : ℝ) *
    (Real.log (x s) - Real.log (xstar s)))

private theorem pairing_eqOn_linked_of_orthogonal
    (N : Network S) {μ : S → ℝ} (hμ : μ ∈ orthSum N.stoichSubspace)
    {c d : Complex S} (hcd : N.Linked c d) :
    (∑ s, (c s : ℝ) * μ s) = ∑ s, (d s : ℝ) * μ s := by
  induction hcd with
  | refl => rfl
  | tail _ hedge ih =>
      apply ih.trans
      rcases hedge with ⟨r, hs, ht⟩ | ⟨r, hs, ht⟩
      · rw [← hs, ← ht]
        exact (N.pairing_eq_of_orthogonal hμ r).symm
      · rw [← hs, ← ht]
        exact N.pairing_eq_of_orthogonal hμ r

private theorem restrict_monomial_eq_smul_of_toric
    (N : Network S) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive)
    (htoric : (fun s => Real.log (x s) - Real.log (xstar s)) ∈ orthSum N.stoichSubspace)
    (q : Quotient N.linkedSetoid) :
    N.restrictToClass q (N.complexMonomialVector x) =
      N.toricClassScale x xstar q • N.restrictToClass q (N.complexMonomialVector xstar) := by
  funext c
  by_cases hc : N.classOf c = q
  · rw [N.restrictToClass_apply_of_eq _ hc]
    change N.complexMonomialVector x c = N.toricClassScale x xstar q *
      N.restrictToClass q (N.complexMonomialVector xstar) c
    rw [N.restrictToClass_apply_of_eq _ hc]
    let rep : N.ComplexIdx := Classical.choose (Quotient.exists_rep q)
    have hrep : N.classOf rep = q := Classical.choose_spec (Quotient.exists_rep q)
    have hlink : N.Linked c.val rep.val := Quotient.exact (hc.trans hrep.symm)
    have hpair : (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s))) =
        ∑ s, (rep.val s : ℝ) * (Real.log (x s) - Real.log (xstar s)) :=
      N.pairing_eqOn_linked_of_orthogonal htoric hlink
    rw [N.complexMonomialVector_eq_mul_exp hx hxs c]
    unfold toricClassScale
    change N.complexMonomialVector xstar c *
        Real.exp (∑ s, (c.val s : ℝ) * (Real.log (x s) - Real.log (xstar s))) =
      Real.exp (∑ s, (rep.val s : ℝ) * (Real.log (x s) - Real.log (xstar s))) *
        N.complexMonomialVector xstar c
    rw [hpair]
    ring
  · rw [N.restrictToClass_apply_of_ne _ hc]
    change 0 = N.toricClassScale x xstar q *
      N.restrictToClass q (N.complexMonomialVector xstar) c
    rw [N.restrictToClass_apply_of_ne _ hc, mul_zero]

private theorem steady_of_toric_of_deficiencyOneConditions
    (N : Network S) (h : N.DeficiencyOneConditions)
    (κ : N.RateConstants) {x xstar : Concentration S}
    (hx : x.Positive) (hxs : xstar.Positive)
    (hss : N.IsMassActionSteadyState κ xstar)
    (htoric : (fun s => Real.log (x s) - Real.log (xstar s)) ∈ orthSum N.stoichSubspace) :
    N.IsMassActionSteadyState κ x := by
  have hvstar : N.kineticMap κ (N.complexMonomialVector xstar) ∈ N.deficiencySubspace :=
    N.kineticMap_complexMonomial_mem_deficiencySubspace κ hss
  have hclasszero : ∀ q : Quotient N.linkedSetoid,
      N.complexMap (N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x))) = 0 := by
    intro q
    have hmemstar := N.restrictToClass_mem_linkageDeficiencySubspace h hvstar q
    have hdefstar : N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector xstar)) ∈
        N.deficiencySubspace := (Submodule.mem_inf.mp hmemstar).1
    have hkerstar : N.complexMap
        (N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector xstar))) = 0 :=
      LinearMap.mem_ker.mp (Submodule.mem_inf.mp hdefstar).1
    have hmon := N.restrict_monomial_eq_smul_of_toric hx hxs htoric q
    have hkin : N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector x)) =
        N.toricClassScale x xstar q •
          N.restrictToClass q (N.kineticMap κ (N.complexMonomialVector xstar)) := by
      rw [← N.kineticMap_restrictToClass κ q, hmon, map_smul,
          N.kineticMap_restrictToClass]
    rw [hkin, map_smul, hkerstar, smul_zero]
  intro s
  have hvec : N.complexMap (N.kineticMap κ (N.complexMonomialVector x)) = 0 := by
    rw [← N.sum_restrictToClass (N.kineticMap κ (N.complexMonomialVector x)), map_sum]
    exact Finset.sum_eq_zero fun q _ => hclasszero q
  have hvf := N.massActionVectorField_eq κ x
  rw [hvf, hvec, Pi.zero_apply]

/-- If one positive steady state exists for a fixed rate vector, then every positive
stoichiometric compatibility class contains exactly one.  This is the non-WR
existence form of the classical theorem. -/
theorem deficiencyOne_existsUnique_every_class_of_exists_positive
    (N : Network S) (h : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants)
    (hex : ∃ x : Concentration S, x.Positive ∧ N.IsMassActionSteadyState κ x) :
    ∀ x₀ : Concentration S, x₀.Positive →
      ∃! x : Concentration S,
        x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  intro x₀ hx₀
  obtain ⟨xstar, hxs, hss⟩ := hex
  have hclass : ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
    obtain ⟨x, hxpos, hxc, hxorth⟩ := birch_existence N.stoichSubspace hxs hx₀
    have horth : (fun s => Real.log (x s) - Real.log (xstar s)) ∈
        orthSum N.stoichSubspace := by
      rw [mem_orthSum]
      exact hxorth
    have hxss : N.IsMassActionSteadyState κ x :=
      N.steady_of_toric_of_deficiencyOneConditions h.conditions κ hxpos hxs hss horth
    exact ⟨x, ⟨hxc, hxpos⟩, hxss⟩
  rcases hclass with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact N.deficiencyOne_uniqueness h κ x₀ hx₀ hy.1 hy.2 hx.1 hx.2

end Network
end CRNT
