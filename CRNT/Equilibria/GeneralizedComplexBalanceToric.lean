import CRNT.Equilibria.GeneralizedTreeConstantCriterion
import CRNT.Kinetics.GeneralizedConditions
import CRNT.Kinetics.GeneralizedNondegeneracy

/-!
# Toric geometry of generalized complex-balanced equilibria

For a weakly reversible generalized mass-action system, the tree-constant binomials become an
affine linear system after taking logarithms.  Differences of logarithms of two generalized CBEs
lie in the orthogonal complement of the kinetic-order subspace.  Thus a nonempty generalized CBE
set is a multiplicative torus with tangent directions `Tᗮ`, where `T` is the kinetic-order
subspace.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Stoichiometric compatibility of two concentrations. -/
def SameStoichClass (N : Network S) (x y : Concentration S) : Prop :=
  x - y ∈ N.stoichSubspace

namespace GeneralizedMassActionData

open scoped BigOperators

variable {N : Network S}

/-- Coordinatewise logarithm of a positive concentration. -/
noncomputable def logConcentration (x : Concentration S) : S → ℝ := fun s => Real.log (x s)

/-- Generalized log-ratio between positive concentrations. -/
noncomputable def logRatio (x y : Concentration S) : S → ℝ :=
  fun s => Real.log (x s) - Real.log (y s)

/-- Affine logarithmic tree-constant equations for generalized complex balance. -/
def SatisfiesLogTreeEquations
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (x : Concentration S) : Prop :=
  ∀ i j : N.ComplexIdx, N.Linked i.1 j.1 →
    ∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * Real.log (x s) =
      Real.log (N.treeConstant κ j) - Real.log (N.treeConstant κ i)

/-- On a weakly reversible graph, positive tree-constant binomials are equivalent to their
logarithmic affine form. -/
theorem treeConstantBinomials_iff_logTreeEquations
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) :
    G.SatisfiesTreeConstantBinomials κ x ↔ G.SatisfiesLogTreeEquations κ x := by
  constructor
  · intro hbin i j hij
    have hKj : 0 < N.treeConstant κ j :=
      N.treeConstant_pos_of_weaklyReversible κ hwr j
    have hKi : 0 < N.treeConstant κ i :=
      N.treeConstant_pos_of_weaklyReversible κ hwr i
    have hmi : 0 < G.kineticMonomial (G.kineticComplex i) x :=
      G.kineticMonomial_pos _ _
    have hmj : 0 < G.kineticMonomial (G.kineticComplex j) x :=
      G.kineticMonomial_pos _ _
    have hlog := congrArg Real.log (hbin i j hij)
    rw [Real.log_mul hKj.ne' hmi.ne', Real.log_mul hKi.ne' hmj.ne'] at hlog
    unfold kineticMonomial at hlog
    rw [Real.log_exp, Real.log_exp] at hlog
    have hsum :
        (∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * Real.log (x s)) =
          (∑ s : S, G.kineticComplex j s * Real.log (x s)) -
            (∑ s : S, G.kineticComplex i s * Real.log (x s)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hsum]
    linarith
  · intro hlog i j hij
    have hKj : 0 < N.treeConstant κ j :=
      N.treeConstant_pos_of_weaklyReversible κ hwr j
    have hKi : 0 < N.treeConstant κ i :=
      N.treeConstant_pos_of_weaklyReversible κ hwr i
    have hz := hlog i j hij
    have hsum :
        (∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * Real.log (x s)) =
          (∑ s : S, G.kineticComplex j s * Real.log (x s)) -
            (∑ s : S, G.kineticComplex i s * Real.log (x s)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      ring
    rw [hsum] at hz
    have hadd :
        Real.log (N.treeConstant κ j) +
            (∑ s : S, G.kineticComplex i s * Real.log (x s)) =
          Real.log (N.treeConstant κ i) +
            (∑ s : S, G.kineticComplex j s * Real.log (x s)) := by
      linarith
    have hexp := congrArg Real.exp hadd
    rw [Real.exp_add, Real.exp_add, Real.exp_log hKj, Real.exp_log hKi] at hexp
    simpa [kineticMonomial] using hexp

/-- Generalized complex balance is equivalent to the affine log-tree system. -/
theorem complexBalanced_iff_logTreeEquations
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {x : Concentration S} (hx : x.Positive) :
    G.IsComplexBalanced κ x ↔ G.SatisfiesLogTreeEquations κ x := by
  rw [G.complexBalanced_iff_treeConstantBinomials κ hwr]
  exact G.treeConstantBinomials_iff_logTreeEquations κ hwr hx

/-- Difference of the log concentrations of two generalized CBEs is orthogonal to the
kinetic-order subspace. -/
theorem logRatio_mem_orth_kineticOrderSubspace
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hcx : G.IsComplexBalanced κ x) (hcy : G.IsComplexBalanced κ y) :
    logRatio x y ∈ orthSum G.kineticOrderSubspace := by
  have hlogx : G.SatisfiesLogTreeEquations κ x :=
    (G.complexBalanced_iff_logTreeEquations κ hwr hx).1 hcx
  have hlogy : G.SatisfiesLogTreeEquations κ y :=
    (G.complexBalanced_iff_logTreeEquations κ hwr hy).1 hcy
  have hrzero : ∀ r : N.R,
      (∑ s : S, logRatio x y s *
        (G.kineticComplex (N.targetIdx r) s - G.kineticComplex (N.sourceIdx r) s)) = 0 := by
    intro r
    have hxy := hlogx (N.sourceIdx r) (N.targetIdx r) (N.linked_of_reaction r)
    have hyy := hlogy (N.sourceIdx r) (N.targetIdx r) (N.linked_of_reaction r)
    have hsum :
        (∑ s : S, logRatio x y s *
          (G.kineticComplex (N.targetIdx r) s - G.kineticComplex (N.sourceIdx r) s)) =
          (∑ s : S, (G.kineticComplex (N.targetIdx r) s -
              G.kineticComplex (N.sourceIdx r) s) * Real.log (x s)) -
          (∑ s : S, (G.kineticComplex (N.targetIdx r) s -
              G.kineticComplex (N.sourceIdx r) s) * Real.log (y s)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro s _
      simp only [logRatio]
      ring
    rw [hsum]
    linarith
  rw [mem_orthSum]
  intro v hv
  rcases hv with ⟨a, rfl⟩
  simp_rw [G.kineticOrderMap_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro r _
  calc
    (∑ s : S, logRatio x y s *
        (a r * (G.kineticComplex (N.targetIdx r) s -
          G.kineticComplex (N.sourceIdx r) s))) =
        a r * (∑ s : S, logRatio x y s *
          (G.kineticComplex (N.targetIdx r) s -
            G.kineticComplex (N.sourceIdx r) s)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s _
          ring
    _ = 0 := by rw [hrzero r, mul_zero]

/-- A positive state belongs to the generalized toric leaf through `xstar` when its logarithmic
ratio lies in the kinetic-order orthogonal complement. -/
def InGeneralizedToricLeaf
    (G : N.GeneralizedMassActionData) (xstar x : Concentration S) : Prop :=
  x.Positive ∧ logRatio x xstar ∈ orthSum G.kineticOrderSubspace

/-- Every generalized CBE lies on the toric leaf through any positive generalized CBE reference. -/
theorem inGeneralizedToricLeaf_of_complexBalanced
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive) (hx : x.Positive)
    (hcbs : G.IsComplexBalanced κ xstar) (hcb : G.IsComplexBalanced κ x) :
    G.InGeneralizedToricLeaf xstar x :=
  ⟨hx, G.logRatio_mem_orth_kineticOrderSubspace κ hwr hx hxs hcb hcbs⟩

/-- Conversely, moving a positive generalized CBE along the multiplicative toric leaf preserves
complex balance. -/
theorem complexBalanced_of_toricLeaf
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {xstar x : Concentration S} (hxs : xstar.Positive)
    (hcbs : G.IsComplexBalanced κ xstar)
    (hx : G.InGeneralizedToricLeaf xstar x) :
    G.IsComplexBalanced κ x := by
  have hstar : G.SatisfiesLogTreeEquations κ xstar :=
    (G.complexBalanced_iff_logTreeEquations κ hwr hxs).1 hcbs
  apply (G.complexBalanced_iff_logTreeEquations κ hwr hx.1).2
  intro i j hij
  have hb := hstar i j hij
  have hD : (fun s => G.kineticComplex j s - G.kineticComplex i s) ∈
      G.kineticOrderSubspace := G.kineticComplex_sub_mem_of_linked hij
  have ho := (mem_orthSum.mp hx.2) _ hD
  have hsum :
      (∑ s : S, logRatio x xstar s *
        (G.kineticComplex j s - G.kineticComplex i s)) =
        (∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * Real.log (x s)) -
        (∑ s : S, (G.kineticComplex j s - G.kineticComplex i s) * Real.log (xstar s)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    simp only [logRatio]
    ring
  rw [hsum] at ho
  linarith

/-- **Toric characterization of generalized CBEs.** Once one positive generalized CBE exists,
the entire positive CBE set is its multiplicative leaf in `Tᗮ`.

`x.Positive` is an explicit hypothesis rather than something derived. `IsComplexBalanced` is the
pure balance condition `∀ c, inflow c = outflow c`, which carries no positivity whatsoever — the
zero state satisfies it vacuously — so the forward implication is simply false without it. The
earlier formulation tried to recover positivity inside the proof, which is not possible. -/
theorem complexBalanced_iff_toricLeaf
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcbs : G.IsComplexBalanced κ xstar) {x : Concentration S} (hx : x.Positive) :
    G.IsComplexBalanced κ x ↔ G.InGeneralizedToricLeaf xstar x := by
  constructor
  · intro h
    exact G.inGeneralizedToricLeaf_of_complexBalanced κ hwr hxs hx hcbs h
  · exact G.complexBalanced_of_toricLeaf κ hwr hxs hcbs

/-- Müller--Regensburger uniqueness at CRN level: the sign condition prevents two distinct
positive generalized CBEs in one stoichiometric class. -/
theorem complexBalanced_unique_in_stoichClass_of_signCompatible
    (G : N.GeneralizedMassActionData) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible)
    (hsign : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace))
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hcx : G.IsComplexBalanced κ x) (hcy : G.IsComplexBalanced κ y)
    (hclass : SameStoichClass N x y) : x = y := by
  apply gen_birch_uniqueness N.stoichSubspace G.kineticOrderSubspace hsign hx hy hclass
  simpa [logRatio] using
    G.logRatio_mem_orth_kineticOrderSubspace κ hwr hx hy hcx hcy

/-- Pointwise nondegeneracy of every positive generalized CBE follows from the same sign condition. -/
theorem complexBalanced_nondegenerate_of_signCompatible
    (G : N.GeneralizedMassActionData)
    (hsign : SignCompatible N.stoichSubspace (orthSum G.kineticOrderSubspace))
    {x : Concentration S} (hx : x.Positive) :
    GeneralizedToricNondegenerateAt N.stoichSubspace G.kineticOrderSubspace x :=
  generalizedToricNondegenerate_of_signCompatible
    N.stoichSubspace G.kineticOrderSubspace hsign hx

end GeneralizedMassActionData
end Network
end CRNT
