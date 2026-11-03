import CRNT.Theorems.DeficiencyOne.Theorem
import CRNT.Deficiency.DeficiencyOne
import CRNT.Deficiency.LinkageCouplingLine
import CRNT.Deficiency.BorosDeficiencyOneReduction
import CRNT.Deficiency.BorosActiveInwardEstimate
import CRNT.Deficiency.PositiveKineticSection
import CRNT.Deficiency.PositiveKineticObstructionIVT
import CRNT.Deficiency.ClassScaleSynchronization
import CRNT.Deficiency.PositiveKineticFamily
import CRNT.Deficiency.PositiveKineticDomain
import CRNT.Deficiency.StrictKineticDissipation
import CRNT.Deficiency.BirchClassScaleTransport
import CRNT.Deficiency.LogObstructionClassScaling

import CRNT.Kinetics.GeneralizedBirchSelector
/-!
# Positive steady-state existence for arbitrary weakly reversible deficiency-one networks

The classical Deficiency One Theorem imposes linkage-class deficiency additivity and
one terminal strong linkage class per linkage class.  A later theorem is stronger on
the **existence** side: every weakly reversible network of total deficiency one has a
positive mass-action steady state in every positive stoichiometric compatibility
class, for every positive rate vector, even when the classical Deficiency One Theorem
hypotheses do not hold.

This module keeps that result separate from the classical uniqueness theorem: weakly
reversible deficiency one guarantees existence, not by itself the classical
Deficiency-One-Theorem uniqueness conclusion.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

open scoped BigOperators Classical

/-- Weak reversibility collapses every linkage class to one strong linkage class, hence that
class is automatically the unique terminal strong linkage class in its linkage class. -/
theorem WeaklyReversible.oneTerminalSLCPerLinkageClass
    {N : Network S} (hwr : N.WeaklyReversible) :
    N.OneTerminalSLCPerLinkageClass := by
  intro θ
  refine Quotient.inductionOn θ ?_
  intro c
  let σ : Quotient N.stronglyLinkedSetoid := Quotient.mk N.stronglyLinkedSetoid c
  refine ⟨σ, ?_, ?_⟩
  · constructor
    · rfl
    · rw [show N.IsTerminalSLClass σ = N.IsTerminalSLC c.val by rfl]
      intro r hr
      have hlink : N.Linked c.val (N.reaction r).target :=
        hr.linked.trans (N.linked_of_reaction r)
      exact ⟨hwr.reaches_of_linked hlink, hwr.reaches_of_linked hlink.symm⟩
  · intro τ hτ
    refine Quotient.inductionOn τ ?_ hτ
    intro d hd
    apply Quotient.sound
    have hq : Quotient.mk N.linkedSetoid d = Quotient.mk N.linkedSetoid c := by
      simpa using hd.1
    have hlink : N.Linked d.val c.val := Quotient.exact hq
    exact ⟨hwr.reaches_of_linked hlink, hwr.reaches_of_linked hlink.symm⟩

/-- Total deficiency one forces every linkage-class deficiency to be at most one, even without
assuming the linkage-deficiency additivity condition from the classical Deficiency One Theorem. -/
theorem linkageDeficiency_le_one_of_deficiencyOne
    (N : Network S) (hδ : N.DeficiencyOne) (q : Quotient N.linkedSetoid) :
    N.linkageDeficiency q ≤ 1 := by
  have hqsum : N.linkageDeficiency q ≤ ∑ q', N.linkageDeficiency q' := by
    exact Finset.single_le_sum
      (fun q' _ => N.linkageDeficiency_nonneg q') (Finset.mem_univ q)
  have hsum := N.sum_linkageDeficiency_le_deficiency
  rw [hδ] at hsum
  exact hqsum.trans hsum

/-- At total deficiency one, the sum of linkage-class deficiencies has only two possibilities:
zero or one.  The second is exactly the classical additivity condition; the first is the genuine
non-DOT residual case. -/
theorem sum_linkageDeficiency_eq_zero_or_one_of_deficiencyOne
    (N : Network S) (hδ : N.DeficiencyOne) :
    (∑ q, N.linkageDeficiency q) = 0 ∨ (∑ q, N.linkageDeficiency q) = 1 := by
  have h0 : (0 : ℤ) ≤ ∑ q, N.linkageDeficiency q :=
    Finset.sum_nonneg fun q _ => N.linkageDeficiency_nonneg q
  have h1 := N.sum_linkageDeficiency_le_deficiency
  rw [hδ] at h1
  omega

/-- A zero sum of the nonnegative linkage deficiencies means that every linkage class itself has
deficiency zero. -/
theorem linkageDeficiency_eq_zero_of_sum_eq_zero
    (N : Network S) (hsum : (∑ q, N.linkageDeficiency q) = 0) :
    ∀ q, N.linkageDeficiency q = 0 := by
  intro q
  have hnonneg : ∀ q' ∈ (Finset.univ : Finset (Quotient N.linkedSetoid)),
      0 ≤ N.linkageDeficiency q' := fun q' _ => N.linkageDeficiency_nonneg q'
  have hall := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum
  exact hall q (Finset.mem_univ q)

/-- In the additive branch, weak reversibility and total deficiency one automatically supply all
three classical Deficiency One Theorem structural hypotheses. -/
theorem deficiencyOneHypotheses_of_weaklyReversible_of_sum_linkageDeficiency_eq_one
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne)
    (hsum : (∑ q, N.linkageDeficiency q) = 1) : N.DeficiencyOneHypotheses := by
  refine ⟨?_, hwr.oneTerminalSLCPerLinkageClass⟩
  refine ⟨N.linkageDeficiency_le_one_of_deficiencyOne hδ, ?_⟩
  exact hsum.trans hδ.symm

/-- CRNT-specific structural reduction for weakly reversible deficiency-one networks.  Either the
classical DOT hypotheses already hold, or every linkage class is individually deficiency zero and
the sole global deficiency comes from non-additivity of the linkage-class stoichiometric spaces. -/
theorem weaklyReversible_deficiencyOne_structural_dichotomy
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne) :
    N.DeficiencyOneHypotheses ∨ ∀ q, N.linkageDeficiency q = 0 := by
  rcases N.sum_linkageDeficiency_eq_zero_or_one_of_deficiencyOne hδ with hsum | hsum
  · exact Or.inr (N.linkageDeficiency_eq_zero_of_sum_eq_zero hsum)
  · exact Or.inl
      (N.deficiencyOneHypotheses_of_weaklyReversible_of_sum_linkageDeficiency_eq_one
        hwr hδ hsum)

/-- In the residual (`Type II`) branch the whole deficiency is exactly the one-dimensional
overlap of the linkage-class stoichiometric subspaces. -/
theorem linkageCouplingDeficiency_eq_one_of_deficiencyOne_of_sum_eq_zero
    (N : Network S) (hδ : N.DeficiencyOne)
    (hsum : ∑ q, N.linkageDeficiency q = 0) :
    N.linkageCouplingDeficiency = 1 := by
  have hdec := N.deficiencyInt_eq_sum_linkageDeficiency_add_coupling
  rw [hδ, hsum] at hdec
  have hc : (N.linkageCouplingDeficiency : ℤ) = 1 := by omega
  exact_mod_cast hc

/-- Equivalently, in the Type-II branch the sum of the linkage stoichiometric ranks exceeds
the global stoichiometric rank by exactly one. -/
theorem sum_linkageStoichRank_eq_stoichRank_add_one_of_deficiencyOne_of_sum_eq_zero
    (N : Network S) (hδ : N.DeficiencyOne)
    (hsum : ∑ q, N.linkageDeficiency q = 0) :
    (∑ q, N.linkageStoichRank q) = N.stoichRank + 1 := by
  have hc := N.linkageCouplingDeficiency_eq_one_of_deficiencyOne_of_sum_eq_zero hδ hsum
  have hr := N.stoichRank_add_linkageCoupling_eq_sum
  omega

/-- Thus the Type-II branch is genuinely non-additive: its linkage stoichiometric subspaces are
not independent. -/
theorem not_linkageStoichIndependent_of_deficiencyOne_of_sum_eq_zero
    (N : Network S) (hδ : N.DeficiencyOne)
    (hsum : ∑ q, N.linkageDeficiency q = 0) :
    ¬ N.LinkageStoichIndependent := by
  intro hind
  have hc := (N.linkageCouplingDeficiency_eq_zero_iff).2 hind
  have h1 := N.linkageCouplingDeficiency_eq_one_of_deficiencyOne_of_sum_eq_zero hδ hsum
  omega

/-- Type II therefore carries a genuine nontrivial linear coupling relation between linkage
stoichiometric subspaces: classwise vectors, not all zero, whose sum vanishes. -/
theorem exists_nontrivial_linkageStoich_relation_of_deficiencyOne_of_sum_eq_zero
    (N : Network S) (hδ : N.DeficiencyOne)
    (hsumδ : ∑ q, N.linkageDeficiency q = 0) :
    ∃ u : (Quotient N.linkedSetoid) → (S → ℝ),
      (∀ q, u q ∈ N.linkageStoichSubspace q) ∧
      (∑ q, u q = 0) ∧ ∃ q, u q ≠ 0 := by
  classical
  have hrank := N.sum_linkageStoichRank_eq_stoichRank_add_one_of_deficiencyOne_of_sum_eq_zero
    hδ hsumδ
  have hnot : ¬ iSupIndep N.linkageStoichSubspace := by
    intro hind
    have heq := finrank_finset_sup_eq_sum_of_iSupIndep
      (K := ℝ) (V := S → ℝ) Finset.univ N.linkageStoichSubspace hind
    rw [← N.stoichSubspace_eq_sup] at heq
    change N.stoichRank = ∑ q, N.linkageStoichRank q at heq
    omega
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero] at hnot
  push Not at hnot
  obtain ⟨t, v, hv, hvsum, q0, hq0t, hq0ne⟩ := hnot
  let u : (Quotient N.linkedSetoid) → (S → ℝ) := fun q => if q ∈ t then v q else 0
  refine ⟨u, ?_, ?_, q0, ?_⟩
  · intro q
    by_cases hq : q ∈ t
    · simp only [u, if_pos hq]
      exact hv q hq
    · simp only [u, if_neg hq]
      exact (N.linkageStoichSubspace q).zero_mem
  · simpa [u] using hvsum
  · simp [u, hq0t, hq0ne]

/-- The additive (`Type I`) branch of weakly-reversible deficiency-one existence is already
covered by the classical Deficiency One Theorem. The structural reduction above manufactures
all three DOT hypotheses from weak reversibility, deficiency one, and `∑ δ_θ = 1`. -/
theorem weaklyReversible_deficiencyOne_exists_positive_steadyState_of_sum_eq_one
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne)
    (hsum : ∑ q, N.linkageDeficiency q = 1)
    (κ : N.RateConstants) (x₀ : Concentration S) (hx₀ : x₀.Positive) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  let h : N.DeficiencyOneHypotheses :=
    N.deficiencyOneHypotheses_of_weaklyReversible_of_sum_linkageDeficiency_eq_one hwr hδ hsum
  exact N.deficiencyOne_exists_positiveSteadyState_via_degree h hwr κ hx₀

/-- **Weakly reversible deficiency-one existence theorem.** -/
theorem weaklyReversible_deficiencyOne_exists_positive_steadyState
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne)
    (κ : N.RateConstants) (x₀ : Concentration S) (hx₀ : x₀.Positive) :
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  rcases N.sum_linkageDeficiency_eq_zero_or_one_of_deficiencyOne hδ with hsum | hsum
  · -- Type II: all linkage deficiencies vanish and the unique deficiency is coupling.
    have hclass : ∀ q, N.linkageDeficiency q = 0 :=
      N.linkageDeficiency_eq_zero_of_sum_eq_zero hsum
    have hcoupling : N.linkageCouplingDeficiency = 1 :=
      N.linkageCouplingDeficiency_eq_one_of_deficiencyOne_of_sum_eq_zero hδ hsum
    have hcouplingLine : Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) = 1 := by
      rw [N.finrank_ker_linkageStoichSumMap, hcoupling]
    obtain ⟨couplingGen, hcouplingGenKer, hcouplingGen0, hcouplingSpan⟩ :=
      N.exists_spanning_linkageStoichCoupling_of_coupling_one hcoupling
    -- The global deficiency line and the Type-II linkage-coupling line are canonically
    -- equivalent. This identifies the unique cancellation direction between the otherwise
    -- deficiency-zero linkage classes.
    let e := N.typeIILinkageCouplingEquiv hδ hclass hcoupling
    have hefin : Module.finrank ℝ N.deficiencySubspace =
        Module.finrank ℝ (LinearMap.ker N.linkageStoichSumMap) := e.finrank_eq
    have hdefLine : Module.finrank ℝ N.deficiencySubspace = 1 :=
      (N.deficiencyOne_iff_deficiency_eq_one).mp hδ
    rw [hdefLine, hcouplingLine] at hefin
    -- Boros linear reduction: positivity of the linear kinetic equation is not the missing
    -- step. There is a fixed nonzero deficiency mode `g`, and every scalar point `a • g`
    -- has a strictly positive kinetic preimage.
    obtain ⟨g, hgD, hg0, hgspan, hpositivePreimage⟩ :=
      N.exists_positiveKineticLine_of_weaklyReversible_deficiencyOne hwr hδ κ
    -- Strengthen pointwise positive preimages to one explicit affine positive section near 0.
    obtain ⟨b, z, ε, hε, hbpos, hbker, hz, hsection⟩ :=
      N.exists_positiveAffineKineticSection hwr κ hgD
    -- Keep the full per-linkage kernel freedom: every fibre `Aκ v = a • g` is exactly
    -- `a • z` plus one tree-kernel coefficient per linkage class, and every scalar fibre has a
    -- strictly positive point.  These are the variables needed to synchronize the class scales.
    have hfullFibre : ∀ {a : ℝ} {v : N.ComplexIdx → ℝ},
        N.kineticMap κ v = a • g ↔
          ∃ coeff : Quotient N.linkedSetoid → ℝ,
            v = N.deficiencyKineticFamily κ z a coeff := by
      intro a v
      exact N.mem_deficiencyKineticFamily_iff hwr κ hz
    have hpositiveFibre : ∀ a : ℝ, ∃ coeff : Quotient N.linkedSetoid → ℝ,
        ∀ c : N.ComplexIdx, 0 < (N.deficiencyKineticFamily κ z a coeff) c := by
      intro a
      exact N.exists_coeff_positive_deficiencyKineticFamily hwr κ hz a
    -- There is in fact a globally defined continuous positive section of every scalar fibre;
    -- its coefficient coordinates are explicit finite sums rather than a choice function.
    let vglob : ℝ → (N.ComplexIdx → ℝ) := fun a =>
      N.deficiencyKineticFamily κ z a (N.canonicalPositiveKineticCoeff κ z a)
    have hglobalPositiveSection : ∀ a c, 0 < vglob a c := by
      intro a c
      exact N.canonicalPositiveKineticFamily_pos hwr κ z a c
    have hglobalContinuous : Continuous vglob :=
      N.continuous_canonicalPositiveKineticFamily κ z
    have hglobalFibre : ∀ a, N.kineticMap κ (vglob a) = a • g := by
      intro a
      exact N.kineticMap_deficiencyKineticFamily hwr κ hz a _
    -- Strict kinetic entropy dissipation orders the logarithmic obstruction on the two
    -- nonzero sides of the deficiency line relative to every positive kernel reference.
    have hstrictSide : ∀ a, a ≠ 0 →
        (a > 0 → (∑ c, g c * Real.log (vglob a c)) <
          ∑ c, g c * Real.log (b c)) ∧
        (a < 0 → (∑ c, g c * Real.log (b c)) <
          ∑ c, g c * Real.log (vglob a c)) := by
      intro a ha
      exact N.deficiencyLogObstruction_strict_side_of_kernel κ hg0 ha
        (hglobalFibre a) (hglobalPositiveSection a) hbpos hbker
    -- Dually, the stoichiometric transpose row space is a hyperplane in the incidence
    -- transpose row space, so only one scalar logarithmic compatibility equation remains.
    have hrowGap := N.range_stoichTranspose_lt_range_incidenceTranspose_of_deficiencyOne hδ
    -- The scalar equation is now an exact characterization, modulo the unavoidable positive
    -- linkage-class scaling symmetry.  Thus no additional logarithmic equations are hidden in
    -- the Type-II branch.
    have hobsIff : ∀ {v : N.ComplexIdx → ℝ}, (∀ c, 0 < v c) →
        ((∑ c, g c * Real.log (v c)) = 0 ↔
          ∃ (x : Concentration S) (lambda : Quotient N.linkedSetoid → ℝ),
            x.Positive ∧ (∀ q, 0 < lambda q) ∧
            ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) := by
      intro v hvpos
      exact N.deficiencyOne_logObstruction_zero_iff_classScaledMonomial
        hδ hgD hg0 hgspan hvpos
    have htransportIff : ∀ {v : N.ComplexIdx → ℝ}, (∀ c, 0 < v c) →
        ((∑ c, g c * Real.log (v c)) = 0 ↔
          ∃ (x : Concentration S) (lambda : Quotient N.linkedSetoid → ℝ),
            x ∈ N.positiveCompatibilityClass x₀ ∧ (∀ q, 0 < lambda q) ∧
            ∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) := by
      intro v hvpos
      exact N.deficiencyOne_logObstruction_zero_iff_classScaledMonomial_in_positiveClass
        hδ hgD hg0 hgspan hvpos hx₀
    -- If the positive kernel fibre already has zero obstruction, its class-scaled monomial
    -- realization can be transported to the requested class. Since that realization is still
    -- in the kinetic kernel, it is a steady state without any class-scale synchronization.
    by_cases hObs : (∑ c, g c * Real.log (b c)) = 0
    · obtain ⟨x, lambda, hxclass, hlambda, hvx⟩ := (htransportIff hbpos).mp hObs
      exact ⟨x, hxclass,
        N.isMassActionSteadyState_of_kernel_classScaledMonomial κ hbker hlambda hvx⟩
    · -- This split only decides whether the kernel reference itself is a class-scaled
      -- monomial. A steady state may instead lie on a nonzero deficiency fibre, so the target
      -- is to find a positive fibre point whose class-scaled monomial realization has synchronized
      -- active linkage scales. The strict-side inequality for the chosen canonical section does
      -- not establish that simultaneous existence; a Brouwer/intersection argument is needed.
      have hrealize :
          ∃ (a : ℝ) (v : N.ComplexIdx → ℝ) (x : Concentration S)
            (lambda : Quotient N.linkedSetoid → ℝ),
            (∀ c, 0 < v c) ∧
            x ∈ N.positiveCompatibilityClass x₀ ∧
            (∀ q, 0 < lambda q) ∧
            (∀ c, v c = lambda (N.classOf c) * N.complexMonomialVector x c) ∧
            N.kineticMap κ v = a • g ∧
            ∃ L : ℝ, 0 < L ∧ ∀ q,
              N.complexMap (N.restrictToClass q (N.kineticMap κ v)) ≠ 0 →
                lambda q = L := by
        letI : Nonempty (Quotient N.linkedSetoid) :=
          N.nonemptyLinkageClass_of_deficiencyOne hδ
        obtain ⟨xsel, hxcont, hxpos, hxclass, _, hgraph⟩ :=
          N.exists_continuous_borosBirchGraph x₀ hx₀
        have hxpositiveClass : ∀ z, xsel z ∈ N.positiveCompatibilityClass x₀ := by
          intro z
          exact ⟨hxclass z, hxpos z⟩
        obtain ⟨kmin, kmax, ε, r, hkminpos, hkmin, hkmaxpos, hkmax,
            hε, hεone, hr0, hrmono, hrnonneg, hεres, hrstep⟩ :=
          N.exists_borosActiveRadiusSchedule hwr κ
        have hinward := N.borosBirchKineticProjectionField_strict_inward
          hwr κ xsel hxpos hgraph kmin kmax ε r hkminpos hkmin hkmaxpos hkmax
          hε hεone hr0 hrmono hrnonneg hεres hrstep
        obtain ⟨y, hyclass, hyss⟩ :=
          N.exists_borosBirchSteadyState_of_activeInward κ xsel hxcont hxpos hxpositiveClass
            r hinward
        exact N.exists_synchronized_classScale_realization_of_positiveSteadyState
          κ hyclass hyss hgspan
      exact N.exists_positiveSteadyState_of_synchronized_classScale_realization κ hgD hrealize
  · exact N.weaklyReversible_deficiencyOne_exists_positive_steadyState_of_sum_eq_one
      hwr hδ hsum κ x₀ hx₀

/-- Every positive class is nonempty in the positive steady-state set for a WR
`δ = 1` mass-action system. -/
def WeaklyReversibleDeficiencyOneExistence (N : Network S) : Prop :=
  ∀ (κ : N.RateConstants) (x₀ : Concentration S), x₀.Positive →
    ∃ x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x

/-- Structural theorem in packaged form. -/
theorem weaklyReversibleDeficiencyOneExistence
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne) :
    N.WeaklyReversibleDeficiencyOneExistence := by
  intro κ x₀ hx₀
  exact N.weaklyReversible_deficiencyOne_exists_positive_steadyState
    hwr hδ κ x₀ hx₀

/-- Under the additional classical Deficiency One Theorem hypotheses, the existence
result combines with uniqueness to recover exactly one positive steady state per class. -/
theorem weaklyReversible_deficiencyOne_existsUnique_of_hypotheses
    (N : Network S) (hwr : N.WeaklyReversible) (hδ : N.DeficiencyOne)
    (hDOT : N.DeficiencyOneHypotheses)
    (κ : N.RateConstants) (x₀ : Concentration S) (hx₀ : x₀.Positive) :
    ∃! x : Concentration S,
      x ∈ N.positiveCompatibilityClass x₀ ∧ N.IsMassActionSteadyState κ x := by
  rcases N.weaklyReversible_deficiencyOne_exists_positive_steadyState
    hwr hδ κ x₀ hx₀ with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact N.deficiencyOne_uniqueness hDOT κ x₀ hx₀ hy.1 hy.2 hx.1 hx.2

end Network
end CRNT
