import CRNT.Geometry.Endotactic
import CRNT.Graph.WeakReversibility

/-!
# Endotactic geometry for global persistence claims

This module adds an audited strong-endotactic predicate based on directions that act
nontrivially on at least one reaction vector.  That is the finite-generator form of the
standard condition `w ∉ S^⊥`, where `S` is the stoichiometric subspace.

The pre-existing `StronglyEndotactic` predicate uses "nonconstant on source complexes" as
its trigger.  The two triggers need not agree for arbitrary networks, so the old definition is
left untouched for compatibility and the standard trigger is given a separate name.

For weakly reversible networks, every reaction target is again a reaction source (unless it is
the same complex, in which case the reaction itself supplies that source).  This is enough to
show that the legacy strong predicate implies the standard one.  We also prove the basic known
fact that weak reversibility implies endotacticity.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Linear `w`-value of an arbitrary complex. -/
def complexWValue (w : S → ℝ) (c : Complex S) : ℝ :=
  dotProduct w (exponentVector c)

@[simp] theorem wValue_eq_complexWValue_source (N : Network S) (w : S → ℝ) (r : N.R) :
    N.wValue w r = complexWValue w (N.reaction r).source :=
  rfl

/-- The reaction `w`-rate is target potential minus source potential. -/
theorem wRate_eq_complexWValue_sub (N : Network S) (w : S → ℝ) (r : N.R) :
    N.wRate w r =
      complexWValue w (N.reaction r).target - complexWValue w (N.reaction r).source := by
  simp only [wRate, dotProduct, reactionVector_apply, complexWValue, exponentVector, mul_sub,
    Finset.sum_sub_distrib]

/-- A direction is stoichiometrically active when it does not annihilate every reaction vector.
Since the stoichiometric subspace is spanned by those vectors, this is the finite-generator form
of `w ∉ S^⊥`. -/
def StoichActiveDirection (N : Network S) (w : S → ℝ) : Prop :=
  ∃ r : N.R, N.wRate w r ≠ 0

/-- Strong endotacticity with the standard stoichiometric trigger. -/
def StronglyEndotacticStd (N : Network S) : Prop :=
  N.Endotactic ∧
    ∀ w : S → ℝ, N.StoichActiveDirection w →
      ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0

/-- Standard strong endotacticity implies ordinary endotacticity. -/
theorem StronglyEndotacticStd.endotactic {N : Network S} (h : N.StronglyEndotacticStd) :
    N.Endotactic :=
  h.1

/-- In a weakly reversible network, the target of every reaction occurs as the source of
some reaction. -/
theorem WeaklyReversible.exists_source_eq_target {N : Network S} (hwr : N.WeaklyReversible)
    (r : N.R) : ∃ r' : N.R, (N.reaction r').source = (N.reaction r).target := by
  rcases Relation.ReflTransGen.cases_head (hwr r) with heq | ⟨e, hedge, _⟩
  · exact ⟨r, heq.symm⟩
  · obtain ⟨r', hs, _ht⟩ := hedge
    exact ⟨r', hs⟩

/-- **Weak reversibility implies endotacticity.**  A reaction from a maximal source cannot
point to larger `w`-value: weak reversibility makes its target the source of a return reaction,
which is bounded by maximality. -/
theorem WeaklyReversible.endotactic {N : Network S} (hwr : N.WeaklyReversible) :
    N.Endotactic := by
  intro w r hmax
  obtain ⟨r', hr'⟩ := hwr.exists_source_eq_target r
  have hle : N.wValue w r' ≤ N.wValue w r := hmax r'
  rw [wValue_eq_complexWValue_source, hr'] at hle
  rw [wValue_eq_complexWValue_source] at hle
  rw [N.wRate_eq_complexWValue_sub w r]
  linarith

/-- For weakly reversible networks, the legacy source-nonconstant trigger is strong enough to
cover every stoichiometrically active direction.  This provides a compatibility bridge while
keeping the standard definition explicit for new global theorems. -/
theorem StronglyEndotactic.toStd_of_weaklyReversible {N : Network S}
    (h : N.StronglyEndotactic) (hwr : N.WeaklyReversible) : N.StronglyEndotacticStd := by
  refine ⟨h.endotactic, ?_⟩
  intro w hactive
  obtain ⟨r, hrne⟩ := hactive
  obtain ⟨r', hr'⟩ := hwr.exists_source_eq_target r
  have hncon : ∃ r₁ r₂ : N.R, N.wValue w r₁ ≠ N.wValue w r₂ := by
    refine ⟨r', r, ?_⟩
    intro heq
    have hpot : complexWValue w (N.reaction r).target =
        complexWValue w (N.reaction r).source := by
      calc
        complexWValue w (N.reaction r).target
            = N.wValue w r' := by rw [wValue_eq_complexWValue_source, hr']
        _ = N.wValue w r := heq
        _ = complexWValue w (N.reaction r).source := wValue_eq_complexWValue_source N w r
    apply hrne
    rw [N.wRate_eq_complexWValue_sub w r, hpot, sub_self]
  exact h.2 w hncon

end Network
end CRNT
