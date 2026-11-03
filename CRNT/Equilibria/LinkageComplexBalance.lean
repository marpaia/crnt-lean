import CRNT.Equilibria.ComplexBalanced
import CRNT.Deficiency.LinkageDeficiency
import CRNT.Deficiency.KineticBlock

/-!
# Linkage-class decomposition of complex balance

Complex balance is local to linkage classes: no reaction joins two distinct linkage
classes, so the kinetic Laplacian is block diagonal.  This module packages that fact and
connects it to per-linkage tree constants and deficiency bookkeeping.
-/

namespace CRNT
namespace Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Inflow restricted to one linkage class. -/
noncomputable def linkageInflow (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (q : Quotient N.linkedSetoid) (c : N.ComplexIdx) : ℝ :=
  ∑ r : N.R,
    if N.classOf (N.sourceIdx r) = q ∧ N.targetIdx r = c
    then N.massActionRate κ r x else 0

/-- Outflow restricted to one linkage class. -/
noncomputable def linkageOutflow (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (q : Quotient N.linkedSetoid) (c : N.ComplexIdx) : ℝ :=
  ∑ r : N.R,
    if N.classOf (N.sourceIdx r) = q ∧ N.sourceIdx r = c
    then N.massActionRate κ r x else 0

/-- Complex balance inside one linkage class. -/
def IsComplexBalancedOnLinkage (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (q : Quotient N.linkedSetoid) : Prop :=
  ∀ c : N.ComplexIdx, N.classOf c = q →
    N.linkageInflow κ x q c = N.linkageOutflow κ x q c

/-- At a complex of its own linkage class, the restricted inflow is the global inflow: the
class constraint `classOf (sourceIdx r) = q` is automatic, because no reaction joins two
distinct linkage classes. -/
theorem linkageInflow_eq_inflow (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (c : N.ComplexIdx) :
    N.linkageInflow κ x (N.classOf c) c = N.inflow κ x c.val := by
  classical
  unfold linkageInflow inflow
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases htg : N.targetIdx r = c
  · have hcls : N.classOf (N.sourceIdx r) = N.classOf c := by
      rw [N.classOf_sourceIdx_eq_targetIdx, htg]
    have hval : (N.reaction r).target = c.val := congrArg Subtype.val htg
    simp [htg, hcls, hval]
  · have hval : ¬ ((N.reaction r).target = c.val) := fun h => htg (Subtype.ext h)
    simp [htg, hval]

/-- The outflow counterpart of `linkageInflow_eq_inflow`. -/
theorem linkageOutflow_eq_outflow (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) (c : N.ComplexIdx) :
    N.linkageOutflow κ x (N.classOf c) c = N.outflow κ x c.val := by
  classical
  unfold linkageOutflow outflow
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hsr : N.sourceIdx r = c
  · have hcls : N.classOf (N.sourceIdx r) = N.classOf c := by rw [hsr]
    have hval : (N.reaction r).source = c.val := congrArg Subtype.val hsr
    simp [hsr, hcls, hval]
  · have hval : ¬ ((N.reaction r).source = c.val) := fun h => hsr (Subtype.ext h)
    simp [hsr, hval]

/-- Global complex balance is exactly classwise complex balance. -/
theorem isComplexBalanced_iff_forall_linkage (N : Network S)
    (κ : N.RateConstants) (x : Concentration S) :
    N.IsComplexBalanced κ x ↔
      ∀ q : Quotient N.linkedSetoid, N.IsComplexBalancedOnLinkage κ x q := by
  classical
  constructor
  · intro h q c hcq
    -- restricted flows at `c` agree with the global ones, and `c` is a complex of `N`
    have hin := N.linkageInflow_eq_inflow κ x c
    have hout := N.linkageOutflow_eq_outflow κ x c
    rw [hcq] at hin hout
    rw [hin, hout]
    exact h c.val c.property
  · intro h c hc
    set ci : N.ComplexIdx := ⟨c, hc⟩ with hci
    have hin := N.linkageInflow_eq_inflow κ x ci
    have hout := N.linkageOutflow_eq_outflow κ x ci
    have := h (N.classOf ci) ci rfl
    rw [hin, hout] at this
    exact this

/-- Classwise balance may be checked independently on every linkage block of the kinetic
Laplacian. -/
theorem kineticMap_zero_iff_linkage_blocks_zero (N : Network S)
    (κ : N.RateConstants) (ψ : N.ComplexIdx → ℝ) :
    N.kineticMap κ ψ = 0 ↔
      ∀ q : Quotient N.linkedSetoid,
        ∀ c : N.ComplexIdx, N.classOf c = q → N.kineticMap κ ψ c = 0 := by
  constructor
  · intro h q c hc
    exact congrFun h c
  · intro h
    funext c
    exact h (N.classOf c) c rfl

/-- At deficiency zero, every linkage class is itself deficiency zero and complex balance
can therefore be established linkage-by-linkage. -/
theorem deficiencyZero_complexBalance_classwise (N : Network S)
    (hδ : N.DeficiencyZero) (κ : N.RateConstants) (x : Concentration S) :
    N.IsComplexBalanced κ x ↔
      ∀ q : Quotient N.linkedSetoid,
        N.linkageDeficiency q = 0 ∧ N.IsComplexBalancedOnLinkage κ x q := by
  constructor
  · intro h q
    exact ⟨N.linkageDeficiency_eq_zero_of_deficiencyZero hδ q,
      (N.isComplexBalanced_iff_forall_linkage κ x).1 h q⟩
  · intro h
    apply (N.isComplexBalanced_iff_forall_linkage κ x).2
    intro q
    exact (h q).2

end Network
end CRNT
