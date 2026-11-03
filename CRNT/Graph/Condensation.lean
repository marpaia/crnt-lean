import CRNT.Decision.StrongLinkage
import CRNT.Decision.DirectedReachability
import Mathlib.Order.Preorder.Finite
import CRNT.Deficiency.DeficiencyOneHypotheses

/-!
# Condensation DAG of a reaction graph

The quotient of the reaction graph by strong linkage is acyclic.  Its sink vertices
are exactly the terminal strong linkage classes.  This is the graph-theoretic object
behind drainage, terminal-kernel decompositions, and the deficiency-one algorithm.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Strong linkage class of a complex index. -/
def strongClassOf (N : Network S) (c : N.ComplexIdx) :
    Quotient N.stronglyLinkedSetoid :=
  Quotient.mk'' c

@[simp] theorem strongClassOf_eq_iff (N : Network S) (c d : N.ComplexIdx) :
    N.strongClassOf c = N.strongClassOf d ↔ N.StronglyLinked c.val d.val := by
  change Quotient.mk N.stronglyLinkedSetoid c = Quotient.mk N.stronglyLinkedSetoid d ↔ _
  exact Quotient.eq_iff_equiv

/-- Directed edge in the SCC condensation graph.  Self edges are excluded. -/
def CondensationEdge (N : Network S)
    (σ τ : Quotient N.stronglyLinkedSetoid) : Prop :=
  σ ≠ τ ∧ ∃ r : N.R,
    N.strongClassOf (N.sourceIdx r) = σ ∧
    N.strongClassOf (N.targetIdx r) = τ

/-- Reachability in the condensation graph. -/
def CondensationReaches (N : Network S)
    (σ τ : Quotient N.stronglyLinkedSetoid) : Prop :=
  Relation.ReflTransGen N.CondensationEdge σ τ

/-- A reaction path projects to a condensation path. -/
theorem condensationReaches_of_reaches (N : Network S)
    {c d : N.ComplexIdx} (h : N.Reaches c.val d.val) :
    N.CondensationReaches (N.strongClassOf c) (N.strongClassOf d) := by
  have hd := (N.reaches_iff_reflTransGen_directedStep c d).1 h
  clear h
  induction hd with
  | refl => exact Relation.ReflTransGen.refl
  | @tail e f _ hef ih =>
      by_cases hcls : N.strongClassOf e = N.strongClassOf f
      · simpa [hcls] using ih
      · obtain ⟨r, hs, ht⟩ := hef
        have hsidx : N.sourceIdx r = e := Subtype.ext hs
        have htidx : N.targetIdx r = f := Subtype.ext ht
        apply Relation.ReflTransGen.tail ih
        refine ⟨hcls, r, ?_, ?_⟩
        · simpa [hsidx]
        · simpa [htidx]

/-- Conversely, a condensation path can be lifted to a reaction path between
representatives after moving within SCCs. -/
theorem reaches_of_condensationReaches (N : Network S)
    {σ τ : Quotient N.stronglyLinkedSetoid}
    (h : N.CondensationReaches σ τ) :
    ∀ c d : N.ComplexIdx,
      N.strongClassOf c = σ → N.strongClassOf d = τ →
      N.Reaches c.val d.val := by
  induction h with
  | refl =>
      intro c d hc hd
      have hcd : N.strongClassOf c = N.strongClassOf d := hc.trans hd.symm
      exact (N.strongClassOf_eq_iff c d).1 hcd |>.1
  | @tail ρ υ hpath hedge ih =>
      intro c d hc hd
      rcases hedge with ⟨_, r, hsrc, htgt⟩
      have hpre : N.Reaches c.val (N.sourceIdx r).val := ih c (N.sourceIdx r) hc hsrc
      have hstep : N.Reaches (N.sourceIdx r).val (N.targetIdx r).val := N.reaches_of_reaction r
      have htdClass : N.strongClassOf (N.targetIdx r) = N.strongClassOf d := htgt.trans hd.symm
      have htd : N.StronglyLinked (N.targetIdx r).val d.val :=
        (N.strongClassOf_eq_iff (N.targetIdx r) d).1 htdClass
      exact hpre.trans (hstep.trans htd.1)

/-- The condensation graph is antisymmetric under reachability. -/
theorem condensationReaches_antisymm (N : Network S)
    {σ τ : Quotient N.stronglyLinkedSetoid}
    (hστ : N.CondensationReaches σ τ)
    (hτσ : N.CondensationReaches τ σ) : σ = τ := by
  let c : N.ComplexIdx := Quotient.out σ
  let d : N.ComplexIdx := Quotient.out τ
  have hc : N.strongClassOf c = σ := by
    dsimp [strongClassOf, c]
    exact Quotient.out_eq σ
  have hd : N.strongClassOf d = τ := by
    dsimp [strongClassOf, d]
    exact Quotient.out_eq τ
  have hcd : N.Reaches c.val d.val := N.reaches_of_condensationReaches hστ c d hc hd
  have hdc : N.Reaches d.val c.val := N.reaches_of_condensationReaches hτσ d c hd hc
  have hsl : N.StronglyLinked c.val d.val := ⟨hcd, hdc⟩
  calc
    σ = N.strongClassOf c := hc.symm
    _ = N.strongClassOf d := (N.strongClassOf_eq_iff c d).2 hsl
    _ = τ := hd

/-- In particular the strict condensation relation has no directed cycles. -/
theorem not_condensationCycle (N : Network S)
    (σ : Quotient N.stronglyLinkedSetoid) :
    ¬ Relation.TransGen N.CondensationEdge σ σ := by
  intro h
  cases h with
  | single hedge => exact hedge.1 rfl
  | @tail ρ _ hprev hedge =>
      have hσρ : N.CondensationReaches σ ρ := hprev.to_reflTransGen
      have hρσ : N.CondensationReaches ρ σ := Relation.ReflTransGen.single hedge
      have heq : σ = ρ := N.condensationReaches_antisymm hσρ hρσ
      exact hedge.1 heq.symm

/-- A sink SCC has no outgoing condensation edge. -/
def IsCondensationSink (N : Network S)
    (σ : Quotient N.stronglyLinkedSetoid) : Prop :=
  ∀ τ, ¬ N.CondensationEdge σ τ

/-- Sink SCCs are exactly terminal strong linkage classes. -/
theorem isCondensationSink_iff_terminal (N : Network S)
    (σ : Quotient N.stronglyLinkedSetoid) :
    N.IsCondensationSink σ ↔ N.IsTerminalSLClass σ := by
  refine Quotient.inductionOn σ ?_
  intro c
  change N.IsCondensationSink (Quotient.mk N.stronglyLinkedSetoid c) ↔ N.IsTerminalSLC c.val
  constructor
  · intro hsink r hsrc
    have hsrcClass : N.strongClassOf (N.sourceIdx r) = Quotient.mk N.stronglyLinkedSetoid c := by
      apply (N.strongClassOf_eq_iff (N.sourceIdx r) c).2
      exact hsrc.symm
    have htgt : N.StronglyLinked c.val (N.targetIdx r).val := by
      by_contra hnot
      have hneq : Quotient.mk N.stronglyLinkedSetoid c ≠ N.strongClassOf (N.targetIdx r) := by
        intro heq
        have hsl : N.StronglyLinked c.val (N.targetIdx r).val := by
          apply (N.strongClassOf_eq_iff c (N.targetIdx r)).1
          dsimp [strongClassOf]
          exact heq
        exact hnot hsl
      have hedge : N.CondensationEdge (Quotient.mk N.stronglyLinkedSetoid c)
          (N.strongClassOf (N.targetIdx r)) := by
        refine ⟨hneq, r, ?_, rfl⟩
        exact hsrcClass
      exact (hsink _ hedge).elim
    exact htgt
  · intro hterm τ hedge
    rcases hedge with ⟨hne, r, hsrc, htgt⟩
    have hsrcSL : N.StronglyLinked c.val (N.sourceIdx r).val := by
      apply (N.strongClassOf_eq_iff c (N.sourceIdx r)).1
      dsimp [strongClassOf]
      exact hsrc.symm
    have htgtSL : N.StronglyLinked c.val (N.targetIdx r).val := hterm r hsrcSL
    have hclassT : Quotient.mk N.stronglyLinkedSetoid c = N.strongClassOf (N.targetIdx r) := by
      apply (N.strongClassOf_eq_iff c (N.targetIdx r)).2 htgtSL
    apply hne
    calc
      Quotient.mk N.stronglyLinkedSetoid c = N.strongClassOf (N.targetIdx r) := hclassT
      _ = τ := htgt

/-- Every SCC reaches a terminal SCC. -/
theorem exists_terminalStrongClass_reachable (N : Network S)
    (σ : Quotient N.stronglyLinkedSetoid) :
    ∃ τ : Quotient N.stronglyLinkedSetoid,
      N.IsTerminalSLClass τ ∧ N.CondensationReaches σ τ := by
  let Q := Quotient N.stronglyLinkedSetoid
  letI : LE Q := ⟨N.CondensationReaches⟩
  letI : IsTrans Q (· ≤ ·) :=
    ⟨fun _ _ _ hab hbc => Relation.ReflTransGen.trans hab hbc⟩
  let R : Set Q := {τ | N.CondensationReaches σ τ}
  have hfin : R.Finite := Set.toFinite R
  have hne : R.Nonempty := ⟨σ, Relation.ReflTransGen.refl⟩
  obtain ⟨τ, hτR, hmax⟩ := hfin.exists_maximal hne
  refine ⟨τ, ?_, hτR⟩
  apply (N.isCondensationSink_iff_terminal τ).1
  intro υ hedge
  have hτυ : N.CondensationReaches τ υ := Relation.ReflTransGen.single hedge
  have hσυ : N.CondensationReaches σ υ := hτR.trans hτυ
  have hυτ : N.CondensationReaches υ τ := hmax hσυ hτυ
  have heq : τ = υ := N.condensationReaches_antisymm hτυ hυτ
  exact hedge.1 heq

/-- Weak reversibility is equivalent to every SCC being a sink, hence to the
condensation graph having no edges. -/
theorem weaklyReversible_iff_allStrongClasses_terminal (N : Network S) :
    N.WeaklyReversible ↔
      ∀ σ : Quotient N.stronglyLinkedSetoid, N.IsTerminalSLClass σ := by
  constructor
  · intro hwr σ
    refine Quotient.inductionOn σ ?_
    intro c
    change N.IsTerminalSLC c.val
    intro r hsrc
    have hst : N.StronglyLinked (N.sourceIdx r).val (N.targetIdx r).val := by
      exact ⟨N.reaches_of_reaction r, hwr r⟩
    exact hsrc.trans hst
  · intro hall r
    have htermClass := hall (Quotient.mk N.stronglyLinkedSetoid (N.sourceIdx r))
    change N.IsTerminalSLC (N.sourceIdx r).val at htermClass
    have hsl := htermClass r (StronglyLinked.refl N (N.sourceIdx r).val)
    exact hsl.2

/-- Weak reversibility iff the SCC condensation has no strict edges. -/
theorem weaklyReversible_iff_noCondensationEdges (N : Network S) :
    N.WeaklyReversible ↔
      ∀ σ τ : Quotient N.stronglyLinkedSetoid,
        ¬ N.CondensationEdge σ τ := by
  rw [N.weaklyReversible_iff_allStrongClasses_terminal]
  constructor
  · intro h σ τ
    exact (N.isCondensationSink_iff_terminal σ).2 (h σ) τ
  · intro h σ
    exact (N.isCondensationSink_iff_terminal σ).1 (fun τ => h σ τ)

end Network
end CRNT
