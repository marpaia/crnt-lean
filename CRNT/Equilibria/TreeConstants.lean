import CRNT.Deficiency.KernelDimension
import CRNT.Graph.LinkageClass
import CRNT.Decision.Reachability
import CRNT.Kinetics.MassAction
import Mathlib.Data.Finset.Card

/-!
# Tree constants and the directed Matrix--Tree theorem

For a complex `y`, its tree constant is the sum of the products of rate constants over
all directed spanning trees of the linkage class of `y` oriented toward `y`.
These are the classical Feinberg/Horn--Jackson tree constants.

The combinatorial objects are defined explicitly here.  The single hard linear-algebraic
bridge -- the directed Matrix--Tree theorem for the kinetic Laplacian -- is isolated as
`treeConstant_kineticKernel`; all standard CRNT consequences are derived from it.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Membership of a complex index in the linkage class of `root`. -/
def SameLinkage (N : Network S) (root c : N.ComplexIdx) : Prop :=
  N.Linked root.1 c.1

/-- A directed edge using only reactions selected by `T`. -/
def SelectedEdge (N : Network S) (T : Finset N.R) (c d : N.ComplexIdx) : Prop :=
  ∃ r : N.R, r ∈ T ∧ N.sourceIdx r = c ∧ N.targetIdx r = d

/-- Directed reachability inside a selected reaction set. -/
def SelectedReaches (N : Network S) (T : Finset N.R) (c d : N.ComplexIdx) : Prop :=
  Relation.ReflTransGen (N.SelectedEdge T) c d

/-- A directed spanning in-arborescence of the linkage class of `root`.

Every non-root complex of the class has exactly one selected outgoing reaction, the root
has none, no selected reaction comes from outside the class, and every class vertex
reaches the root through selected reactions.  This orientation matches the standard CRNT
tree constant convention. -/
def IsRootedInArborescence (N : Network S) (root : N.ComplexIdx) (T : Finset N.R) : Prop :=
  (∀ c : N.ComplexIdx, N.SameLinkage root c → c ≠ root →
    ∃! r : N.R, r ∈ T ∧ N.sourceIdx r = c) ∧
  (∀ r : N.R, r ∈ T → N.sourceIdx r ≠ root) ∧
  (∀ r : N.R, r ∈ T → N.SameLinkage root (N.sourceIdx r)) ∧
  (∀ c : N.ComplexIdx, N.SameLinkage root c → N.SelectedReaches T c root)

/-- The finite set of rooted in-arborescences of a linkage class. -/
noncomputable def rootedInArborescences (N : Network S) (root : N.ComplexIdx) :
    Finset (Finset N.R) := by
  classical
  exact Finset.univ.filter (N.IsRootedInArborescence root)

@[simp] theorem mem_rootedInArborescences_iff (N : Network S) (root : N.ComplexIdx)
    (T : Finset N.R) :
    T ∈ N.rootedInArborescences root ↔ N.IsRootedInArborescence root T := by
  classical
  simp [rootedInArborescences]

/-- Product of rate constants along a selected reaction set. -/
def treeWeight (N : Network S) (κ : N.RateConstants) (T : Finset N.R) : ℝ :=
  ∏ r ∈ T, κ.k r

/-- Every tree weight is strictly positive. -/
theorem treeWeight_pos (N : Network S) (κ : N.RateConstants) (T : Finset N.R) :
    0 < N.treeWeight κ T := by
  unfold treeWeight
  exact Finset.prod_pos fun r _ => κ.positive r

/-- The tree constant rooted at a complex. -/
noncomputable def treeConstant (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) : ℝ :=
  ∑ T ∈ N.rootedInArborescences root, N.treeWeight κ T

/-- Tree constants are nonnegative. -/
theorem treeConstant_nonneg (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) : 0 ≤ N.treeConstant κ root := by
  classical
  unfold treeConstant
  exact Finset.sum_nonneg fun T _ => (N.treeWeight_pos κ T).le

/-- Existence of one rooted arborescence makes the corresponding tree constant positive. -/
theorem treeConstant_pos_of_exists_arborescence (N : Network S) (κ : N.RateConstants)
    (root : N.ComplexIdx) (hex : ∃ T, N.IsRootedInArborescence root T) :
    0 < N.treeConstant κ root := by
  classical
  obtain ⟨T, hT⟩ := hex
  have hmem : T ∈ N.rootedInArborescences root :=
    (N.mem_rootedInArborescences_iff root T).2 hT
  have hpos := N.treeWeight_pos κ T
  unfold treeConstant
  exact Finset.sum_pos' (fun U _ => (N.treeWeight_pos κ U).le)
    ⟨T, by simpa using hmem, hpos⟩

/-- Vector of tree constants over the finite complex set. -/
noncomputable def treeConstantVector (N : Network S) (κ : N.RateConstants) :
    N.ComplexIdx → ℝ :=
  fun c => N.treeConstant κ c

/-- Along the selected path from a non-root class vertex to the root, some selected reaction
enters the root.  This is the inverse-edge existence lemma used by the root-rotation proof of the
directed Matrix--Tree theorem. -/
theorem IsRootedInArborescence.exists_selected_reaction_into_root
    {N : Network S} {root c : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hc : N.SameLinkage root c) (hne : c ≠ root) :
    ∃ r : N.R, r ∈ T ∧ N.targetIdx r = root := by
  have hreach : N.SelectedReaches T c root := hT.2.2.2 c hc
  revert hne
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hne
      exact (hne rfl).elim
  | @head a b hab _ ih =>
      intro hne
      rcases hab with ⟨r, hrT, hsource, htarget⟩
      have hbLink : N.SameLinkage root b := by
        have hsrcLink := hT.2.2.1 r hrT
        unfold SameLinkage at hsrcLink ⊢
        have hrLink : N.Linked (N.sourceIdx r).1 (N.targetIdx r).1 := by
          simpa [sourceIdx, targetIdx] using N.linked_of_reaction r
        rw [hsource] at hsrcLink
        rw [hsource, htarget] at hrLink
        exact Network.Linked.trans hsrcLink hrLink
      by_cases hb : b = root
      · exact ⟨r, hrT, htarget.trans hb⟩
      · exact ih hbLink hb

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

lemma IsRootedInArborescence.selectedEdge_rightUnique
    {N : Network S} {root : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T) :
    Relator.RightUnique (N.SelectedEdge T) := by
  intro a b c hab hac
  rcases hab with ⟨r, hrT, hrs, hrt⟩
  rcases hac with ⟨q, hqT, hqs, hqt⟩
  have haLink : N.SameLinkage root a := by
    have h := hT.2.2.1 r hrT
    simpa [hrs] using h
  have hane : a ≠ root := by
    intro ha
    have hno := hT.2.1 r hrT
    exact hno (hrs.trans ha)
  obtain ⟨p, hp, huniq⟩ := hT.1 a haLink hane
  have hrp : r = p := huniq r ⟨hrT, hrs⟩
  have hqp : q = p := huniq q ⟨hqT, hqs⟩
  rw [hrp] at hrt
  rw [hqp] at hqt
  exact hrt.symm.trans hqt

lemma IsRootedInArborescence.root_reaches_eq
    {N : Network S} {root x : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (h : N.SelectedReaches T root x) : x = root := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => rfl
  | @head a b hab hrest ih =>
      rcases hab with ⟨r, hrT, hrs, hrt⟩
      exfalso
      exact (hT.2.1 r hrT) hrs

lemma IsRootedInArborescence.reaction_not_mem_of_source_root
    {N : Network S} {root : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    {r : N.R} (hr : N.sourceIdx r = root) : r ∉ T := by
  intro hrT
  exact hT.2.1 r hrT hr

lemma IsRootedInArborescence.edge_source_link
    {N : Network S} {root : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    {a b : N.ComplexIdx} (h : N.SelectedEdge T a b) :
    N.SameLinkage root a := by
  rcases h with ⟨r, hrT, hrs, _⟩
  have hs := hT.2.2.1 r hrT
  simpa [hrs] using hs

lemma IsRootedInArborescence.forward_swap_isRooted
    {N : Network S} {old new : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence old T)
    {r q : N.R}
    (hrsource : N.sourceIdx r = old)
    (hrtarget : N.targetIdx r = new)
    (hne : new ≠ old)
    (hqT : q ∈ T)
    (hqsource : N.sourceIdx q = new) :
    N.IsRootedInArborescence new (insert r (T.erase q)) := by
  have hrnot : r ∉ T := hT.reaction_not_mem_of_source_root hrsource
  have hrq : r ≠ q := by
    intro heq
    subst q
    exact hrnot hqT
  have hnewLinkOld : N.SameLinkage old new := by
    unfold SameLinkage
    rw [← hrsource, ← hrtarget]
    simpa [sourceIdx, targetIdx] using N.linked_of_reaction r
  have hOldLinkNew : N.SameLinkage new old := by
    exact Network.Linked.symm hnewLinkOld
  have hq_unique : ∀ q' : N.R, q' ∈ T ∧ N.sourceIdx q' = new → q' = q := by
    obtain ⟨p, hp, hu⟩ := hT.1 new hnewLinkOld hne
    intro q' hq'
    exact (hu q' hq').trans (hu q ⟨hqT, hqsource⟩).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxlink hxne
    have hxOld : N.SameLinkage old x := by
      exact Network.Linked.trans hnewLinkOld hxlink
    by_cases hxold : x = old
    · subst x
      refine ⟨r, ?_, ?_⟩
      · constructor
        · exact Finset.mem_insert_self r (T.erase q)
        · exact hrsource
      · intro p hp
        rcases hp with ⟨hpU, hpsrc⟩
        rcases Finset.mem_insert.mp hpU with hpr | hpErase
        · exact hpr
        · have hpT : p ∈ T := Finset.mem_of_mem_erase hpErase
          have hno := hT.2.1 p hpT
          exact False.elim (hno hpsrc)
    · obtain ⟨p, hp, hu⟩ := hT.1 x hxOld hxold
      have hpne : p ≠ q := by
        intro hpq
        subst p
        exact hxne (hp.2.symm.trans hqsource)
      refine ⟨p, ?_, ?_⟩
      · constructor
        · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hpne, hp.1⟩))
        · exact hp.2
      · intro p' hp'
        rcases hp' with ⟨hp'U, hp'src⟩
        rcases Finset.mem_insert.mp hp'U with hpr | hpErase
        · subst p'
          exact False.elim (hxold (hrsource.symm.trans hp'src).symm)
        · exact hu p' ⟨Finset.mem_of_mem_erase hpErase, hp'src⟩
  · intro p hpU
    rcases Finset.mem_insert.mp hpU with hpr | hpErase
    · subst p
      exact hrsource.trans_ne hne.symm
    · have hpT := Finset.mem_of_mem_erase hpErase
      intro hpsrc
      have hpq : p = q := hq_unique p ⟨hpT, hpsrc⟩
      subst p
      exact (Finset.notMem_erase q T) hpErase
  · intro p hpU
    rcases Finset.mem_insert.mp hpU with hpr | hpErase
    · subst p
      simpa [hrsource] using hOldLinkNew
    · have hpT := Finset.mem_of_mem_erase hpErase
      have hpOld := hT.2.2.1 p hpT
      exact Network.Linked.trans hOldLinkNew hpOld
  · intro x hxlink
    have hxOld : N.SameLinkage old x := Network.Linked.trans hnewLinkOld hxlink
    have hreachOld : N.SelectedReaches T x old := hT.2.2.2 x hxOld
    have holdNew : N.SelectedEdge (insert r (T.erase q)) old new := by
      exact ⟨r, Finset.mem_insert_self r (T.erase q), hrsource, hrtarget⟩
    induction hreachOld using Relation.ReflTransGen.head_induction_on with
    | refl => exact Relation.ReflTransGen.single holdNew
    | @head a b hab hrest ih =>
        by_cases ha : a = new
        · subst a
          exact Relation.ReflTransGen.refl
        · rcases hab with ⟨p, hpT, hpsrc, hptgt⟩
          have hpne : p ≠ q := by
            intro hpq
            subst p
            exact ha (hpsrc.symm.trans hqsource)
          have habU : N.SelectedEdge (insert r (T.erase q)) a b :=
            ⟨p, Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hpne, hpT⟩)), hpsrc, hptgt⟩
          have hbOld : N.SameLinkage old b := by
            have hsrcLink := hT.2.2.1 p hpT
            have hpLink : N.Linked (N.sourceIdx p).1 (N.targetIdx p).1 := by
              simpa [sourceIdx, targetIdx] using N.linked_of_reaction p
            rw [hpsrc] at hsrcLink
            rw [hpsrc, hptgt] at hpLink
            exact Network.Linked.trans hsrcLink hpLink
          have hbNew : N.SameLinkage new b :=
            Network.Linked.trans hOldLinkNew hbOld
          exact Relation.ReflTransGen.head habU (ih hbNew hbOld)

lemma treeWeight_forward_swap
    {N : Network S} (κ : N.RateConstants) {T : Finset N.R} {r q : N.R}
    (hrnot : r ∉ T) (hqT : q ∈ T) :
    κ.k r * N.treeWeight κ T =
      κ.k q * N.treeWeight κ (insert r (T.erase q)) := by
  unfold treeWeight
  have hrq : r ≠ q := by
    intro h
    subst q
    exact hrnot hqT
  rw [Finset.prod_insert]
  · rw [← Finset.mul_prod_erase T (fun z => κ.k z) hqT]
    ring
  · simpa [Finset.mem_erase, hrq, hrnot]



open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

lemma selectedReaches_erase_of_not_reaches_source
    {N : Network S} {T : Finset N.R} {r : N.R} {x y : N.ComplexIdx}
    (h : N.SelectedReaches T x y)
    (hnot : ¬ N.SelectedReaches T x (N.sourceIdx r)) :
    N.SelectedReaches (T.erase r) x y := by
  revert hnot
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro _
      exact Relation.ReflTransGen.refl
  | @head a b hab hrest ih =>
      intro hnot
      rcases hab with ⟨p, hpT, hps, hpt⟩
      have hpne : p ≠ r := by
        intro hpr
        subst p
        apply hnot
        rw [hps]
        exact Relation.ReflTransGen.refl
      have hab' : N.SelectedEdge (T.erase r) a b :=
        ⟨p, Finset.mem_erase.mpr ⟨hpne, hpT⟩, hps, hpt⟩
      have hnotb : ¬ N.SelectedReaches T b (N.sourceIdx r) := by
        intro hb
        apply hnot
        exact Relation.ReflTransGen.head ⟨p, hpT, hps, hpt⟩ hb
      exact Relation.ReflTransGen.head hab' (ih hnotb)

lemma IsRootedInArborescence.selectedReaches_erase_to_source
    {N : Network S} {root : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    {r : N.R} (hrT : r ∈ T) (hrt : N.targetIdx r = root)
    {x : N.ComplexIdx}
    (h : N.SelectedReaches T x (N.sourceIdx r)) :
    N.SelectedReaches (T.erase r) x (N.sourceIdx r) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | @head a b hab hrest ih =>
      rcases hab with ⟨p, hpT, hps, hpt⟩
      have hpne : p ≠ r := by
        intro hpr
        subst p
        have hbroot : b = root := hpt.symm.trans hrt
        rw [hbroot] at hrest
        have hsroot : N.sourceIdx r = root := hT.root_reaches_eq hrest
        exact (hT.2.1 r hrT) hsroot
      exact Relation.ReflTransGen.head
        ⟨p, Finset.mem_erase.mpr ⟨hpne, hpT⟩, hps, hpt⟩ ih

lemma IsRootedInArborescence.inverse_swap_isRooted
    {N : Network S} {new : N.ComplexIdx} {U : Finset N.R}
    (hU : N.IsRootedInArborescence new U)
    {q r : N.R}
    (hqsource : N.sourceIdx q = new)
    (hqtarget_ne : N.targetIdx q ≠ new)
    (hrU : r ∈ U)
    (hrtarget : N.targetIdx r = new)
    (hprefix : N.SelectedReaches U (N.targetIdx q) (N.sourceIdx r)) :
    N.IsRootedInArborescence (N.sourceIdx r) (insert q (U.erase r)) := by
  let old := N.sourceIdx r
  have holdne : old ≠ new := hU.2.1 r hrU
  have hqnot : q ∉ U := hU.reaction_not_mem_of_source_root hqsource
  have hqr : q ≠ r := by
    intro h
    subst q
    exact hqnot hrU
  have holdLinkNew : N.SameLinkage old new := by
    unfold SameLinkage
    rw [← hrtarget]
    simpa [old, sourceIdx, targetIdx] using N.linked_of_reaction r
  have hNewLinkOld : N.SameLinkage new old := Network.Linked.symm holdLinkNew
  have hr_unique : ∀ p : N.R, p ∈ U ∧ N.sourceIdx p = old → p = r := by
    have holdNew : N.SameLinkage new old := hNewLinkOld
    obtain ⟨p, hp, hu⟩ := hU.1 old holdNew holdne
    intro p' hp'
    exact (hu p' hp').trans (hu r ⟨hrU, rfl⟩).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hxlink hxne
    have hxNew : N.SameLinkage new x := Network.Linked.trans hNewLinkOld hxlink
    by_cases hxnew : x = new
    · subst x
      refine ⟨q, ?_, ?_⟩
      · exact ⟨Finset.mem_insert_self q (U.erase r), hqsource⟩
      · intro p hp
        rcases hp with ⟨hpT, hps⟩
        rcases Finset.mem_insert.mp hpT with hpq | hpErase
        · exact hpq
        · have hpU := Finset.mem_of_mem_erase hpErase
          exact False.elim ((hU.2.1 p hpU) hps)
    · obtain ⟨p, hp, hu⟩ := hU.1 x hxNew hxnew
      have hpne : p ≠ r := by
        intro hpr
        subst p
        exact hxne hp.2.symm
      refine ⟨p, ?_, ?_⟩
      · exact ⟨Finset.mem_insert.mpr (Or.inr (Finset.mem_erase.mpr ⟨hpne, hp.1⟩)), hp.2⟩
      · intro p' hp'
        rcases hp' with ⟨hp'T, hp'src⟩
        rcases Finset.mem_insert.mp hp'T with hpq | hpErase
        · subst p'
          exact False.elim (hxnew (hqsource.symm.trans hp'src).symm)
        · exact hu p' ⟨Finset.mem_of_mem_erase hpErase, hp'src⟩
  · intro p hpT
    rcases Finset.mem_insert.mp hpT with hpq | hpErase
    · subst p
      intro hqold
      exact holdne (hqsource.symm.trans hqold).symm
    · have hpU := Finset.mem_of_mem_erase hpErase
      intro hpsold
      have hpr : p = r := hr_unique p ⟨hpU, hpsold⟩
      subst p
      exact (Finset.notMem_erase r U) hpErase
  · intro p hpT
    rcases Finset.mem_insert.mp hpT with hpq | hpErase
    · subst p
      rw [hqsource]
      exact holdLinkNew
    · have hpU := Finset.mem_of_mem_erase hpErase
      have hpNew := hU.2.2.1 p hpU
      exact Network.Linked.trans holdLinkNew hpNew
  · intro x hxlink
    by_cases hxreach : N.SelectedReaches U x old
    · have hkeep := hU.selectedReaches_erase_to_source hrU hrtarget hxreach
      exact (Relation.ReflTransGen.mono
        (r := N.SelectedEdge (U.erase r))
        (p := N.SelectedEdge (insert q (U.erase r))) (by
        intro a b hab
        rcases hab with ⟨p, hp, hs, ht⟩
        exact ⟨p, Finset.mem_insert.mpr (Or.inr hp), hs, ht⟩))
        x (N.sourceIdx r) hkeep
    · have hxNew : N.SameLinkage new x := Network.Linked.trans hNewLinkOld hxlink
      have hxroot : N.SelectedReaches U x new := hU.2.2.2 x hxNew
      have hxroot' : N.SelectedReaches (U.erase r) x new :=
        selectedReaches_erase_of_not_reaches_source hxroot hxreach
      have hprefix' : N.SelectedReaches (U.erase r) (N.targetIdx q) old :=
        hU.selectedReaches_erase_to_source hrU hrtarget hprefix
      have hqEdge : N.SelectedEdge (insert q (U.erase r)) new (N.targetIdx q) :=
        ⟨q, Finset.mem_insert_self q (U.erase r), hqsource, rfl⟩
      have liftErase : ∀ a b, N.SelectedEdge (U.erase r) a b →
          N.SelectedEdge (insert q (U.erase r)) a b := by
        intro a b hab
        rcases hab with ⟨p, hp, hs, ht⟩
        exact ⟨p, Finset.mem_insert.mpr (Or.inr hp), hs, ht⟩
      have hxrootT : N.SelectedReaches (insert q (U.erase r)) x new := by
        exact (Relation.ReflTransGen.mono
          (r := N.SelectedEdge (U.erase r))
          (p := N.SelectedEdge (insert q (U.erase r))) liftErase)
          x new hxroot'
      have hprefixT : N.SelectedReaches (insert q (U.erase r)) (N.targetIdx q) old := by
        exact (Relation.ReflTransGen.mono
          (r := N.SelectedEdge (U.erase r))
          (p := N.SelectedEdge (insert q (U.erase r))) liftErase)
          (N.targetIdx q) old hprefix'
      exact hxrootT.trans (Relation.ReflTransGen.head hqEdge hprefixT)



variable {S : Type} [DecidableEq S] [Fintype S]

lemma IsRootedInArborescence.reachable_from_preRoot_eq_source
    {N : Network S} {root : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    {r : N.R} (hrT : r ∈ T) (hrt : N.targetIdx r = root)
    {x : N.ComplexIdx} (hxroot : x ≠ root)
    (hreach : N.SelectedReaches T (N.sourceIdx r) x) :
    x = N.sourceIdx r := by
  rcases Relation.ReflTransGen.cases_head hreach with hEq | ⟨b, hab, hbx⟩
  · exact hEq.symm
  · have hrEdge : N.SelectedEdge T (N.sourceIdx r) root := ⟨r, hrT, rfl, hrt⟩
    have hbroot : b = root := hT.selectedEdge_rightUnique hab hrEdge
    rw [hbroot] at hbx
    exact False.elim (hxroot (hT.root_reaches_eq hbx))

lemma IsRootedInArborescence.last_entering_reaction_unique
    {N : Network S} {root d : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    {r s : N.R}
    (hrT : r ∈ T) (hrt : N.targetIdx r = root)
    (hsT : s ∈ T) (hst : N.targetIdx s = root)
    (hdr : N.SelectedReaches T d (N.sourceIdx r))
    (hds : N.SelectedReaches T d (N.sourceIdx s)) : r = s := by
  have hrsne : N.sourceIdx r ≠ root := hT.2.1 r hrT
  have hssne : N.sourceIdx s ≠ root := hT.2.1 s hsT
  have hsrc : N.sourceIdx r = N.sourceIdx s := by
    rcases Relation.ReflTransGen.total_of_right_unique hT.selectedEdge_rightUnique hdr hds with hrs | hsr
    · exact (hT.reachable_from_preRoot_eq_source hrT hrt hssne hrs).symm
    · exact hT.reachable_from_preRoot_eq_source hsT hst hrsne hsr
  have hrLink : N.SameLinkage root (N.sourceIdx r) := hT.2.2.1 r hrT
  obtain ⟨p, hp, hu⟩ := hT.1 (N.sourceIdx r) hrLink hrsne
  exact (hu r ⟨hrT, rfl⟩).trans (hu s ⟨hsT, hsrc.symm⟩).symm

lemma IsRootedInArborescence.exists_last_entering_reaction
    {N : Network S} {root d : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hdLink : N.SameLinkage root d) (hdne : d ≠ root) :
    ∃ r : N.R, r ∈ T ∧ N.targetIdx r = root ∧
      N.SelectedReaches T d (N.sourceIdx r) := by
  have hreach : N.SelectedReaches T d root := hT.2.2.2 d hdLink
  rcases Relation.ReflTransGen.cases_tail hreach with hEq | ⟨a, hda, haroot⟩
  · exact False.elim (hdne hEq.symm)
  · rcases haroot with ⟨r, hrT, hrs, hrt⟩
    refine ⟨r, hrT, hrt, ?_⟩
    rw [← hrs] at hda
    exact hda



variable {S : Type} [DecidableEq S] [Fintype S]

lemma IsRootedInArborescence.no_selected_cycle
    {N : Network S} {root x : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hxroot : N.SelectedReaches T x root) :
    ¬ Relation.TransGen (N.SelectedEdge T) x x := by
  induction hxroot using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro hcycle
      rcases Relation.TransGen.head'_iff.mp hcycle with ⟨b, hrootb, _⟩
      rcases hrootb with ⟨r, hrT, hrs, _⟩
      exact (hT.2.1 r hrT) hrs
  | @head a b hab hrest ih =>
      intro hcycle
      rcases Relation.TransGen.head'_iff.mp hcycle with ⟨d, had, hda⟩
      have hdb : d = b := hT.selectedEdge_rightUnique had hab
      subst d
      exact ih (Relation.TransGen.tail' hda hab)

lemma IsRootedInArborescence.target_not_reaches_source
    {N : Network S} {root : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    {q : N.R} (hqT : q ∈ T) :
    ¬ N.SelectedReaches T (N.targetIdx q) (N.sourceIdx q) := by
  intro hback
  have hsrcLink := hT.2.2.1 q hqT
  have hroot := hT.2.2.2 (N.sourceIdx q) hsrcLink
  have hedge : N.SelectedEdge T (N.sourceIdx q) (N.targetIdx q) :=
    ⟨q, hqT, rfl, rfl⟩
  exact hT.no_selected_cycle hroot (Relation.TransGen.head' hedge hback)



variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable def rootedOutgoingReaction
    {N : Network S} {root c : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hc : N.SameLinkage root c) (hne : c ≠ root) : N.R :=
  Classical.choose (ExistsUnique.exists (hT.1 c hc hne))

lemma rootedOutgoingReaction_spec
    {N : Network S} {root c : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hc : N.SameLinkage root c) (hne : c ≠ root) :
    N.rootedOutgoingReaction hT hc hne ∈ T ∧
      N.sourceIdx (N.rootedOutgoingReaction hT hc hne) = c := by
  exact Classical.choose_spec (ExistsUnique.exists (hT.1 c hc hne))

lemma rootedOutgoingReaction_eq
    {N : Network S} {root c : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hc : N.SameLinkage root c) (hne : c ≠ root)
    {q : N.R} (hqT : q ∈ T) (hqsrc : N.sourceIdx q = c) :
    N.rootedOutgoingReaction hT hc hne = q := by
  obtain ⟨p, hp, hu⟩ := hT.1 c hc hne
  exact (hu _ (N.rootedOutgoingReaction_spec hT hc hne)).trans
    (hu q ⟨hqT, hqsrc⟩).symm

noncomputable def lastEnteringReaction
    {N : Network S} {root d : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hdLink : N.SameLinkage root d) (hdne : d ≠ root) : N.R :=
  Classical.choose (hT.exists_last_entering_reaction hdLink hdne)

lemma lastEnteringReaction_spec
    {N : Network S} {root d : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hdLink : N.SameLinkage root d) (hdne : d ≠ root) :
    N.lastEnteringReaction hT hdLink hdne ∈ T ∧
      N.targetIdx (N.lastEnteringReaction hT hdLink hdne) = root ∧
      N.SelectedReaches T d (N.sourceIdx (N.lastEnteringReaction hT hdLink hdne)) := by
  exact Classical.choose_spec (hT.exists_last_entering_reaction hdLink hdne)

lemma lastEnteringReaction_eq
    {N : Network S} {root d : N.ComplexIdx} {T : Finset N.R}
    (hT : N.IsRootedInArborescence root T)
    (hdLink : N.SameLinkage root d) (hdne : d ≠ root)
    {r : N.R} (hrT : r ∈ T) (hrt : N.targetIdx r = root)
    (hdr : N.SelectedReaches T d (N.sourceIdx r)) :
    N.lastEnteringReaction hT hdLink hdne = r := by
  rcases N.lastEnteringReaction_spec hT hdLink hdne with ⟨hpT, hpt, hdp⟩
  exact hT.last_entering_reaction_unique hpT hpt hrT hrt hdp hdr



variable {S : Type} [DecidableEq S] [Fintype S]

/-- Incoming reaction decorated by a tree rooted at its source. -/
def IncomingTreeDecoration (N : Network S) (c : N.ComplexIdx) :=
  {p : N.R × Finset N.R //
    N.targetIdx p.1 = c ∧ N.IsRootedInArborescence (N.sourceIdx p.1) p.2}

/-- Outgoing reaction decorated by a tree rooted at `c`. -/
def OutgoingTreeDecoration (N : Network S) (c : N.ComplexIdx) :=
  {p : N.R × Finset N.R //
    N.sourceIdx p.1 = c ∧ N.IsRootedInArborescence c p.2}

noncomputable instance instFintypeIncomingTreeDecoration (N : Network S) (c : N.ComplexIdx) :
    Fintype (N.IncomingTreeDecoration c) := by
  classical
  exact Subtype.fintype _

noncomputable instance instFintypeOutgoingTreeDecoration (N : Network S) (c : N.ComplexIdx) :
    Fintype (N.OutgoingTreeDecoration c) := by
  classical
  exact Subtype.fintype _

lemma reaction_sameLinkage (N : Network S) (r : N.R) :
    N.SameLinkage (N.sourceIdx r) (N.targetIdx r) := by
  unfold SameLinkage
  simpa [sourceIdx, targetIdx] using N.linked_of_reaction r

noncomputable def rotateIncomingToOutgoing
    (N : Network S) (c : N.ComplexIdx)
    (x : N.IncomingTreeDecoration c) : N.OutgoingTreeDecoration c := by
  classical
  by_cases hloop : N.sourceIdx x.1.1 = c
  · exact ⟨x.1, hloop, by simpa [hloop] using x.2.2⟩
  · have hcLink : N.SameLinkage (N.sourceIdx x.1.1) c := by
      simpa [x.2.1] using N.reaction_sameLinkage x.1.1
    have hcne : c ≠ N.sourceIdx x.1.1 := Ne.symm hloop
    let q := N.rootedOutgoingReaction x.2.2 hcLink hcne
    have hq := N.rootedOutgoingReaction_spec x.2.2 hcLink hcne
    exact ⟨(q, insert x.1.1 (x.1.2.erase q)), hq.2,
      x.2.2.forward_swap_isRooted rfl x.2.1 hcne hq.1 hq.2⟩

noncomputable def rotateOutgoingToIncoming
    (N : Network S) (c : N.ComplexIdx)
    (x : N.OutgoingTreeDecoration c) : N.IncomingTreeDecoration c := by
  classical
  by_cases hloop : N.targetIdx x.1.1 = c
  · exact ⟨x.1, hloop, by simpa [x.2.1] using x.2.2⟩
  · have hdLink : N.SameLinkage c (N.targetIdx x.1.1) := by
      simpa [x.2.1] using N.reaction_sameLinkage x.1.1
    let r := N.lastEnteringReaction x.2.2 hdLink hloop
    have hr := N.lastEnteringReaction_spec x.2.2 hdLink hloop
    exact ⟨(r, insert x.1.1 (x.1.2.erase r)), hr.2.1,
      x.2.2.inverse_swap_isRooted x.2.1 hloop hr.1 hr.2.1 hr.2.2⟩



open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

lemma rotateIncomingToOutgoing_weight
    (N : Network S) (κ : N.RateConstants) (c : N.ComplexIdx)
    (x : N.IncomingTreeDecoration c) :
    κ.k x.1.1 * N.treeWeight κ x.1.2 =
      κ.k (N.rotateIncomingToOutgoing c x).1.1 *
        N.treeWeight κ (N.rotateIncomingToOutgoing c x).1.2 := by
  classical
  rcases x with ⟨⟨r, T⟩, hrt, hT⟩
  change κ.k r * N.treeWeight κ T = _
  by_cases hloop : N.sourceIdx r = c
  · simp [rotateIncomingToOutgoing, hloop]
  · simp [rotateIncomingToOutgoing, hloop]
    have hcLink : N.SameLinkage (N.sourceIdx r) c := by
      unfold SameLinkage
      rw [← hrt]
      simpa [sourceIdx, targetIdx] using N.linked_of_reaction r
    have hcne : c ≠ N.sourceIdx r := Ne.symm hloop
    let q := N.rootedOutgoingReaction hT hcLink hcne
    have hq := N.rootedOutgoingReaction_spec hT hcLink hcne
    have hrnot : r ∉ T := hT.reaction_not_mem_of_source_root rfl
    exact N.treeWeight_forward_swap κ hrnot hq.1




variable {S : Type} [DecidableEq S] [Fintype S]

lemma rotateIncomingToOutgoing_val_of_loop
    (N : Network S) (c : N.ComplexIdx) (x : N.IncomingTreeDecoration c)
    (hloop : N.sourceIdx x.1.1 = c) :
    (N.rotateIncomingToOutgoing c x).1 = x.1 := by
  classical
  simp [rotateIncomingToOutgoing, hloop]

lemma rotateOutgoingToIncoming_val_of_loop
    (N : Network S) (c : N.ComplexIdx) (x : N.OutgoingTreeDecoration c)
    (hloop : N.targetIdx x.1.1 = c) :
    (N.rotateOutgoingToIncoming c x).1 = x.1 := by
  classical
  simp [rotateOutgoingToIncoming, hloop]



variable {S : Type} [DecidableEq S] [Fintype S]

lemma rotateIncomingToOutgoing_val_of_ne
    (N : Network S) (c : N.ComplexIdx) (x : N.IncomingTreeDecoration c)
    (hloop : N.sourceIdx x.1.1 ≠ c) :
    let hcLink : N.SameLinkage (N.sourceIdx x.1.1) c := by
      simpa [x.2.1] using N.reaction_sameLinkage x.1.1
    let hcne : c ≠ N.sourceIdx x.1.1 := Ne.symm hloop
    let q := N.rootedOutgoingReaction x.2.2 hcLink hcne
    (N.rotateIncomingToOutgoing c x).1 =
      (q, insert x.1.1 (x.1.2.erase q)) := by
  classical
  simp [rotateIncomingToOutgoing, hloop]

lemma rotateOutgoingToIncoming_val_of_ne
    (N : Network S) (c : N.ComplexIdx) (x : N.OutgoingTreeDecoration c)
    (hloop : N.targetIdx x.1.1 ≠ c) :
    let hdLink : N.SameLinkage c (N.targetIdx x.1.1) := by
      simpa [x.2.1] using N.reaction_sameLinkage x.1.1
    let r := N.lastEnteringReaction x.2.2 hdLink hloop
    (N.rotateOutgoingToIncoming c x).1 =
      (r, insert x.1.1 (x.1.2.erase r)) := by
  classical
  simp [rotateOutgoingToIncoming, hloop]



variable {S : Type} [DecidableEq S] [Fintype S]

lemma rotate_right_inv
    (N : Network S) (c : N.ComplexIdx)
    (y : N.OutgoingTreeDecoration c) :
    N.rotateIncomingToOutgoing c (N.rotateOutgoingToIncoming c y) = y := by
  classical
  apply Subtype.ext
  by_cases hloop : N.targetIdx y.1.1 = c
  · have hinv := N.rotateOutgoingToIncoming_val_of_loop c y hloop
    let x := N.rotateOutgoingToIncoming c y
    have hxval : x.1 = y.1 := by
      dsimp [x]
      exact hinv
    have hxsrc : N.sourceIdx x.1.1 = c := by
      rw [hxval]
      exact y.2.1
    have hfwd := N.rotateIncomingToOutgoing_val_of_loop c x hxsrc
    exact hfwd.trans hxval
  · let hdLink : N.SameLinkage c (N.targetIdx y.1.1) := by
      simpa [y.2.1] using N.reaction_sameLinkage y.1.1
    let r := N.lastEnteringReaction y.2.2 hdLink hloop
    have hr := N.lastEnteringReaction_spec y.2.2 hdLink hloop
    let T := insert y.1.1 (y.1.2.erase r)
    let x := N.rotateOutgoingToIncoming c y
    have hxval : x.1 = (r, T) := by
      dsimp [x, T, r, hdLink]
      exact N.rotateOutgoingToIncoming_val_of_ne c y hloop
    have hsrcne : N.sourceIdx x.1.1 ≠ c := by
      rw [hxval]
      exact y.2.2.2.1 r hr.1
    let hcLink : N.SameLinkage (N.sourceIdx x.1.1) c := by
      simpa [x.2.1] using N.reaction_sameLinkage x.1.1
    let hcne : c ≠ N.sourceIdx x.1.1 := Ne.symm hsrcne
    let qx := N.rootedOutgoingReaction x.2.2 hcLink hcne
    have hqmem : y.1.1 ∈ x.1.2 := by
      rw [hxval]
      dsimp [T]
      exact Finset.mem_insert_self y.1.1 (y.1.2.erase r)
    have hqeq : qx = y.1.1 := by
      dsimp [qx]
      exact N.rootedOutgoingReaction_eq x.2.2 hcLink hcne hqmem y.2.1
    have hfwd := N.rotateIncomingToOutgoing_val_of_ne c x hsrcne
    have hqnotU : y.1.1 ∉ y.1.2 :=
      y.2.2.reaction_not_mem_of_source_root y.2.1
    have heraseT : T.erase y.1.1 = y.1.2.erase r := by
      dsimp [T]
      apply Finset.erase_insert
      intro hmem
      exact hqnotU (Finset.mem_of_mem_erase hmem)
    have hins : insert r (T.erase y.1.1) = y.1.2 := by
      rw [heraseT, Finset.insert_erase hr.1]
    change (N.rotateIncomingToOutgoing c x).1 =
      (qx, insert x.1.1 (x.1.2.erase qx)) at hfwd
    rw [hqeq] at hfwd
    rw [hxval] at hfwd
    change (N.rotateIncomingToOutgoing c x).1 = y.1
    calc
      (N.rotateIncomingToOutgoing c x).1
          = (y.1.1, insert r (T.erase y.1.1)) := hfwd
      _ = (y.1.1, y.1.2) := by rw [hins]
      _ = y.1 := by cases y.1 <;> rfl



variable {S : Type} [DecidableEq S] [Fintype S]

lemma rotate_left_inv
    (N : Network S) (c : N.ComplexIdx)
    (x : N.IncomingTreeDecoration c) :
    N.rotateOutgoingToIncoming c (N.rotateIncomingToOutgoing c x) = x := by
  classical
  apply Subtype.ext
  by_cases hloop : N.sourceIdx x.1.1 = c
  · have hfwd := N.rotateIncomingToOutgoing_val_of_loop c x hloop
    let y := N.rotateIncomingToOutgoing c x
    have hyval : y.1 = x.1 := by
      dsimp [y]
      exact hfwd
    have hytgt : N.targetIdx y.1.1 = c := by
      rw [hyval]
      exact x.2.1
    have hinv := N.rotateOutgoingToIncoming_val_of_loop c y hytgt
    exact hinv.trans hyval
  · let hcLink : N.SameLinkage (N.sourceIdx x.1.1) c := by
      simpa [x.2.1] using N.reaction_sameLinkage x.1.1
    let hcne : c ≠ N.sourceIdx x.1.1 := Ne.symm hloop
    let q := N.rootedOutgoingReaction x.2.2 hcLink hcne
    have hq := N.rootedOutgoingReaction_spec x.2.2 hcLink hcne
    let U := insert x.1.1 (x.1.2.erase q)
    let y := N.rotateIncomingToOutgoing c x
    have hyval : y.1 = (q, U) := by
      dsimp [y, U, q, hcLink, hcne]
      exact N.rotateIncomingToOutgoing_val_of_ne c x hloop
    have hqtgtne : N.targetIdx y.1.1 ≠ c := by
      rw [hyval]
      intro hqt
      apply x.2.2.target_not_reaches_source hq.1
      have hsame : N.targetIdx q = N.sourceIdx q := hqt.trans hq.2.symm
      rw [hsame]
      exact Relation.ReflTransGen.refl
    let hdLink : N.SameLinkage c (N.targetIdx y.1.1) := by
      simpa [y.2.1] using N.reaction_sameLinkage y.1.1
    let ry := N.lastEnteringReaction y.2.2 hdLink hqtgtne
    have hrmemY : x.1.1 ∈ y.1.2 := by
      rw [hyval]
      dsimp [U]
      exact Finset.mem_insert_self x.1.1 (x.1.2.erase q)
    have hrtgtY : N.targetIdx x.1.1 = c := x.2.1
    have hqTargetLinkOld : N.SameLinkage (N.sourceIdx x.1.1) (N.targetIdx q) := by
      have hsrcLink := x.2.2.2.2.1 q hq.1
      exact Network.Linked.trans hsrcLink (N.reaction_sameLinkage q)
    have hreachOld : N.SelectedReaches x.1.2 (N.targetIdx q) (N.sourceIdx x.1.1) :=
      x.2.2.2.2.2 (N.targetIdx q) hqTargetLinkOld
    have hnotBack : ¬ N.SelectedReaches x.1.2 (N.targetIdx q) (N.sourceIdx q) :=
      x.2.2.target_not_reaches_source hq.1
    have hprefixErase :
        N.SelectedReaches (x.1.2.erase q) (N.targetIdx q) (N.sourceIdx x.1.1) :=
      selectedReaches_erase_of_not_reaches_source hreachOld hnotBack
    have hprefixY : N.SelectedReaches y.1.2 (N.targetIdx y.1.1) (N.sourceIdx x.1.1) := by
      rw [hyval]
      dsimp [U]
      exact (Relation.ReflTransGen.mono
        (r := N.SelectedEdge (x.1.2.erase q))
          (p := N.SelectedEdge (insert x.1.1 (x.1.2.erase q))) (by
        intro a b hab
        rcases hab with ⟨p, hp, hs, ht⟩
        exact ⟨p, Finset.mem_insert.mpr (Or.inr hp), hs, ht⟩))
        (N.targetIdx q) (N.sourceIdx x.1.1) hprefixErase
    have hryeq : ry = x.1.1 := by
      dsimp [ry]
      exact N.lastEnteringReaction_eq y.2.2 hdLink hqtgtne hrmemY hrtgtY hprefixY
    have hinv := N.rotateOutgoingToIncoming_val_of_ne c y hqtgtne
    change (N.rotateOutgoingToIncoming c y).1 =
      (ry, insert y.1.1 (y.1.2.erase ry)) at hinv
    rw [hryeq] at hinv
    rw [hyval] at hinv
    have hrnotT : x.1.1 ∉ x.1.2 :=
      x.2.2.reaction_not_mem_of_source_root rfl
    have heraseU : U.erase x.1.1 = x.1.2.erase q := by
      dsimp [U]
      apply Finset.erase_insert
      intro hmem
      exact hrnotT (Finset.mem_of_mem_erase hmem)
    have hins : insert q (U.erase x.1.1) = x.1.2 := by
      rw [heraseU, Finset.insert_erase hq.1]
    change (N.rotateOutgoingToIncoming c y).1 = x.1
    calc
      (N.rotateOutgoingToIncoming c y).1
          = (x.1.1, insert q (U.erase x.1.1)) := hinv
      _ = (x.1.1, x.1.2) := by rw [hins]
      _ = x.1 := by cases x.1 <;> rfl



open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

lemma sum_incomingTreeDecoration
    (N : Network S) (κ : N.RateConstants) (c : N.ComplexIdx) :
    (∑ x : N.IncomingTreeDecoration c,
      κ.k x.1.1 * N.treeWeight κ x.1.2) =
    ∑ r : N.R, if N.targetIdx r = c then
      κ.k r * N.treeConstant κ (N.sourceIdx r) else 0 := by
  classical
  change (∑ x : {p : N.R × Finset N.R //
      N.targetIdx p.1 = c ∧ N.IsRootedInArborescence (N.sourceIdx p.1) p.2},
      κ.k x.1.1 * N.treeWeight κ x.1.2) = _
  have hsub :
      (∑ x : {p : N.R × Finset N.R //
          N.targetIdx p.1 = c ∧ N.IsRootedInArborescence (N.sourceIdx p.1) p.2},
        κ.k x.1.1 * N.treeWeight κ x.1.2) =
      ∑ p ∈ Finset.univ.filter (fun p : N.R × Finset N.R =>
          N.targetIdx p.1 = c ∧ N.IsRootedInArborescence (N.sourceIdx p.1) p.2),
        κ.k p.1 * N.treeWeight κ p.2 := by
    symm
    exact Finset.sum_subtype _ (by intro p; simp) _
  rw [hsub]
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hrt : N.targetIdx r = c
  · simp only [hrt, true_and, if_true]
    change (∑ x : Finset N.R,
      if N.IsRootedInArborescence (N.sourceIdx r) x then
        κ.k r * N.treeWeight κ x else 0) = _
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    rfl
  · simp only [hrt, false_and, if_false]
    exact Fintype.sum_eq_zero _ (fun _ => rfl)

lemma sum_outgoingTreeDecoration
    (N : Network S) (κ : N.RateConstants) (c : N.ComplexIdx) :
    (∑ x : N.OutgoingTreeDecoration c,
      κ.k x.1.1 * N.treeWeight κ x.1.2) =
    ∑ r : N.R, if N.sourceIdx r = c then
      κ.k r * N.treeConstant κ c else 0 := by
  classical
  change (∑ x : {p : N.R × Finset N.R //
      N.sourceIdx p.1 = c ∧ N.IsRootedInArborescence c p.2},
      κ.k x.1.1 * N.treeWeight κ x.1.2) = _
  have hsub :
      (∑ x : {p : N.R × Finset N.R //
          N.sourceIdx p.1 = c ∧ N.IsRootedInArborescence c p.2},
        κ.k x.1.1 * N.treeWeight κ x.1.2) =
      ∑ p ∈ Finset.univ.filter (fun p : N.R × Finset N.R =>
          N.sourceIdx p.1 = c ∧ N.IsRootedInArborescence c p.2),
        κ.k p.1 * N.treeWeight κ p.2 := by
    symm
    exact Finset.sum_subtype _ (by intro p; simp) _
  rw [hsub]
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hrs : N.sourceIdx r = c
  · simp only [hrs, true_and, if_true]
    change (∑ x : Finset N.R,
      if N.IsRootedInArborescence c x then
        κ.k r * N.treeWeight κ x else 0) = _
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    rfl
  · simp only [hrs, false_and, if_false]
    exact Fintype.sum_eq_zero _ (fun _ => rfl)



open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

noncomputable def treeRotationEquiv (N : Network S) (c : N.ComplexIdx) :
    N.IncomingTreeDecoration c ≃ N.OutgoingTreeDecoration c where
  toFun := N.rotateIncomingToOutgoing c
  invFun := N.rotateOutgoingToIncoming c
  left_inv := N.rotate_left_inv c
  right_inv := N.rotate_right_inv c

lemma incomingTreeDecoration_sum_eq_outgoing
    (N : Network S) (κ : N.RateConstants) (c : N.ComplexIdx) :
    (∑ x : N.IncomingTreeDecoration c,
      κ.k x.1.1 * N.treeWeight κ x.1.2) =
    ∑ y : N.OutgoingTreeDecoration c,
      κ.k y.1.1 * N.treeWeight κ y.1.2 := by
  classical
  exact Fintype.sum_equiv (N.treeRotationEquiv c)
    (fun x : N.IncomingTreeDecoration c => κ.k x.1.1 * N.treeWeight κ x.1.2)
    (fun y : N.OutgoingTreeDecoration c => κ.k y.1.1 * N.treeWeight κ y.1.2)
    (N.rotateIncomingToOutgoing_weight κ c)

lemma treeConstant_flow_balance
    (N : Network S) (κ : N.RateConstants) (c : N.ComplexIdx) :
    (∑ r : N.R, if N.targetIdx r = c then
      κ.k r * N.treeConstant κ (N.sourceIdx r) else 0) =
    ∑ r : N.R, if N.sourceIdx r = c then
      κ.k r * N.treeConstant κ c else 0 := by
  calc
    (∑ r : N.R, if N.targetIdx r = c then
      κ.k r * N.treeConstant κ (N.sourceIdx r) else 0)
        = ∑ x : N.IncomingTreeDecoration c,
            κ.k x.1.1 * N.treeWeight κ x.1.2 :=
          (N.sum_incomingTreeDecoration κ c).symm
    _ = ∑ y : N.OutgoingTreeDecoration c,
          κ.k y.1.1 * N.treeWeight κ y.1.2 :=
        N.incomingTreeDecoration_sum_eq_outgoing κ c
    _ = ∑ r : N.R, if N.sourceIdx r = c then
          κ.k r * N.treeConstant κ c else 0 :=
        N.sum_outgoingTreeDecoration κ c

/-- **Directed Matrix--Tree theorem, kinetic-kernel form.** The tree-constant vector lies
in the kernel of the kinetic Laplacian.

This is the exact CRNT form of the directed Matrix--Tree theorem.  Its determinant/cofactor
proof is isolated here so downstream CRNT can use the mathematically natural statement. -/
theorem treeConstant_kineticKernel (N : Network S) (κ : N.RateConstants) :
    N.kineticMap κ (N.treeConstantVector κ) = 0 := by
  classical
  funext c
  rw [N.kineticMap_apply]
  change (∑ r : N.R, κ.k r * N.treeConstant κ (N.sourceIdx r) *
      ((if N.targetIdx r = c then 1 else 0) -
       (if N.sourceIdx r = c then 1 else 0))) = 0
  have hterm : ∀ r : N.R,
      κ.k r * N.treeConstant κ (N.sourceIdx r) *
          ((if N.targetIdx r = c then 1 else 0) -
           (if N.sourceIdx r = c then 1 else 0)) =
        (if N.targetIdx r = c then
            κ.k r * N.treeConstant κ (N.sourceIdx r) else 0) -
        (if N.sourceIdx r = c then
            κ.k r * N.treeConstant κ c else 0) := by
    intro r
    by_cases ht : N.targetIdx r = c <;>
      by_cases hs : N.sourceIdx r = c <;>
      simp [ht, hs]
  simp_rw [hterm]
  rw [Finset.sum_sub_distrib]
  rw [N.treeConstant_flow_balance κ c]
  exact sub_self _

/-- If the network is weakly reversible, every complex admits a rooted in-arborescence
inside its linkage class. -/
theorem exists_rootedInArborescence_of_weaklyReversible (N : Network S)
    (hwr : N.WeaklyReversible) (root : N.ComplexIdx) :
    ∃ T, N.IsRootedInArborescence root T := by
  classical
  -- Work inside the linkage class of the root.  For each class vertex, use the least
  -- bounded directed distance to the root.  Weak reversibility makes every such distance
  -- finite; a shortest nontrivial path starts with a reaction whose target has strictly
  -- smaller distance.
  let L := {c : N.ComplexIdx // N.SameLinkage root c}
  let dist : L → ℕ := fun c =>
    Nat.find ((N.reaches_iff_exists_reachesWithin c.1.1 root.1).1
      (hwr.reaches_of_linked (Network.Linked.symm c.2)))
  have hdist_spec (c : L) : N.ReachesWithin (dist c) c.1.1 root.1 := by
    dsimp [dist]
    exact Nat.find_spec ((N.reaches_iff_exists_reachesWithin c.1.1 root.1).1
      (hwr.reaches_of_linked (Network.Linked.symm c.2)))
  have hstep (c : L) (hc : c.1 ≠ root) :
      ∃ r : N.R, N.sourceIdx r = c.1 ∧
        ∃ ht : N.SameLinkage root (N.targetIdx r),
          dist (⟨N.targetIdx r, ht⟩ : L) < dist c := by
    have hpos : 0 < dist c := by
      by_contra hnot
      have hz : dist c = 0 := Nat.eq_zero_of_not_pos hnot
      have hre := hdist_spec c
      rw [hz, N.reachesWithin_zero] at hre
      exact hc (Subtype.ext hre)
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hpos)
    have hre := hdist_spec c
    rw [hk, N.reachesWithin_succ] at hre
    rcases hre with heq | ⟨r, hsrc, hrest⟩
    · exact False.elim (hc (Subtype.ext heq))
    · have hsrcIdx : N.sourceIdx r = c.1 := by
        apply Subtype.ext
        exact hsrc
      have ht : N.SameLinkage root (N.targetIdx r) := by
        unfold SameLinkage
        have hrlink := N.linked_of_reaction r
        rw [hsrc] at hrlink
        exact Network.Linked.trans c.2 hrlink
      let t : L := ⟨N.targetIdx r, ht⟩
      have hdist_le : dist t ≤ k := by
        dsimp [dist, t]
        exact Nat.find_min' _ hrest
      refine ⟨r, hsrcIdx, ht, ?_⟩
      rw [hk]
      exact Nat.lt_succ_of_le hdist_le
  -- Select exactly the distance-decreasing reaction at every non-root class vertex.
  let D := {c : L // c.1 ≠ root}
  let parent : D → N.R := fun c => Classical.choose (hstep c.1 c.2)
  have hparent_src (c : D) : N.sourceIdx (parent c) = c.1.1 := by
    dsimp [parent]
    exact (Classical.choose_spec (hstep c.1 c.2)).1
  have hparent_target_link (c : D) :
      N.SameLinkage root (N.targetIdx (parent c)) := by
    dsimp [parent]
    exact (Classical.choose_spec (hstep c.1 c.2)).2.choose
  have hparent_dist (c : D) :
      dist (⟨N.targetIdx (parent c), hparent_target_link c⟩ : L) < dist c.1 := by
    dsimp [parent]
    exact (Classical.choose_spec (hstep c.1 c.2)).2.choose_spec
  have hparent_inj : Function.Injective parent := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have hs := congrArg N.sourceIdx hab
    simpa only [hparent_src] using hs
  let T : Finset N.R := Finset.univ.image parent
  have hparent_mem (c : D) : parent c ∈ T := by
    dsimp [T]
    exact Finset.mem_image.mpr ⟨c, Finset.mem_univ c, rfl⟩
  have hmem_parent {r : N.R} (hr : r ∈ T) : ∃ c : D, parent c = r := by
    dsimp [T] at hr
    rcases Finset.mem_image.mp hr with ⟨c, _, hc⟩
    exact ⟨c, hc⟩
  refine ⟨T, ?_, ?_, ?_, ?_⟩
  · intro c hlink hc
    let lc : L := ⟨c, hlink⟩
    let dc : D := ⟨lc, hc⟩
    refine ⟨parent dc, ⟨hparent_mem dc, hparent_src dc⟩, ?_⟩
    intro r hr
    rcases hr with ⟨hrT, hsrc⟩
    obtain ⟨d, hd⟩ := hmem_parent hrT
    have hdc : d = dc := by
      apply Subtype.ext
      apply Subtype.ext
      calc
        d.1.1 = N.sourceIdx (parent d) := (hparent_src d).symm
        _ = N.sourceIdx r := by rw [hd]
        _ = c := hsrc
        _ = dc.1.1 := rfl
    calc
      r = parent d := hd.symm
      _ = parent dc := by rw [hdc]
  · intro r hr
    obtain ⟨d, rfl⟩ := hmem_parent hr
    rw [hparent_src d]
    exact d.2
  · intro r hr
    obtain ⟨d, rfl⟩ := hmem_parent hr
    rw [hparent_src d]
    exact d.1.2
  · intro c hlink
    let lc : L := ⟨c, hlink⟩
    suffices hreach : ∀ x : L, N.SelectedReaches T x.1 root by
      exact hreach lc
    intro x
    induction hdx : dist x using Nat.strong_induction_on generalizing x with
    | h n ih =>
      by_cases hx : x.1 = root
      · have hrefl : N.SelectedReaches T root root := Relation.ReflTransGen.refl
        simpa [hx] using hrefl
      · let d : D := ⟨x, hx⟩
        let y : L := ⟨N.targetIdx (parent d), hparent_target_link d⟩
        have hylt : dist y < n := by
          rw [← hdx]
          exact hparent_dist d
        have hyreach : N.SelectedReaches T y.1 root := ih (dist y) hylt y rfl
        have hedge : N.SelectedEdge T x.1 y.1 := by
          refine ⟨parent d, hparent_mem d, ?_, rfl⟩
          exact hparent_src d
        exact (Relation.ReflTransGen.single hedge).trans hyreach

/-- Tree constants are strictly positive on weakly reversible networks. -/
theorem treeConstant_pos_of_weaklyReversible (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) (root : N.ComplexIdx) :
    0 < N.treeConstant κ root :=
  N.treeConstant_pos_of_exists_arborescence κ root
    (N.exists_rootedInArborescence_of_weaklyReversible hwr root)

/-- On a weakly reversible network the tree-constant vector is a strictly positive
kinetic-kernel vector. -/
theorem treeConstantVector_positive_kernel (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) :
    (∀ c, 0 < N.treeConstantVector κ c) ∧
      N.kineticMap κ (N.treeConstantVector κ) = 0 := by
  refine ⟨?_, N.treeConstant_kineticKernel κ⟩
  intro c
  exact N.treeConstant_pos_of_weaklyReversible κ hwr c

end Network

end CRNT
