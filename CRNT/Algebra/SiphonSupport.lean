import CRNT.Dynamics.Siphon
import CRNT.Graph.Reversibility

/-!
# Combinatorial support characterizations of siphons

`ComplexUsesSpeciesSet P y` says that `y` uses a species in `P`.
Backward reaction closure is exactly the siphon condition; minimal nonempty
supports correspond to minimal nonempty siphons. Forward closure is also studied.

These are support predicates. This module constructs no polynomial ideal and
proves no actual prime-ideal membership or minimal-prime/saturation theorem.
The full algebraic Shiu–Sturmfels correspondence remains incomplete.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A complex uses `P` iff at least one
species from `P` occurs in the complex. -/
def ComplexUsesSpeciesSet (P : Finset S) (y : Complex S) : Prop :=
  ∃ s ∈ P, y s ≠ 0

/-- Reaction-support backward closure of the species support. -/
def SupportBackwardClosed (N : Network S) (P : Finset S) : Prop :=
  ∀ r : N.R,
    ComplexUsesSpeciesSet P (N.reaction r).target →
      ComplexUsesSpeciesSet P (N.reaction r).source

/-- Reaction-support forward closure. -/
def SupportForwardClosed (N : Network S) (P : Finset S) : Prop :=
  ∀ r : N.R,
    ComplexUsesSpeciesSet P (N.reaction r).source →
      ComplexUsesSpeciesSet P (N.reaction r).target

/-- Product-complex species-support membership is exactly "the reaction produces a
species in `P`". -/
theorem complexUsesSpeciesSet_target_iff (N : Network S) (P : Finset S) (r : N.R) :
    ComplexUsesSpeciesSet P (N.reaction r).target ↔
      ∃ s ∈ P, N.IsProduct r s :=
  Iff.rfl

/-- Source-complex species-support membership is exactly "the reaction consumes a
species in `P`". -/
theorem complexUsesSpeciesSet_source_iff (N : Network S) (P : Finset S) (r : N.R) :
    ComplexUsesSpeciesSet P (N.reaction r).source ↔
      ∃ s ∈ P, N.IsReactant r s :=
  Iff.rfl

/-- **Support siphon criterion.** A species set is a siphon iff its species support is
backward closed under every reaction. -/
theorem isSiphon_iff_supportBackwardClosed (N : Network S) (P : Finset S) :
    N.IsSiphon P ↔ N.SupportBackwardClosed P := by
  rfl

/-- A nonempty species support satisfying the support closure criterion. -/
def IsNonemptySiphonSupport (N : Network S) (P : Finset S) : Prop :=
  P.Nonempty ∧ N.SupportBackwardClosed P

/-- Nonempty siphon supports are exactly nonempty siphons. -/
theorem isNonemptySiphonSupport_iff (N : Network S) (P : Finset S) :
    N.IsNonemptySiphonSupport P ↔ P.Nonempty ∧ N.IsSiphon P := by
  simp [IsNonemptySiphonSupport, isSiphon_iff_supportBackwardClosed]

/-- Inclusion-minimal nonempty species support with reaction-support closure. -/
def IsMinimalNonemptySiphonSupport (N : Network S) (P : Finset S) : Prop :=
  N.IsNonemptySiphonSupport P ∧
    ∀ Q : Finset S, Q ⊆ P → Q ≠ P → Q.Nonempty → ¬ N.IsNonemptySiphonSupport Q

/-- **Minimal siphons are precisely minimal reaction-support species supports.** -/
theorem isMinimalSiphon_iff_minimalNonemptySupport (N : Network S) (P : Finset S) :
    N.IsMinimalSiphon P ↔ N.IsMinimalNonemptySiphonSupport P := by
  constructor
  · intro h
    refine ⟨(N.isNonemptySiphonSupport_iff P).2 ⟨h.1, h.2.1⟩, ?_⟩
    intro Q hQP hne hQne hQprime
    have hQpow : Q ∈ P.powerset := Finset.mem_powerset.mpr hQP
    exact h.2.2 Q hQpow hQne hne ((N.isNonemptySiphonSupport_iff Q).1 hQprime).2
  · rintro ⟨hP, hmin⟩
    have hPs := (N.isNonemptySiphonSupport_iff P).1 hP
    refine ⟨hPs.1, hPs.2, ?_⟩
    intro Q hQpow hQne hne hQs
    have hQP : Q ⊆ P := Finset.mem_powerset.mp hQpow
    exact hmin Q hQP hne hQne ((N.isNonemptySiphonSupport_iff Q).2 ⟨hQne, hQs⟩)

/-- On a reversible network, reaction-support backward closure automatically implies
forward closure.  Here, species-support membership is invariant along every
reversible reaction pair. -/
theorem supportForwardClosed_of_reversible (N : Network S) (hrev : N.Reversible)
    {P : Finset S} (hback : N.SupportBackwardClosed P) :
    N.SupportForwardClosed P := by
  intro r hsrc
  obtain ⟨r', hsrc', htgt'⟩ := hrev r
  -- the reverse reaction has target = original source and source = original target
  have hrevTarget : ComplexUsesSpeciesSet P (N.reaction r').target := by
    simpa [htgt'] using hsrc
  have hrevSource := hback r' hrevTarget
  simpa [hsrc'] using hrevSource

/-- Thus on reversible networks, membership in the species support is equivalent at the
two endpoints of every reaction. -/
theorem complexUsesSpeciesSet_source_iff_target_of_reversible
    (N : Network S) (hrev : N.Reversible) {P : Finset S} (hP : N.IsSiphon P) (r : N.R) :
    ComplexUsesSpeciesSet P (N.reaction r).source ↔
      ComplexUsesSpeciesSet P (N.reaction r).target := by
  constructor
  · exact N.supportForwardClosed_of_reversible hrev
      ((N.isSiphon_iff_supportBackwardClosed P).1 hP) r
  · exact ((N.isSiphon_iff_supportBackwardClosed P).1 hP) r

end Network

end CRNT
