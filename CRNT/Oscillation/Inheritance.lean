import CRNT.Oscillation.Floquet
import CRNT.Oscillation.ReactionRestriction

/-!
# Exact oscillation inheritance under dynamically null reaction enlargement

The general Banaji-style inheritance theorems for adding reactions/species require regular or
singular perturbation theory.  This module closes an important exact special case: adjoining any
finite family of **self-reaction channels** `y → y`.

A self reaction has zero reaction vector, so it contributes exactly zero to both the mass-action
vector field and its Jacobian for every concentration and every positive rate constant.  Therefore
an existing periodic orbit transfers without approximation.  Because the Jacobian along the orbit
is unchanged, the same fundamental variational matrix transfers too, preserving Floquet
nondegeneracy and linear stability exactly.

This is useful in its own right and provides a theorem-level base case for broader reaction-addition
inheritance developments.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Enlarge a CRN by adding a finite family of dynamically null self-reaction channels `c(q) → c(q)`.
Parallel self channels are allowed. -/
def addSelfReactions (N : Network S) (Q : Type) [DecidableEq Q] [Fintype Q]
    (c : Q → Complex S) : Network S where
  R := N.R ⊕ Q
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction
    | Sum.inl r => N.reaction r
    | Sum.inr q => ⟨c q, c q⟩

@[simp] theorem addSelfReactions_reaction_inl (N : Network S)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) (r : N.R) :
    (N.addSelfReactions Q c).reaction (Sum.inl r) = N.reaction r :=
  rfl

@[simp] theorem addSelfReactions_reaction_inr (N : Network S)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) (q : Q) :
    (N.addSelfReactions Q c).reaction (Sum.inr q) = ⟨c q, c q⟩ :=
  rfl

@[simp] theorem addSelfReactions_reactionVector_inl (N : Network S)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) (r : N.R) :
    (N.addSelfReactions Q c).reactionVector (Sum.inl r) = N.reactionVector r := by
  rfl

@[simp] theorem addSelfReactions_reactionVector_inr (N : Network S)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) (q : Q) :
    (N.addSelfReactions Q c).reactionVector (Sum.inr q) = 0 := by
  funext s
  simp [Network.reactionVector, Reaction.vector, addSelfReactions]

/-- Extend an old positive rate vector to the self-reaction enlargement.  The new dynamically null
channels receive the arbitrary positive rate `1`. -/
def RateConstants.extendSelfReactions {N : Network S}
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S)
    (κ : N.RateConstants) : (N.addSelfReactions Q c).RateConstants where
  k
    | Sum.inl r => κ.k r
    | Sum.inr _ => 1
  positive
    | Sum.inl r => κ.positive r
    | Sum.inr _ => zero_lt_one

@[simp] theorem extendSelfReactions_k_inl {N : Network S}
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S)
    (κ : N.RateConstants) (r : N.R) :
    (κ.extendSelfReactions Q c).k (Sum.inl r) = κ.k r :=
  rfl

@[simp] theorem extendSelfReactions_k_inr {N : Network S}
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S)
    (κ : N.RateConstants) (q : Q) :
    (κ.extendSelfReactions Q c).k (Sum.inr q) = 1 :=
  rfl

/-- Old reaction channels retain exactly their old mass-action rates after self-reaction enlargement. -/
@[simp] theorem massActionRate_addSelfReactions_inl (N : Network S)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S)
    (κ : N.RateConstants) (r : N.R) (x : Concentration S) :
    (N.addSelfReactions Q c).massActionRate (κ.extendSelfReactions Q c) (Sum.inl r) x =
      N.massActionRate κ r x := by
  rfl

/-- Splitting a sum over the reactions of `addSelfReactions`.  Stated once here because the
sum in the goals below carries the structure's own `fintypeR` field instance rather than
`instFintypeSum`, so `Fintype.sum_sum_type` matches by neither `rw` nor `simp only`; `exact`
closes it since `(N.addSelfReactions Q c).R` is *definitionally* `N.R ⊕ Q`. -/
theorem sum_addSelfReactions {M : Type*} [AddCommMonoid M] (N : Network S) (Q : Type)
    [DecidableEq Q] [Fintype Q] (c : Q → Complex S)
    (f : (N.addSelfReactions Q c).R → M) :
    ∑ r, f r = (∑ r : N.R, f (Sum.inl r)) + ∑ q : Q, f (Sum.inr q) :=
  Fintype.sum_sum_type f

/-- **Exact vector-field inheritance.** Adding self-reaction channels does not change the
mass-action vector field. -/
theorem massActionVectorField_addSelfReactions (N : Network S)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S)
    (κ : N.RateConstants) (x : Concentration S) :
    (N.addSelfReactions Q c).massActionVectorField (κ.extendSelfReactions Q c) x =
      N.massActionVectorField κ x := by
  funext s
  rw [massActionVectorField_apply, massActionVectorField_apply]
  -- OBLIGATION (Lean plumbing).  `(N.addSelfReactions Q c).R` *is* `N.R ⊕ Q`, but the sum
  -- carries the structure's own `fintypeR` field instance, not `instFintypeSum`, so
  -- `Fintype.sum_sum_type` matches neither by `rw`, `simp only`, nor full `simp`
  -- (all three tried; full `simp` made it worse by reshaping the goal).
  -- Route: add a reusable splitting lemma next to `addSelfReactions`, e.g.
  --   `theorem sum_addSelfReactions (f : (N.addSelfReactions Q c).R → M) :
  --      ∑ r, f r = ∑ r : N.R, f (Sum.inl r) + ∑ q : Q, f (Sum.inr q)`
  -- proved once by `Fintype.sum_congr`/`Subsingleton.elim` on the instance, then used
  -- here and at lines ~129 and ~171 which fail the same way.
  rw [sum_addSelfReactions N Q c
    (fun r => (N.addSelfReactions Q c).massActionRate (κ.extendSelfReactions Q c) r x *
      (N.addSelfReactions Q c).reactionVector r s)]
  have hself :
      (∑ q : Q,
        (N.addSelfReactions Q c).massActionRate (κ.extendSelfReactions Q c) (Sum.inr q) x *
          (N.addSelfReactions Q c).reactionVector (Sum.inr q) s) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    simp
  rw [hself, add_zero]
  apply Finset.sum_congr rfl
  intro r _
  simp

/-- **Exact Jacobian inheritance.** Adding self-reaction channels does not change the mass-action
Jacobian. -/
theorem massActionJacobian_addSelfReactions (N : Network S)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S)
    (κ : N.RateConstants) (x : Concentration S) :
    (N.addSelfReactions Q c).massActionJacobian (κ.extendSelfReactions Q c) x =
      N.massActionJacobian κ x := by
  ext i j
  simp only [massActionJacobian]
  rw [sum_addSelfReactions N Q c
    (fun r => (κ.extendSelfReactions Q c).k r *
      massActionMonomialGrad ((N.addSelfReactions Q c).reaction r).source x j *
      (N.addSelfReactions Q c).reactionVector r i)]
  have hself :
      (∑ q : Q,
        (κ.extendSelfReactions Q c).k (Sum.inr q) *
          massActionMonomialGrad ((N.addSelfReactions Q c).reaction (Sum.inr q)).source x j *
          (N.addSelfReactions Q c).reactionVector (Sum.inr q) i) = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    simp
  rw [hself, add_zero]
  apply Finset.sum_congr rfl
  intro r _
  simp

/-- Lift a positive periodic orbit unchanged through a self-reaction enlargement. -/
def PositivePeriodicOrbit.addSelfReactions
    {N : Network S} {κ : N.RateConstants} (P : N.PositivePeriodicOrbit κ)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (N.addSelfReactions Q c).PositivePeriodicOrbit (κ.extendSelfReactions Q c) where
  orbit := P.orbit
  period := P.period
  period_pos := P.period_pos
  positive := P.positive
  solution := by
    intro t s
    rw [N.massActionVectorField_addSelfReactions Q c κ (P.orbit t)]
    exact P.solution t s
  periodic := P.periodic
  nonconstant := P.nonconstant

/-- Lift a fundamental variational matrix unchanged through a self-reaction enlargement. -/
def MassActionFloquetData.addSelfReactions
    {N : Network S} {κ : N.RateConstants} {P : N.PositivePeriodicOrbit κ}
    (F : N.MassActionFloquetData κ P)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (N.addSelfReactions Q c).MassActionFloquetData (κ.extendSelfReactions Q c)
      (P.addSelfReactions Q c) where
  fundamental := F.fundamental
  initial := F.initial
  solves := by
    intro t i j
    have h := F.solves t i j
    -- the orbit argument appears as `(P.addSelfReactions Q c).orbit t`, which is only
    -- *defeq* to `P.orbit t`; `simp only` unifies where `rw` cannot.
    simp only [N.massActionJacobian_addSelfReactions Q c κ]
    exact h

/-- The monodromy matrix is literally unchanged by self-reaction enlargement. -/
@[simp] theorem MassActionFloquetData.monodromy_addSelfReactions
    {N : Network S} {κ : N.RateConstants} {P : N.PositivePeriodicOrbit κ}
    (F : N.MassActionFloquetData κ P)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (F.addSelfReactions Q c).monodromy = F.monodromy :=
  rfl

/-- Floquet nondegeneracy is preserved exactly by self-reaction enlargement. -/
def NondegeneratePositivePeriodicOrbit.addSelfReactions
    {N : Network S} {κ : N.RateConstants}
    (P : N.NondegeneratePositivePeriodicOrbit κ)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (N.addSelfReactions Q c).NondegeneratePositivePeriodicOrbit (κ.extendSelfReactions Q c) where
  orbit := P.orbit.addSelfReactions Q c
  floquet := P.floquet.addSelfReactions Q c
  nondegenerate := by
    simpa [MassActionFloquetData.Nondegenerate, MassActionFloquetData.OneIsSimpleMultiplier,
      MassActionFloquetData.floquetPolynomial] using P.nondegenerate

/-- Linear Floquet stability is preserved exactly by self-reaction enlargement. -/
def LinearlyStablePositivePeriodicOrbit.addSelfReactions
    {N : Network S} {κ : N.RateConstants}
    (P : N.LinearlyStablePositivePeriodicOrbit κ)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (N.addSelfReactions Q c).LinearlyStablePositivePeriodicOrbit (κ.extendSelfReactions Q c) where
  orbit := P.orbit.addSelfReactions Q c
  floquet := P.floquet.addSelfReactions Q c
  stable := by
    simpa [MassActionFloquetData.LinearlyStable, MassActionFloquetData.Nondegenerate,
      MassActionFloquetData.OneIsSimpleMultiplier, MassActionFloquetData.HasMultiplier,
      MassActionFloquetData.floquetPolynomial] using P.stable

/-- Ordinary oscillatory capacity is inherited by arbitrary finite self-reaction enlargement. -/
theorem oscillatoryCapacity_addSelfReactions
    {N : Network S} (h : N.OscillatoryCapacity)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (N.addSelfReactions Q c).OscillatoryCapacity := by
  obtain ⟨κ, ⟨P⟩⟩ := h
  exact ⟨κ.extendSelfReactions Q c, ⟨P.addSelfReactions Q c⟩⟩

/-- Nondegenerate oscillatory capacity is inherited by self-reaction enlargement. -/
theorem nondegenerateOscillatoryCapacity_addSelfReactions
    {N : Network S} (h : N.NondegenerateOscillatoryCapacity)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (N.addSelfReactions Q c).NondegenerateOscillatoryCapacity := by
  obtain ⟨κ, ⟨P⟩⟩ := h
  exact ⟨κ.extendSelfReactions Q c, ⟨P.addSelfReactions Q c⟩⟩

/-- Linearly stable oscillatory capacity is inherited by self-reaction enlargement. -/
theorem linearlyStableOscillatoryCapacity_addSelfReactions
    {N : Network S} (h : N.LinearlyStableOscillatoryCapacity)
    (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    (N.addSelfReactions Q c).LinearlyStableOscillatoryCapacity := by
  obtain ⟨κ, ⟨P⟩⟩ := h
  exact ⟨κ.extendSelfReactions Q c, ⟨P.addSelfReactions Q c⟩⟩

/-- Self-reaction enlargement is a proved oscillation-preserving transformation. -/
theorem oscillationPreserving_addSelfReactions
    (N : Network S) (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    N.OscillationPreserving (N.addSelfReactions Q c) :=
  fun h => oscillatoryCapacity_addSelfReactions h Q c

/-- A transformation from `Nsmall` to `Nlarge` preserves nondegenerate oscillatory capacity. -/
def NondegenerateOscillationPreserving
    {T U : Type} [DecidableEq T] [Fintype T] [DecidableEq U] [Fintype U]
    (Nsmall : Network T) (Nlarge : Network U) : Prop :=
  Nsmall.NondegenerateOscillatoryCapacity → Nlarge.NondegenerateOscillatoryCapacity

/-- A transformation from `Nsmall` to `Nlarge` preserves linearly stable oscillatory capacity. -/
def LinearlyStableOscillationPreserving
    {T U : Type} [DecidableEq T] [Fintype T] [DecidableEq U] [Fintype U]
    (Nsmall : Network T) (Nlarge : Network U) : Prop :=
  Nsmall.LinearlyStableOscillatoryCapacity → Nlarge.LinearlyStableOscillatoryCapacity

/-- Self-reaction enlargement preserves nondegenerate oscillation. -/
theorem nondegenerateOscillationPreserving_addSelfReactions
    (N : Network S) (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    N.NondegenerateOscillationPreserving (N.addSelfReactions Q c) :=
  fun h => nondegenerateOscillatoryCapacity_addSelfReactions h Q c

/-- Self-reaction enlargement preserves linearly stable oscillation. -/
theorem linearlyStableOscillationPreserving_addSelfReactions
    (N : Network S) (Q : Type) [DecidableEq Q] [Fintype Q] (c : Q → Complex S) :
    N.LinearlyStableOscillationPreserving (N.addSelfReactions Q c) :=
  fun h => linearlyStableOscillatoryCapacity_addSelfReactions h Q c

/-- Generic statement of a nondegenerate inheritance theorem for a *specified* enlargement
relation.  Concrete Banaji-style developments must first formalize the corresponding network
relation (fully-open induced extension, rank-preserving species extension, reaction splitting,
etc.) and then prove this proposition for that relation.  Unlike the earlier broad placeholder,
this cannot accidentally claim that arbitrary unrelated networks inherit oscillation. -/
def NondegenerateInheritanceTargetFor
    (Extension : ∀ {T U : Type} [DecidableEq T] [Fintype T]
      [DecidableEq U] [Fintype U], Network T → Network U → Prop) : Prop :=
  ∀ {T U : Type} [DecidableEq T] [Fintype T] [DecidableEq U] [Fintype U]
    (Nsmall : Network T) (Nlarge : Network U),
    Extension Nsmall Nlarge →
    Nsmall.NondegenerateOscillationPreserving Nlarge

/-- Stable analogue of `NondegenerateInheritanceTargetFor`. -/
def LinearlyStableInheritanceTargetFor
    (Extension : ∀ {T U : Type} [DecidableEq T] [Fintype T]
      [DecidableEq U] [Fintype U], Network T → Network U → Prop) : Prop :=
  ∀ {T U : Type} [DecidableEq T] [Fintype T] [DecidableEq U] [Fintype U]
    (Nsmall : Network T) (Nlarge : Network U),
    Extension Nsmall Nlarge →
    Nsmall.LinearlyStableOscillationPreserving Nlarge

end Network

end CRNT
