import CRNT.Oscillation.BanajiDependentReaction

/-!
# End-to-end ordinary oscillation inheritance for one dependent added reaction

The network algebra for appending a stoichiometrically dependent reaction is closed: the
stoichiometric subspace/rank is unchanged and the new vector field is embedded into a smooth real
parameter family through zero rate.  The return-map IFT and scalar branch-to-periodic-orbit closure
are also closed.

The remaining model-specific construction is therefore a parameterized scalar Poincare section for
the original nondegenerate cycle whose IFT branch stays positive.  Once that object is supplied,
strictly positive added-reaction rate and oscillatory capacity of the enlarged CRN follow
immediately.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Precise return-section construction target for regular perturbation by one dependent reaction. -/
def ScalarDependentReactionPersistenceConstructionTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T]
    (N : Network T) (q : Reaction T)
    (hdep : N.IsStoichiometricallyDependentReaction q)
    (κ : N.RateConstants) (P : N.NondegeneratePositivePeriodicOrbit κ),
      Nonempty (ScalarDependentReactionPersistenceData N q κ)

/-- A certified nondegenerate orbit of the small network persists to **ordinary** oscillatory
capacity after adding one dependent reaction.  Retaining nondegeneracy/stability of the enlarged
cycle is a stronger Floquet-continuity statement and remains represented separately by the existing
inheritance targets. -/
theorem oscillatoryCapacity_addDependentReaction
    (hpersist : ScalarDependentReactionPersistenceConstructionTarget)
    {N : Network S} (q : Reaction S)
    (hdep : N.IsStoichiometricallyDependentReaction q)
    (hosc : N.NondegenerateOscillatoryCapacity) :
    (N.addReaction q).OscillatoryCapacity := by
  obtain ⟨κ, ⟨P⟩⟩ := hosc
  obtain ⟨D⟩ := hpersist N q hdep κ P
  exact D.oscillatoryCapacity

/-- Relation-facing version for two explicitly related networks. -/
theorem oscillatoryCapacity_of_singleDependentReactionExtension
    (hpersist : ScalarDependentReactionPersistenceConstructionTarget)
    {Nsmall Nlarge : Network S}
    (hext : IsSingleDependentReactionExtension Nsmall Nlarge)
    (hosc : Nsmall.NondegenerateOscillatoryCapacity) :
    Nlarge.OscillatoryCapacity := by
  obtain ⟨q, hdep, rfl⟩ := hext
  exact oscillatoryCapacity_addDependentReaction hpersist q hdep hosc

end Network
end CRNT
