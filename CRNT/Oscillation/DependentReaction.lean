import CRNT.Oscillation.Inheritance
import CRNT.Stoich.Subspace
import CRNT.Dynamics.MassActionField

/-!
# Adding one stoichiometrically dependent reaction

This module formalizes the finite-CRN side of one of the basic reaction-addition inheritance
moves used in oscillation inheritance theory.  A new reaction `q` is appended to a network while
keeping the species set fixed.  When `q.vector` already lies in the old stoichiometric subspace,
the enlargement does not change that subspace or its rank.

Unlike the exact self-reaction case, the new reaction generally *does* perturb the vector field.
The perturbation is made completely explicit: for new rate `ε > 0`,

`f_new(x) = f_old(x) + ε * x^(source q) * q.vector`.

The Jacobian is the corresponding rank-one reaction contribution.  Thus all CRN-specific algebra
needed by the regular-perturbation inheritance theorem is closed here.  The remaining step is the
analytic persistence theorem saying that a nondegenerate (respectively linearly stable) periodic
orbit survives a sufficiently small positive `ε`.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Append one reaction channel to a network without changing its species type. -/
def addReaction (N : Network S) (q : Reaction S) : Network S where
  R := N.R ⊕ Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction
    | Sum.inl r => N.reaction r
    | Sum.inr _ => q

@[simp] theorem addReaction_reaction_inl (N : Network S) (q : Reaction S) (r : N.R) :
    (N.addReaction q).reaction (Sum.inl r) = N.reaction r :=
  rfl

@[simp] theorem addReaction_reaction_inr (N : Network S) (q : Reaction S) (u : Unit) :
    (N.addReaction q).reaction (Sum.inr u) = q :=
  rfl

@[simp] theorem addReaction_reactionVector_inl (N : Network S) (q : Reaction S) (r : N.R) :
    (N.addReaction q).reactionVector (Sum.inl r) = N.reactionVector r :=
  rfl

@[simp] theorem addReaction_reactionVector_inr (N : Network S) (q : Reaction S) (u : Unit) :
    (N.addReaction q).reactionVector (Sum.inr u) = q.vector :=
  rfl

/-- The added reaction is stoichiometrically dependent when its reaction vector already belongs to
    the old stoichiometric subspace. -/
def IsStoichiometricallyDependentReaction (N : Network S) (q : Reaction S) : Prop :=
  q.vector ∈ N.stoichSubspace

/-- Extend old rate constants by assigning the new reaction an arbitrary positive rate `ε`. -/
def RateConstants.extendReaction {N : Network S} (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) : (N.addReaction q).RateConstants where
  k
    | Sum.inl r => κ.k r
    | Sum.inr _ => ε
  positive
    | Sum.inl r => κ.positive r
    | Sum.inr _ => hε

@[simp] theorem extendReaction_k_inl {N : Network S} (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (r : N.R) :
    (κ.extendReaction q ε hε).k (Sum.inl r) = κ.k r :=
  rfl

@[simp] theorem extendReaction_k_inr {N : Network S} (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (u : Unit) :
    (κ.extendReaction q ε hε).k (Sum.inr u) = ε :=
  rfl

/-- Old channels retain their mass-action rates after appending a reaction. -/
@[simp] theorem massActionRate_addReaction_inl (N : Network S) (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (r : N.R) (x : Concentration S) :
    (N.addReaction q).massActionRate (κ.extendReaction q ε hε) (Sum.inl r) x =
      N.massActionRate κ r x :=
  rfl

/-- The new channel has the expected mass-action rate. -/
@[simp] theorem massActionRate_addReaction_inr (N : Network S) (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (u : Unit) (x : Concentration S) :
    (N.addReaction q).massActionRate (κ.extendReaction q ε hε) (Sum.inr u) x =
      ε * q.source.massActionMonomial x :=
  rfl

/-- Smooth real-parameter extension of the dependent-reaction perturbation through
`ε = 0`.  Positive `ε` corresponds to a genuine positive rate constant on the appended reaction;
`ε = 0` recovers the original vector field exactly. -/
def addedReactionFieldFamily (N : Network S) (κ : N.RateConstants) (q : Reaction S)
    (ε : ℝ) (x : Concentration S) : Concentration S :=
  N.massActionVectorField κ x + (ε * q.source.massActionMonomial x) • q.vector

@[simp] theorem addedReactionFieldFamily_zero (N : Network S) (κ : N.RateConstants)
    (q : Reaction S) (x : Concentration S) :
    N.addedReactionFieldFamily κ q 0 x = N.massActionVectorField κ x := by
  simp [addedReactionFieldFamily]

/-- The parameterized perturbation is smooth jointly in reaction-rate parameter and state. -/
theorem addedReactionFieldFamily_contDiff (N : Network S) (κ : N.RateConstants)
    (q : Reaction S) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun p : ℝ × Concentration S =>
      N.addedReactionFieldFamily κ q p.1 p.2) := by
  have hold : ContDiff ℝ n (fun p : ℝ × Concentration S => N.massActionVectorField κ p.2) :=
    (N.massActionVectorField_contDiff κ).comp contDiff_snd
  have hmono : ContDiff ℝ n (fun p : ℝ × Concentration S => q.source.massActionMonomial p.2) := by
    show ContDiff ℝ n (fun p : ℝ × Concentration S => ∏ s, p.2 s ^ q.source s)
    exact contDiff_prod fun s _ =>
      (((contDiff_apply ℝ ℝ s).comp contDiff_snd).pow _)
  have hscalar : ContDiff ℝ n (fun p : ℝ × Concentration S =>
      p.1 * q.source.massActionMonomial p.2) :=
    contDiff_fst.mul hmono
  simpa [addedReactionFieldFamily] using hold.add (hscalar.smul contDiff_const)

/-- Splitting a sum over the reactions of `addReaction`.  As with `sum_addSelfReactions`,
`(N.addReaction q).R` is *definitionally* `N.R ⊕ Unit` but the sum carries the structure's own
`fintypeR` field, so `Fintype.sum_sum_type` will not match by `rw`; `exact`/`trans` go
through by defeq. -/
theorem sum_addReaction {M : Type*} [AddCommMonoid M] (N : Network S) (q : Reaction S)
    (f : (N.addReaction q).R → M) :
    ∑ r, f r = (∑ r : N.R, f (Sum.inl r)) + f (Sum.inr ()) :=
  (Fintype.sum_sum_type f).trans (by simp)

/-- Exact componentwise vector-field perturbation after adding one reaction. -/
theorem massActionVectorField_addReaction_apply (N : Network S) (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (x : Concentration S) (s : S) :
    (N.addReaction q).massActionVectorField (κ.extendReaction q ε hε) x s =
      N.massActionVectorField κ x s +
        ε * q.source.massActionMonomial x * q.vector s := by
  rw [massActionVectorField_apply, massActionVectorField_apply]
  rw [sum_addReaction N q (fun r => (N.addReaction q).massActionRate
    (κ.extendReaction q ε hε) r x * (N.addReaction q).reactionVector r s)]
  simp [massActionRate, addReaction, RateConstants.extendReaction, reactionVector]

/-- Exact vector form of the one-reaction mass-action perturbation. -/
theorem massActionVectorField_addReaction (N : Network S) (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (x : Concentration S) :
    (N.addReaction q).massActionVectorField (κ.extendReaction q ε hε) x =
      N.massActionVectorField κ x +
        (ε * q.source.massActionMonomial x) • q.vector := by
  funext s
  rw [massActionVectorField_addReaction_apply]
  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- For every positive parameter, the smooth family is exactly the mass-action field of the
enlarged CRN with new reaction rate `ε`. -/
theorem massActionVectorField_addReaction_eq_family (N : Network S) (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (x : Concentration S) :
    (N.addReaction q).massActionVectorField (κ.extendReaction q ε hε) x =
      N.addedReactionFieldFamily κ q ε x := by
  exact N.massActionVectorField_addReaction q κ ε hε x

/-- Exact componentwise Jacobian perturbation after adding one reaction. -/
theorem massActionJacobian_addReaction_apply (N : Network S) (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (x : Concentration S) (i j : S) :
    (N.addReaction q).massActionJacobian (κ.extendReaction q ε hε) x i j =
      N.massActionJacobian κ x i j +
        ε * massActionMonomialGrad q.source x j * q.vector i := by
  simp only [massActionJacobian]
  rw [sum_addReaction N q (fun r => (κ.extendReaction q ε hε).k r *
    massActionMonomialGrad ((N.addReaction q).reaction r).source x j *
    (N.addReaction q).reactionVector r i)]
  simp [addReaction, RateConstants.extendReaction, reactionVector]

/-- Exact matrix form of the Jacobian perturbation. -/
theorem massActionJacobian_addReaction (N : Network S) (q : Reaction S)
    (κ : N.RateConstants) (ε : ℝ) (hε : 0 < ε) (x : Concentration S) :
    (N.addReaction q).massActionJacobian (κ.extendReaction q ε hε) x =
      N.massActionJacobian κ x +
        Matrix.of (fun i j => ε * massActionMonomialGrad q.source x j * q.vector i) := by
  ext i j
  exact N.massActionJacobian_addReaction_apply q κ ε hε x i j

/-- If the appended reaction is stoichiometrically dependent, the enlarged stoichiometric subspace
is exactly the original one. -/
theorem stoichSubspace_addReaction_eq (N : Network S) (q : Reaction S)
    (hdep : N.IsStoichiometricallyDependentReaction q) :
    (N.addReaction q).stoichSubspace = N.stoichSubspace := by
  apply le_antisymm
  · rw [stoichSubspace, Submodule.span_le]
    rintro v ⟨r, rfl⟩
    cases r with
    | inl r =>
        simpa using N.reactionVector_mem_stoichSubspace r
    | inr u =>
        cases u
        simpa [IsStoichiometricallyDependentReaction] using hdep
  · rw [stoichSubspace, Submodule.span_le]
    rintro v ⟨r, rfl⟩
    have hmem := (N.addReaction q).reactionVector_mem_stoichSubspace (Sum.inl r)
    simpa using hmem

/-- Consequently appending a stoichiometrically dependent reaction preserves stoichiometric rank. -/
theorem stoichRank_addReaction_eq (N : Network S) (q : Reaction S)
    (hdep : N.IsStoichiometricallyDependentReaction q) :
    (N.addReaction q).stoichRank = N.stoichRank := by
  unfold stoichRank
  rw [N.stoichSubspace_addReaction_eq q hdep]


/-! ## Closing a smooth-family periodic trajectory back to the enlarged CRN -/

/-- A positive periodic trajectory of the smooth one-reaction perturbation at a strictly positive
parameter is exactly a positive periodic mass-action orbit of the enlarged network.

This theorem is the semantic closure needed by regular-perturbation arguments: the IFT/Poincare
layer may work with the smooth real family `addedReactionFieldFamily`, including the reference
value `ε = 0`, while the CRN conclusion at `ε > 0` uses genuine positive rate constants. -/
noncomputable def positivePeriodicOrbitOfAddedReactionFamily
    (N : Network S) (q : Reaction S) (κ : N.RateConstants)
    {ε : ℝ} (hε : 0 < ε)
    (P : PeriodicTrajectory (N.addedReactionFieldFamily κ q ε))
    (hpos : ∀ t s, 0 < P.orbit t s) :
    (N.addReaction q).PositivePeriodicOrbit (κ.extendReaction q ε hε) where
  orbit := P.orbit
  period := P.period
  period_pos := P.period_pos
  positive := hpos
  solution := by
    intro t s
    have h := P.solution t
    have hs := hasDerivAt_pi.mp h s
    -- the goal carries the raw reaction sum; rewrite it into the family form first so
    -- `hs` (stated via `addedReactionFieldFamily`) matches.
    rw [N.massActionVectorField_addReaction_eq_family q κ ε hε (P.orbit t)]
    exact hs
  periodic := P.periodic
  nonconstant := P.nonconstant

/-- Propositional version of `positivePeriodicOrbitOfAddedReactionFamily`. -/
theorem hasPositivePeriodicOrbit_addReaction_of_family
    (N : Network S) (q : Reaction S) (κ : N.RateConstants)
    {ε : ℝ} (hε : 0 < ε)
    (P : PeriodicTrajectory (N.addedReactionFieldFamily κ q ε))
    (hpos : ∀ t s, 0 < P.orbit t s) :
    (N.addReaction q).HasPositivePeriodicOrbit (κ.extendReaction q ε hε) :=
  ⟨N.positivePeriodicOrbitOfAddedReactionFamily q κ hε P hpos⟩

/-- A single positive-parameter positive periodic trajectory in the smooth perturbation family
witnesses structural oscillatory capacity of the enlarged CRN. -/
theorem oscillatoryCapacity_addReaction_of_family_witness
    (N : Network S) (q : Reaction S) (κ : N.RateConstants)
    {ε : ℝ} (hε : 0 < ε)
    (P : PeriodicTrajectory (N.addedReactionFieldFamily κ q ε))
    (hpos : ∀ t s, 0 < P.orbit t s) :
    (N.addReaction q).OscillatoryCapacity :=
  ⟨κ.extendReaction q ε hε,
    N.hasPositivePeriodicOrbit_addReaction_of_family q κ hε P hpos⟩

/-- Proof-relevant witness package for the final step of a regular-perturbation inheritance proof.
Everything before this object may be performed in the smooth family through `ε=0`; this package
contains only the two genuinely CRN-specific facts needed at a selected positive parameter. -/
structure DependentReactionPeriodicWitness
    (N : Network S) (q : Reaction S) (κ : N.RateConstants) : Type where
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  orbit : PeriodicTrajectory (N.addedReactionFieldFamily κ q epsilon)
  positive : ∀ t s, 0 < orbit.orbit t s

namespace DependentReactionPeriodicWitness

/-- Convert a smooth-family witness into the actual enlarged-network positive periodic orbit. -/
noncomputable def toPositivePeriodicOrbit
    {N : Network S} {q : Reaction S} {κ : N.RateConstants}
    (W : DependentReactionPeriodicWitness N q κ) :
    (N.addReaction q).PositivePeriodicOrbit
      (κ.extendReaction q W.epsilon W.epsilon_pos) :=
  N.positivePeriodicOrbitOfAddedReactionFamily q κ W.epsilon_pos W.orbit W.positive

/-- Every smooth-family witness proves oscillatory capacity of the enlarged CRN. -/
theorem oscillatoryCapacity
    {N : Network S} {q : Reaction S} {κ : N.RateConstants}
    (W : DependentReactionPeriodicWitness N q κ) :
    (N.addReaction q).OscillatoryCapacity :=
  ⟨κ.extendReaction q W.epsilon W.epsilon_pos, ⟨W.toPositivePeriodicOrbit⟩⟩

end DependentReactionPeriodicWitness

/-- Concrete relation used by Banaji-style inheritance statements: `Nlarge` is obtained from
`Nsmall` by appending one stoichiometrically dependent reaction. -/
def IsSingleDependentReactionExtension (Nsmall Nlarge : Network S) : Prop :=
  ∃ q : Reaction S,
    Nsmall.IsStoichiometricallyDependentReaction q ∧ Nlarge = Nsmall.addReaction q

/-- Exact regular-perturbation theorem still needed to obtain nondegenerate oscillation inheritance
for a newly added dependent reaction.  All network algebra and rank preservation are already proved
above; this target is only periodic-orbit persistence under the small positive reaction rate. -/
def NondegenerateDependentReactionPersistenceTarget : Prop :=
  ∀ (N : Network S) (q : Reaction S),
    N.IsStoichiometricallyDependentReaction q →
    N.NondegenerateOscillatoryCapacity →
    (N.addReaction q).NondegenerateOscillatoryCapacity

/-- Stable analogue of `NondegenerateDependentReactionPersistenceTarget`. -/
def StableDependentReactionPersistenceTarget : Prop :=
  ∀ (N : Network S) (q : Reaction S),
    N.IsStoichiometricallyDependentReaction q →
    N.LinearlyStableOscillatoryCapacity →
    (N.addReaction q).LinearlyStableOscillatoryCapacity

end Network

end CRNT
