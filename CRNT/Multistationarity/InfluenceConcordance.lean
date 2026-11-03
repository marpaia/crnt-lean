import CRNT.Multistationarity.StrongConcordance

/-!
# Concordance relative to a general influence specification

Shinar--Feinberg concordance and strong concordance are two instances of a more
general construction.  For each reaction/species pair, an **influence
specification** records whether that species is permitted to induce (`+`),
inhibit (`-`), or not influence (`0`) the reaction rate.

* ordinary concordance uses the sign of the source complex;
* strong concordance uses the sign of `source-target`;
* arbitrary influence specifications permit regulatory species that need not
  occur in the reaction at all.

This file isolates the common sign theorem.  It contains no numerical search
procedure.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- Signed influence specification for every reaction/species pair. -/
structure InfluenceSpecification (N : Network S) where
  sign : N.R → S → SignType

/-- The ordinary reactant-only influence specification. -/
noncomputable def reactantInfluenceSpecification (N : Network S) :
    N.InfluenceSpecification where
  sign := fun r s => SignType.sign ((N.reaction r).source s : ℝ)

/-- The two-way reactant/product influence specification underlying strong
concordance. -/
noncomputable def twoWayInfluenceSpecification (N : Network S) :
    N.InfluenceSpecification where
  sign := fun r s => SignType.sign (N.reactionDirectionSign r s)

/-- A displacement promotes a reaction relative to an arbitrary influence
specification. -/
def InfluenceSpecification.Promotes (I : N.InfluenceSpecification)
    (r : N.R) (σ : S → ℝ) (s : S) : Prop :=
  I.sign r s ≠ 0 ∧ SignType.sign (σ s) = I.sign r s

/-- A displacement opposes a reaction relative to an arbitrary influence
specification. -/
def InfluenceSpecification.Opposes (I : N.InfluenceSpecification)
    (r : N.R) (σ : S → ℝ) (s : S) : Prop :=
  I.sign r s ≠ 0 ∧ SignType.sign (σ s) = - I.sign r s

/-- Forbidden witness for concordance relative to `I`. -/
structure InfluenceConcordanceWitness (I : N.InfluenceSpecification)
    (α : N.R → ℝ) (σ : S → ℝ) : Prop where
  mem_kerL : N.InKerL α
  mem_stoich : σ ∈ N.stoichSubspace
  sigma_ne : σ ≠ 0
  positive_reaction : ∀ r : N.R, 0 < α r → ∃ s : S, I.Promotes r σ s
  negative_reaction : ∀ r : N.R, α r < 0 → ∃ s : S, I.Opposes r σ s
  zero_reaction : ∀ r : N.R, α r = 0 →
    (∀ s : S, I.sign r s ≠ 0 → σ s = 0) ∨
      (∃ s t : S, I.Promotes r σ s ∧ I.Opposes r σ t)

/-- Concordance relative to an influence specification. -/
def ConcordantWith (N : Network S) (I : N.InfluenceSpecification) : Prop :=
  ¬ ∃ (α : N.R → ℝ) (σ : S → ℝ), InfluenceConcordanceWitness I α σ

namespace Kinetics

/-- Weak monotonicity relative to an arbitrary influence specification. -/
def WeaklyMonotonicWith (K : Kinetics N) (I : N.InfluenceSpecification) : Prop :=
  ∀ (x y : Concentration S), x.Nonnegative → y.Nonnegative → ∀ r : N.R,
    K.rate r x < K.rate r y → ∃ s : S, I.Promotes r (y - x) s

/-- Equality clause needed by the injectivity argument. -/
def EqualityCompatibleWith (K : Kinetics N) (I : N.InfluenceSpecification) : Prop :=
  ∀ (x y : Concentration S), x.Nonnegative → y.Nonnegative → ∀ r : N.R,
    K.rate r x = K.rate r y →
      (∀ s : S, I.sign r s ≠ 0 → x s = y s) ∨
      (∃ s t : S, I.Promotes r (y - x) s ∧ I.Opposes r (y - x) t)

/-- Combined general influence-monotonic kinetic class. -/
def InfluenceMonotonic (K : Kinetics N) (I : N.InfluenceSpecification) : Prop :=
  K.WeaklyMonotonicWith I ∧ K.EqualityCompatibleWith I

/-- Equal vector-field values generate the corresponding influence-concordance
witness. -/
theorem influenceConcordanceWitness_of_eq_vectorField
    {K : Kinetics N} {I : N.InfluenceSpecification}
    (hmono : K.InfluenceMonotonic I)
    {x y : Concentration S} (hx : x.Positive) (hy : y.Positive)
    (hmem : y - x ∈ N.stoichSubspace) (hne : x ≠ y)
    (hfield : K.vectorField x = K.vectorField y) :
    InfluenceConcordanceWitness I
      (fun r => K.rate r y - K.rate r x) (y - x) := by
  set α : N.R → ℝ := fun r => K.rate r y - K.rate r x with hα
  set σ : Concentration S := y - x with hσ
  have hker : N.InKerL α := by
    refine N.inKerL_of_apply fun s => ?_
    have hxy : K.vectorField x s = K.vectorField y s := by rw [hfield]
    have hsum : ∑ r : N.R, (K.rate r y - K.rate r x) * N.reactionVector r s
        = (∑ r : N.R, K.rate r y * N.reactionVector r s) -
          ∑ r : N.R, K.rate r x * N.reactionVector r s := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    simp only [hα]
    rw [hsum, ← K.vectorField_apply y s, ← K.vectorField_apply x s, ← hxy, sub_self]
  refine ⟨hker, hmem, ?_, ?_, ?_, ?_⟩
  · simpa [hσ, sub_ne_zero] using Ne.symm hne
  · intro r hr
    have hrate : K.rate r x < K.rate r y := by simp only [hα] at hr; linarith
    simpa [hσ] using hmono.1 x y hx.nonnegative hy.nonnegative r hrate
  · intro r hr
    have hrate : K.rate r y < K.rate r x := by simp only [hα] at hr; linarith
    obtain ⟨s, hs0, hs⟩ := hmono.1 y x hy.nonnegative hx.nonnegative r hrate
    refine ⟨s, hs0, ?_⟩
    simp only [hσ]
    rw [show (y - x) s = -((x - y) s) by simp]
    rw [Left.sign_neg, hs]
  · intro r hr
    have hrate : K.rate r x = K.rate r y := by simp only [hα] at hr; linarith
    rcases hmono.2 x y hx.nonnegative hy.nonnegative r hrate with heq | hopp
    · left
      intro s hs
      have hxy := heq s hs
      simp only [hσ, Pi.sub_apply, hxy, sub_self]
    · exact Or.inr hopp

end Kinetics

/-- **General influence injectivity theorem** (Shinar--Feinberg Proposition 9.18). -/
theorem injective_of_concordantWith
    {I : N.InfluenceSpecification} (hN : N.ConcordantWith I)
    {K : Kinetics N} (hK : K.InfluenceMonotonic I) : K.Injective := by
  intro x₀ x hx y hy hfield
  by_contra hxy
  have hmem : y - x ∈ N.stoichSubspace := by
    rw [← sub_sub_sub_cancel_right y x x₀]
    exact N.stoichSubspace.sub_mem hy.1 hx.1
  exact hN ⟨_, _, K.influenceConcordanceWitness_of_eq_vectorField hK
    hx.2 hy.2 hmem hxy hfield⟩

private theorem reactant_promotes_iff (N : Network S) (r : N.R) (σ : S → ℝ) (s : S) :
    N.reactantInfluenceSpecification.Promotes r σ s ↔
      (N.reaction r).source s ≠ 0 ∧ 0 < σ s := by
  rw [InfluenceSpecification.Promotes]
  simp only [reactantInfluenceSpecification]
  constructor
  · rintro ⟨hsign0, hsig⟩
    have hsrc : (N.reaction r).source s ≠ 0 := by
      intro hz
      simp [hz] at hsign0
    refine ⟨hsrc, ?_⟩
    have hsrcpos : 0 < (((N.reaction r).source s : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hsrc
    have hs1 : SignType.sign (((N.reaction r).source s : ℕ) : ℝ) = 1 :=
      sign_pos hsrcpos
    rw [hs1] at hsig
    exact sign_eq_one_iff.mp hsig
  · rintro ⟨hsrc, hσ⟩
    have hsrcpos : 0 < (((N.reaction r).source s : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hsrc
    have hs1 : SignType.sign (((N.reaction r).source s : ℕ) : ℝ) = 1 :=
      sign_pos hsrcpos
    refine ⟨?_, ?_⟩
    · rw [hs1]; simp
    · rw [hs1, sign_pos hσ]

private theorem reactant_opposes_iff (N : Network S) (r : N.R) (σ : S → ℝ) (s : S) :
    N.reactantInfluenceSpecification.Opposes r σ s ↔
      (N.reaction r).source s ≠ 0 ∧ σ s < 0 := by
  rw [InfluenceSpecification.Opposes]
  simp only [reactantInfluenceSpecification]
  constructor
  · rintro ⟨hsign0, hsig⟩
    have hsrc : (N.reaction r).source s ≠ 0 := by
      intro hz
      simp [hz] at hsign0
    refine ⟨hsrc, ?_⟩
    have hsrcpos : 0 < (((N.reaction r).source s : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hsrc
    have hs1 : SignType.sign (((N.reaction r).source s : ℕ) : ℝ) = 1 :=
      sign_pos hsrcpos
    rw [hs1] at hsig
    simpa using sign_eq_neg_one_iff.mp hsig
  · rintro ⟨hsrc, hσ⟩
    have hsrcpos : 0 < (((N.reaction r).source s : ℕ) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hsrc
    have hs1 : SignType.sign (((N.reaction r).source s : ℕ) : ℝ) = 1 :=
      sign_pos hsrcpos
    refine ⟨?_, ?_⟩
    · rw [hs1]; simp
    · rw [hs1, sign_neg hσ]

/-- Ordinary concordance is the reactant-influence specialization. -/
theorem concordantWith_reactant_iff (N : Network S) :
    N.ConcordantWith N.reactantInfluenceSpecification ↔ N.Concordant := by
  constructor
  · intro hI hC
    rcases hC with ⟨α, σ, W⟩
    apply hI
    refine ⟨α, σ, ?_⟩
    refine ⟨W.mem_kerL, W.mem_stoich, W.sigma_ne, ?_, ?_, ?_⟩
    · intro r har
      obtain ⟨s, hsrc, hsign⟩ := W.sign_match r har.ne'
      refine ⟨s, (reactant_promotes_iff N r σ s).2 ⟨hsrc, ?_⟩⟩
      have ha : SignType.sign (α r) = 1 := sign_pos har
      rw [ha] at hsign
      exact sign_eq_one_iff.mp hsign
    · intro r har
      obtain ⟨s, hsrc, hsign⟩ := W.sign_match r har.ne
      refine ⟨s, (reactant_opposes_iff N r σ s).2 ⟨hsrc, ?_⟩⟩
      have ha : SignType.sign (α r) = -1 := sign_neg har
      rw [ha] at hsign
      exact sign_eq_neg_one_iff.mp hsign
    · intro r har
      rcases W.sign_balance r har with hall | ⟨s, t, hs, ht, hneg, hpos⟩
      · left
        intro s hI
        apply hall s
        intro hz
        simp [hz, reactantInfluenceSpecification] at hI
      · right
        exact ⟨t, s, (reactant_promotes_iff N r σ t).2 ⟨ht, hpos⟩,
          (reactant_opposes_iff N r σ s).2 ⟨hs, hneg⟩⟩
  · intro hC hI
    rcases hI with ⟨α, σ, W⟩
    apply hC
    refine ⟨α, σ, ?_⟩
    refine ⟨W.mem_kerL, W.mem_stoich, W.sigma_ne, ?_, ?_⟩
    · intro r har
      rcases lt_or_gt_of_ne har with harneg | harpos
      · obtain ⟨s, hs⟩ := W.negative_reaction r harneg
        have hs' := (reactant_opposes_iff N r σ s).1 hs
        refine ⟨s, hs'.1, ?_⟩
        rw [sign_neg hs'.2, sign_neg harneg]
      · obtain ⟨s, hs⟩ := W.positive_reaction r harpos
        have hs' := (reactant_promotes_iff N r σ s).1 hs
        refine ⟨s, hs'.1, ?_⟩
        rw [sign_pos hs'.2, sign_pos harpos]
    · intro r har
      rcases W.zero_reaction r har with hall | ⟨s, t, hs, ht⟩
      · left
        intro s hsrc
        apply hall s
        have hsrcpos : 0 < (((N.reaction r).source s : ℕ) : ℝ) := by
          exact_mod_cast Nat.pos_of_ne_zero hsrc
        simp only [reactantInfluenceSpecification]
        rw [sign_pos hsrcpos]
        simp
      · right
        have hsp := (reactant_promotes_iff N r σ s).1 hs
        have hto := (reactant_opposes_iff N r σ t).1 ht
        exact ⟨t, s, hto.1, hsp.1, hto.2, hsp.2⟩

/-- Under source/product separation, strong concordance rules out every witness for the
all-active-species two-way influence specification.  This is the valid implication for the
current definitions.  The converse/equivalence previously stated here was too strong: the zero-rate
clause of `StrongConcordanceWitness` constrains source species only, whereas
`InfluenceConcordanceWitness` constrains every species with nonzero two-way influence. -/
theorem concordantWith_twoWay_of_stronglyConcordant
    (N : Network S) (hsep : N.ReactantProductSeparated)
    (hstrong : N.StronglyConcordant) :
    N.ConcordantWith N.twoWayInfluenceSpecification := by
  intro hex
  rcases hex with ⟨α, σ, W⟩
  apply hstrong
  refine ⟨α, σ, ?_⟩
  refine ⟨W.mem_kerL, W.mem_stoich, W.sigma_ne, ?_, ?_, ?_⟩
  · intro r ha
    obtain ⟨s, hs0, hs⟩ := W.positive_reaction r ha
    refine ⟨s, ?_, ?_⟩
    · simpa [twoWayInfluenceSpecification] using hs
    · have : N.reactionDirectionSign r s ≠ 0 := by
        simpa [twoWayInfluenceSpecification] using hs0
      exact this
  · intro r ha
    obtain ⟨s, hs0, hs⟩ := W.negative_reaction r ha
    refine ⟨s, ?_, ?_⟩
    · simpa [twoWayInfluenceSpecification] using hs
    · have : N.reactionDirectionSign r s ≠ 0 := by
        simpa [twoWayInfluenceSpecification] using hs0
      exact this
  · intro r ha
    rcases W.zero_reaction r ha with hall | ⟨s, t, hs, ht⟩
    · left
      intro s hsrc
      apply hall s
      have hdir : 0 < N.reactionDirectionSign r s := by
        rw [reactionDirectionSign, hsep r s hsrc]
        simp
        exact_mod_cast Nat.pos_of_ne_zero hsrc
      simp [twoWayInfluenceSpecification, sign_pos hdir]
    · right
      refine ⟨s, t, ?_, ?_⟩
      · rcases hs with ⟨hsgn, hdir⟩
        refine ⟨?_, ?_⟩
        · simpa [twoWayInfluenceSpecification] using hdir
        · simpa [twoWayInfluenceSpecification] using hsgn
      · rcases ht with ⟨hsgn, hdir⟩
        refine ⟨?_, ?_⟩
        · simpa [twoWayInfluenceSpecification] using hdir
        · simpa [twoWayInfluenceSpecification] using hsgn

end Network
end CRNT
