import CRNT.Multistationarity.TrueChemistrySRCriterion

/-!
# What the causal-cycle constructor actually supplies

`no_degree_two_causal_cycle` is the proved endgame of the true-SR argument.  To use it one must
feed it a cycle satisfying `hrep`, `hσ`, `hcausal`, `hopp`, `hrest`.  This file records exactly
which of those the existing constructor `trueSRCycleOfPeriodicCausalOrbit` provides.

* `hrep` is free (both edges at a position are built from the same cause reaction).
* `hσ` is free (cycle species are active by construction).
* `hcausal`/`hopp` are supplied **with the opposite orientation**: along the causal orbit the
  cycle's *incoming* reaction at a species opposes that species' sign and the *outgoing* one is
  causal for it, which is the mirror of what `no_degree_two_causal_cycle` asks.
* `hrest` is the genuine open gap (the source-block decomposition).
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The chosen representative of a labelled edge is the reaction it was built from, in both
branches of the direction split. -/
@[simp] theorem trueSREdgeOfReactionVectorNe_representative (N : Network S)
    (r : N.R) (hrint : ¬ N.IsFlowChannel r) (s : S) (hrs : N.reactionVector r s ≠ 0) :
    (N.trueSREdgeOfReactionVectorNe r hrint s hrs).representative = r := by
  unfold trueSREdgeOfReactionVectorNe
  split <;> rfl

section
variable (N : Network S) (hflow : N.ZeroComplexReactionsAreFlows)
  {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (W : N.fullyOpen.StrongConcordanceWitness α σ)

@[simp] theorem trueInternalCausalLeftEdge_representative (s : {s : S // σ s ≠ 0}) :
    (N.trueInternalCausalLeftEdge hflow W s).representative =
      (N.trueInternalCauseReaction hflow W s).1 := by
  unfold trueInternalCausalLeftEdge
  simp

@[simp] theorem trueInternalCausalRightEdge_representative (s : {s : S // σ s ≠ 0}) :
    (N.trueInternalCausalRightEdge hflow W s).representative =
      (N.trueInternalCauseReaction hflow W s).1 := by
  unfold trueInternalCausalRightEdge
  simp

/-- **`hrep` is free.**  The two edges at one cycle position share their representative. -/
theorem trueInternalCausalEdges_representative_eq (s : {s : S // σ s ≠ 0}) :
    (N.trueInternalCausalLeftEdge hflow W s).representative =
      (N.trueInternalCausalRightEdge hflow W s).representative := by
  simp

/-- The cause reaction is causal at the species it was chosen for: this is the sign that the
constructor's **left** edge carries. -/
theorem causal_at_left (s : {s : S // σ s ≠ 0}) :
    0 < (α (Sum.inl (N.trueInternalCausalLeftEdge hflow W s).representative) *
      N.reactionVector (N.trueInternalCausalLeftEdge hflow W s).representative s.1) * σ s.1 := by
  rw [trueInternalCausalLeftEdge_representative]
  exact N.trueInternalCauseReaction_pos hflow W s

/-- The same reaction *opposes* the next species: this is the sign that the constructor's
**right** edge carries. -/
theorem opposing_at_right (s : {s : S // σ s ≠ 0}) :
    (α (Sum.inl (N.trueInternalCausalRightEdge hflow W s).representative) *
      N.reactionVector (N.trueInternalCausalRightEdge hflow W s).representative
        (N.trueInternalCausalSpeciesStep hflow W s).1) *
      σ (N.trueInternalCausalSpeciesStep hflow W s).1 < 0 := by
  rw [trueInternalCausalRightEdge_representative]
  exact N.trueInternalOppositeSpecies_neg W (N.trueInternalCauseReaction hflow W s)

end

/-! ### The constructed cycle cannot satisfy `no_degree_two_causal_cycle`'s `hopp`

`no_degree_two_causal_cycle` requires, at every position `j = finRotate n i`, that the **left**
edge's flux term at `C.species j` be strictly *negative* (`hopp`).  The causal-orbit constructor
delivers the opposite: the left edge at a position is the cause reaction chosen *for that very
species*, so its flux term there is strictly *positive*.  The two conventions are mirror images,
and the endgame lemma is therefore not applicable to this constructor as both are currently
stated. -/

section Constructed

variable (N : Network S) (hflow : N.ZeroComplexReactionsAreFlows)
  {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (W : N.fullyOpen.StrongConcordanceWitness α σ)
  (s : {s : S // σ s ≠ 0})
  (hsper : s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W))
  (hperiod : 2 ≤ Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s)
  (hreac : Function.Injective (fun i : Fin (Function.minimalPeriod
    (N.trueInternalCausalSpeciesStep hflow W) s) =>
      N.trueReaction (N.trueInternalCauseReaction hflow W
        ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1))

/-- At every position of the constructed causal cycle, the left edge's flux term at that
position's species is **strictly positive**. -/
theorem constructed_left_causal
    (i : Fin (Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s)) :
    0 < (α (Sum.inl ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod
          hreac).leftEdge i).representative) *
        N.reactionVector ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod
          hreac).leftEdge i).representative
          ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod hreac).species i)) *
      σ ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod hreac).species i) := by
  simpa [trueSRCycleOfPeriodicCausalOrbit] using
    causal_at_left N hflow W ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)

/-- Hence the `hopp` hypothesis of `no_degree_two_causal_cycle` is **unsatisfiable** for the
cycle the constructor produces. -/
theorem constructed_hopp_false :
    ¬ (∀ i : Fin (Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s),
        (α (Sum.inl ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod
              hreac).leftEdge (finRotate _ i)).representative) *
            N.reactionVector ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod
              hreac).leftEdge (finRotate _ i)).representative
              ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod
                hreac).species (finRotate _ i))) *
          σ ((N.trueSRCycleOfPeriodicCausalOrbit hflow W s hsper hperiod
            hreac).species (finRotate _ i)) < 0) := by
  intro h
  have hz : 0 < Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s := by
    omega
  haveI : NeZero (Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s) := ⟨by omega⟩
  have hpos := constructed_left_causal N hflow W s hsper hperiod hreac
    (finRotate _ (⟨0, hz⟩ : Fin _))
  exact absurd (h ⟨0, hz⟩) (not_lt.mpr hpos.le)

end Constructed

/-! ### `hreac` is nearly free

`hreac` asks that the causal orbit never revisit a true-reaction *class*.  At the level of
*channels* this is automatic: `trueInternalOppositeSpecies` depends only on the chosen reaction,
so two orbit positions with the same cause would have the same successor, contradicting
injectivity of the orbit's species.  The only way `hreac` can fail is therefore for the orbit to
use two **distinct channels of one true reaction** — that is, both directions of a reversible
pair. -/

private theorem mod_succ_inj {n a b : ℕ} (ha : a < n) (hb : b < n)
    (h : (a + 1) % n = (b + 1) % n) : a = b := by
  rcases Nat.lt_or_ge (a + 1) n with h1 | h1 <;> rcases Nat.lt_or_ge (b + 1) n with h2 | h2
  · rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at h; omega
  · have hb2 : b + 1 = n := by omega
    rw [Nat.mod_eq_of_lt h1, hb2, Nat.mod_self] at h; omega
  · have ha2 : a + 1 = n := by omega
    rw [ha2, Nat.mod_self, Nat.mod_eq_of_lt h2] at h; omega
  · omega

section Orbit

variable (N : Network S) (hflow : N.ZeroComplexReactionsAreFlows)
  {α : N.fullyOpen.R → ℝ} {σ : S → ℝ} (W : N.fullyOpen.StrongConcordanceWitness α σ)

/-- **The cause channel is injective along a minimal periodic causal orbit.**

`trueInternalOppositeSpecies` depends only on the chosen reaction, so two orbit positions with
the same cause have the same successor; the orbit's species are distinct, so the positions
coincide. -/
theorem trueInternalCause_injective_on_orbit
    (s : {s : S // σ s ≠ 0})
    (hsper : s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W)) :
    Function.Injective (fun i : Fin (Function.minimalPeriod
      (N.trueInternalCausalSpeciesStep hflow W) s) =>
        (N.trueInternalCauseReaction hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1) := by
  intro i j hij
  have hcause : N.trueInternalCauseReaction hflow W
        ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)
      = N.trueInternalCauseReaction hflow W
        ((N.trueInternalCausalSpeciesStep hflow W)^[j.1] s) := Subtype.ext hij
  have hstep : N.trueInternalCausalSpeciesStep hflow W
        ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)
      = N.trueInternalCausalSpeciesStep hflow W
        ((N.trueInternalCausalSpeciesStep hflow W)^[j.1] s) :=
    congrArg (N.trueInternalOppositeSpecies W) hcause
  rw [N.trueInternalPeriodicSpecies_succ hflow W s hsper i,
    N.trueInternalPeriodicSpecies_succ hflow W s hsper j] at hstep
  have hi2 := i.isLt
  have hj2 := j.isLt
  have hlt : 0 < Function.minimalPeriod (N.trueInternalCausalSpeciesStep hflow W) s := by omega
  have heq := N.trueInternalPeriodicSpecies_injective hflow W s hsper
    (a₁ := ⟨_, Nat.mod_lt _ hlt⟩) (a₂ := ⟨_, Nat.mod_lt _ hlt⟩)
    (congrArg Subtype.val hstep)
  exact Fin.ext (mod_succ_inj hi2 hj2 (congrArg Fin.val heq))

/-- **Consequently `hreac` follows from a single statement about reversible pairs**: the orbit
never uses two distinct channels of the same true reaction (both directions of a reversible
pair).  This is all that separates the canonical causal orbit from being a true-SR cycle. -/
theorem hreac_of_no_reversible_reuse
    (s : {s : S // σ s ≠ 0})
    (hsper : s ∈ Function.periodicPts (N.trueInternalCausalSpeciesStep hflow W))
    (hno : ∀ i j : Fin (Function.minimalPeriod
      (N.trueInternalCausalSpeciesStep hflow W) s),
        N.trueReaction (N.trueInternalCauseReaction hflow W
            ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1
          = N.trueReaction (N.trueInternalCauseReaction hflow W
            ((N.trueInternalCausalSpeciesStep hflow W)^[j.1] s)).1 →
        (N.trueInternalCauseReaction hflow W
            ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1
          = (N.trueInternalCauseReaction hflow W
            ((N.trueInternalCausalSpeciesStep hflow W)^[j.1] s)).1) :
    Function.Injective (fun i : Fin (Function.minimalPeriod
      (N.trueInternalCausalSpeciesStep hflow W) s) =>
        N.trueReaction (N.trueInternalCauseReaction hflow W
          ((N.trueInternalCausalSpeciesStep hflow W)^[i.1] s)).1) :=
  fun i j hij =>
    trueInternalCause_injective_on_orbit N hflow W s hsper (hno i j hij)

end Orbit

/-! ### Towards `hreac`: the reuse lemma

An exhaustive search (`cancel_check3.py`, `disjunct_diag.py`) over 83 088 reuse configurations
at two and three species found that whenever two distinct channels of one true reaction both
carry a nonzero witness coefficient, **each** channel has both a promoting and an opposing
species — and that the `zero_reaction` field's source-support disjunct is never the one doing
the work.  That makes the following the exact statement needed to normalise a witness so the
causal orbit cannot reuse a true reaction, and hence to discharge `hreac`.

The same-sign half is proved here.  The opposite-sign half is **not**: the witness conditions
alone do not supply it (both `0 < α q` and `α r < 0` yield the *same* fact, `Opposes r`), so it
needs the `InKerL`/`σ = g` structure and remains open. -/

/-- Reversing a reaction's orientation exchanges promoting and opposing. -/
theorem promotes_iff_opposes_of_reversed (M : Network S) {r q : M.R} (σ : S → ℝ)
    (hs : (M.reaction q).source = (M.reaction r).target)
    (ht : (M.reaction q).target = (M.reaction r).source) (s : S) :
    M.Promotes q σ s ↔ M.Opposes r σ s := by
  have hd : M.reactionDirectionSign q s = -M.reactionDirectionSign r s := by
    simp only [Network.reactionDirectionSign]
    rw [hs, ht]
    ring
  have hne : (M.reactionDirectionSign q s ≠ 0) ↔ (M.reactionDirectionSign r s ≠ 0) := by
    rw [hd, neg_ne_zero]
  have hsg : SignType.sign (M.reactionDirectionSign q s)
      = -SignType.sign (M.reactionDirectionSign r s) := by
    rw [hd]
    first
      | exact Left.sign_neg _
      | exact sign_neg _
      | simp
  unfold Network.Promotes Network.Opposes
  rw [hsg, hne]

/-- **Same-sign reuse case.**  If two channels of one true reaction carry witness coefficients
of the same sign, then each has both a promoting and an opposing species — exactly the
`zero_reaction` disjunct needed to zero one of them out. -/
theorem reversed_pair_promotes_and_opposes (M : Network S)
    {α : M.R → ℝ} {σ : S → ℝ} (W : M.StrongConcordanceWitness α σ)
    {r q : M.R}
    (hs : (M.reaction q).source = (M.reaction r).target)
    (ht : (M.reaction q).target = (M.reaction r).source)
    (hsign : (0 < α r ∧ 0 < α q) ∨ (α r < 0 ∧ α q < 0)) :
    (∃ s, M.Promotes r σ s) ∧ (∃ s, M.Opposes r σ s) := by
  -- the transfer in the other direction, obtained by swapping the two channels
  have hswap : ∀ s, M.Promotes r σ s ↔ M.Opposes q σ s :=
    fun s => promotes_iff_opposes_of_reversed M σ ht.symm hs.symm s
  rcases hsign with ⟨hr, hq⟩ | ⟨hr, hq⟩
  · obtain ⟨s, hsp⟩ := W.positive_reaction r hr
    obtain ⟨t, htp⟩ := W.positive_reaction q hq
    exact ⟨⟨s, hsp⟩, ⟨t, (promotes_iff_opposes_of_reversed M σ hs ht t).mp htp⟩⟩
  · obtain ⟨s, hso⟩ := W.negative_reaction r hr
    obtain ⟨t, hto⟩ := W.negative_reaction q hq
    exact ⟨⟨t, (hswap t).mpr hto⟩, ⟨s, hso⟩⟩

end CRNT.Network
