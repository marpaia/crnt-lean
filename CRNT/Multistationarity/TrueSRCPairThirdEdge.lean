import CRNT.Multistationarity.TrueChemistrySRGraph
import CRNT.Multistationarity.StrongConcordance
import CRNT.Multistationarity.TrueSRChordExtraction

/-!
# A c-pair forces an SR edge off the cycle

`TrueSRCycle.SToRIntersection` can only be realised against a cycle `C` if some *reaction* vertex
of `C` is incident to an SR edge that `C` does not use.  A shared component has to end at a
reaction vertex, and a reaction vertex of SR-degree two has both its edges inside whichever cycle
uses it, so the component would run past it.  Every construction of the second even cycle
therefore needs an edge outside `C`.

This file supplies one, from the c-pair condition alone.  If `C.isCPair j` then the two cycle
edges at `C.reaction j` carry the *same* endpoint complex, so both cycle species sit on one side
of the reaction.  The class is internal, so neither of its endpoint complexes is the zero complex
(`TrueReaction.Internal` unfolds to `¬ IsFlowChannel` at any representative), hence the opposite
side is nonempty and supplies a third species `w`.  Reactant/product separation puts `w` off the
occupied side, so `w` is neither cycle species — and then `reaction_injective` upgrades that to
`¬ C.ContainsEdge`, since an edge of `C` sharing `C.reaction j` must be one of the two edges at
index `j`.

Note what is *not* needed: `ZeroComplexReactionsAreFlows` plays no role.  Internality of the
reaction class is already enough to rule out a zero complex.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

-- A nonzero complex has a species occurring in it.
omit [DecidableEq S] [Fintype S] in
private theorem exists_occurring_of_ne_zero {c : Complex S} (hc : c ≠ Complex.zero) :
    ∃ w : S, c w ≠ 0 := by
  by_contra h
  refine hc (funext fun w => ?_)
  by_contra hw
  exact h ⟨w, hw⟩

/-- **A c-pair reaction carries an edge off the cycle.**

At a c-pair index both cycle edges label the same endpoint complex, so both cycle species lie on
one side of the reaction.  Internality forbids the other side from being the zero complex, and
separation keeps its species off the occupied side. -/
theorem exists_offCycle_edge_of_isCPair (N : Network S) (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (j : Fin n) (hpair : C.isCPair j) :
    ∃ f : N.TrueSREdge, f.reaction = C.reaction j ∧
      f.species ≠ (C.leftEdge j).species ∧ f.species ≠ (C.rightEdge j).species ∧
      ¬ C.ContainsEdge f := by
  classical
  -- the representative of the class at index `j`
  have hint : ¬ N.IsFlowChannel (C.leftEdge j).representative := by
    have hi : TrueReaction.Internal N (N.trueReaction (C.leftEdge j).representative) := by
      rw [(C.leftEdge j).representative_class]
      exact (C.leftEdge j).internal
    change ¬ N.IsFlowChannel (C.leftEdge j).representative at hi
    exact hi
  -- both cycle species occur in the shared endpoint complex
  have hL : (C.leftEdge j).endpoint (C.leftEdge j).species ≠ 0 := (C.leftEdge j).occurs
  have hR : (C.leftEdge j).endpoint (C.rightEdge j).species ≠ 0 := by
    rw [hpair]
    exact (C.rightEdge j).occurs
  -- an edge at `C.reaction j` whose species is neither cycle species is not a cycle edge
  have hnotContains : ∀ f : N.TrueSREdge, f.reaction = C.reaction j →
      f.species ≠ (C.leftEdge j).species → f.species ≠ (C.rightEdge j).species →
      ¬ C.ContainsEdge f := by
    intro f hfr hfL hfR hcont
    rcases hcont with ⟨t, hsame⟩ | ⟨t, hsame⟩
    · have htj : t = j := by
        apply C.reaction_injective
        rw [← C.left_reaction t, ← hsame.2.1, hfr]
      rw [htj] at hsame
      exact hfL hsame.1
    · have htj : t = j := by
        apply C.reaction_injective
        rw [← C.right_reaction t, ← hsame.2.1, hfr]
      rw [htj] at hsame
      exact hfR hsame.1
  rcases (C.leftEdge j).endpoint_is_source_or_target with hEs | hEt
  · -- the shared complex is the reactant side; the product side supplies `w`
    obtain ⟨w, hw⟩ := exists_occurring_of_ne_zero (fun h => hint (Or.inr h))
    have hoff : ∀ x : S, (C.leftEdge j).endpoint x ≠ 0 → w ≠ x := by
      intro x hx hwx
      have hsrc : (N.reaction (C.leftEdge j).representative).source x ≠ 0 := by
        rw [← hEs]; exact hx
      have htz := hsep (C.leftEdge j).representative x hsrc
      rw [← hwx] at htz
      exact hw htz
    refine ⟨{ species := w
              reaction := C.reaction j
              internal := by rw [← C.left_reaction j]; exact (C.leftEdge j).internal
              endpoint := (N.reaction (C.leftEdge j).representative).target
              representative := (C.leftEdge j).representative
              representative_class := by
                rw [(C.leftEdge j).representative_class]
                exact C.left_reaction j
              endpoint_is_source_or_target := Or.inr rfl
              occurs := hw }, rfl, hoff _ hL, hoff _ hR, ?_⟩
    exact hnotContains _ rfl (hoff _ hL) (hoff _ hR)
  · -- the shared complex is the product side; the reactant side supplies `w`
    obtain ⟨w, hw⟩ := exists_occurring_of_ne_zero (fun h => hint (Or.inl h))
    have hoff : ∀ x : S, (C.leftEdge j).endpoint x ≠ 0 → w ≠ x := by
      intro x hx hwx
      have htgt : (N.reaction (C.leftEdge j).representative).target x ≠ 0 := by
        rw [← hEt]; exact hx
      have htz := hsep (C.leftEdge j).representative w hw
      rw [hwx] at htz
      exact htgt htz
    refine ⟨{ species := w
              reaction := C.reaction j
              internal := by rw [← C.left_reaction j]; exact (C.leftEdge j).internal
              endpoint := (N.reaction (C.leftEdge j).representative).source
              representative := (C.leftEdge j).representative
              representative_class := by
                rw [(C.leftEdge j).representative_class]
                exact C.left_reaction j
              endpoint_is_source_or_target := Or.inl rfl
              occurs := hw }, rfl, hoff _ hL, hoff _ hR, ?_⟩
    exact hnotContains _ rfl (hoff _ hL) (hoff _ hR)

/-- The same conclusion in cycle-index form. -/
theorem exists_offCycle_edge_of_isCPair' (N : Network S) (hsep : N.ReactantProductSeparated)
    (C : N.TrueSRCycle n) (j : Fin n) (hpair : C.isCPair j) :
    ∃ f : N.TrueSREdge, f.reaction = C.reaction j ∧
      f.species ≠ C.species j ∧
      f.species ≠ C.species ⟨(j.1 + 1) % n, Nat.mod_lt _ (by have := C.nontrivial; omega)⟩ ∧
      ¬ C.ContainsEdge f := by
  obtain ⟨f, hfr, hfL, hfR, hcont⟩ := N.exists_offCycle_edge_of_isCPair hsep C j hpair
  refine ⟨f, hfr, ?_, ?_, hcont⟩
  · rw [← C.left_species j]; exact hfL
  · rw [← C.right_species j]; exact hfR

/-- **An even cycle with a c-pair always has material off the cycle.**  Contrapositive reading:
if every reaction of `C` has SR-degree two, then `C` has no c-pair at all, so `numCPairs C = 0`. -/
theorem exists_offCycle_edge_of_numCPairs_pos (N : Network S)
    (hsep : N.ReactantProductSeparated) (C : N.TrueSRCycle n) (h : 0 < C.numCPairs) :
    ∃ (j : Fin n) (f : N.TrueSREdge), f.reaction = C.reaction j ∧ ¬ C.ContainsEdge f := by
  classical
  have hne : (Finset.univ.filter C.isCPair).Nonempty := by
    rw [← Finset.card_pos]
    exact h
  obtain ⟨j, hj⟩ := hne
  obtain ⟨f, hfr, -, -, hcont⟩ :=
    N.exists_offCycle_edge_of_isCPair hsep C j (Finset.mem_filter.mp hj).2
  exact ⟨j, f, hfr, hcont⟩

/-- **The third edge leaves the cycle's species set too.**

Sharpening `exists_offCycle_edge_of_isCPair`: the species it produces cannot be *any* species of
`C`.  If it were, `f` would be a one-edge species-to-reaction chord of an even cycle — a cycle
species joined directly to a cycle reaction by an edge that is not a cycle edge — and that is
exactly what `no_single_edge_chord_of_trueSRCriterion` forbids.

So a c-pair on an even cycle reaches genuinely outside the cycle, in both coordinates. -/
theorem exists_offCycle_species_of_isCPair (N : Network S)
    (hsep : N.ReactantProductSeparated) (hSR : N.TrueSRStrongCriterion)
    (C : N.TrueSRCycle n) (hC : C.Even)
    (huniq : ∀ e f : N.TrueSREdge, e.reaction = f.reaction → e.species = f.species →
      e.endpoint = f.endpoint)
    (j : Fin n) (hpair : C.isCPair j) :
    ∃ f : N.TrueSREdge, f.reaction = C.reaction j ∧
      ¬ C.HasSpecies f.species ∧ ¬ C.ContainsEdge f := by
  obtain ⟨f, hfr, -, -, hcont⟩ := N.exists_offCycle_edge_of_isCPair hsep C j hpair
  have hoffL : ∀ t : Fin n, ¬ f.SameIncidence (C.leftEdge t) := by
    intro t hsame
    exact hcont (Or.inl ⟨t, hsame⟩)
  have hoffR : ∀ t : Fin n, ¬ f.SameIncidence (C.rightEdge t) := by
    intro t hsame
    exact hcont (Or.inr ⟨t, hsame⟩)
  refine ⟨f, hfr, ?_, hcont⟩
  rintro ⟨t, ht⟩
  exact no_single_edge_chord_of_trueSRCriterion hSR C hC huniq f t j ht.symm hfr hoffL hoffR

/-- **Which edges at a cycle reaction are cycle edges.**  Under separation an SR edge is
determined by its species and reaction, so an edge at `C.reaction k` lies on `C` exactly when its
species is one of `C.reaction k`'s two cycle neighbours.

This is the reusable form of a step used repeatedly on the `hSR.2` route: combined with the
causal orientation of `C` (reaction `C.reaction k` is negative at `C.species k` and positive at
`C.species ((k+1) % n)`), it says a *negative* causal edge into `C.reaction k` is a cycle edge iff
it comes from `C.species k`, and a *positive* causal edge out of it is a cycle edge iff it goes to
`C.species ((k+1) % n)`. -/
theorem containsEdge_iff_cycleNeighbour (N : Network S)
    (huniq : ∀ e f : N.TrueSREdge, e.reaction = f.reaction → e.species = f.species →
      e.endpoint = f.endpoint)
    (C : N.TrueSRCycle n) (e : N.TrueSREdge) (b k : Fin n)
    (hes : e.species = C.species b) (her : e.reaction = C.reaction k) :
    C.ContainsEdge e ↔ (b = k ∨ b.1 = (k.1 + 1) % n) := by
  have hn := C.nontrivial
  constructor
  · rintro (⟨t, hsame⟩ | ⟨t, hsame⟩)
    · have htk : t = k := by
        apply C.reaction_injective
        rw [← C.left_reaction t, ← hsame.2.1, her]
      refine Or.inl (C.species_injective ?_)
      rw [← hes, hsame.1, C.left_species t, htk]
    · have htk : t = k := by
        apply C.reaction_injective
        rw [← C.right_reaction t, ← hsame.2.1, her]
      have hsp : C.species b
          = C.species ⟨(k.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ := by
        rw [← hes, hsame.1, C.right_species t, htk]
      have hbk := C.species_injective hsp
      exact Or.inr (by rw [hbk])
  · rintro (hbk | hbk)
    · refine Or.inl ⟨k, ?_, ?_, ?_⟩
      · rw [hes, C.left_species k, hbk]
      · rw [her, C.left_reaction k]
      · exact huniq e (C.leftEdge k) (by rw [her, C.left_reaction k])
          (by rw [hes, C.left_species k, hbk])
    · refine Or.inr ⟨k, ?_, ?_, ?_⟩
      · rw [hes, C.right_species k]
        exact congrArg C.species (Fin.ext hbk)
      · rw [her, C.right_reaction k]
      · refine huniq e (C.rightEdge k) (by rw [her, C.right_reaction k]) ?_
        rw [hes, C.right_species k]
        exact congrArg C.species (Fin.ext hbk)

/-! ### Two even cycles meeting in a single edge -/

/-- **A single shared edge is already an S-to-R intersection.**

The classical condition asks that the *whole* common-edge subgraph be nonempty with every
connected component a simple path running from a species to a reaction.  When the two cycles share
exactly one edge there is one component, it has one edge, and its two endpoints are the edge's
species and reaction — so the condition holds outright.

This is the shape a computational search turns up.  The minimal network witnessing that the second
conjunct of `TrueSRStrongCriterion` cannot be dropped is
`B -> C`, `A -> C`, `A + B -> C` with all coefficients one: the cycles `{A,C}` and `{B,C}` are both
even, both are s-cycles for free, and they share exactly the edge `(C, A + B -> C)`.  Note that the
three-cycle through all of `A`, `B`, `C` is *odd* there — its single c-pair sits at `A + B -> C`,
where `A` and `B` are both reactants — so the criterion says nothing about it, and the failure is
located entirely in the pair of two-cycles. -/
theorem sToRIntersection_of_single_shared_edge (N : Network S) {m k : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle k) (e : N.TrueSREdge)
    (hCe : C.ContainsEdge e) (hDe : D.ContainsEdge e)
    (hunique : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f → f.SameIncidence e) :
    Nonempty (C.SToRIntersection D) := by
  classical
  refine ⟨{ componentCount := 1
            componentCount_pos := Nat.one_pos
            componentLength := fun _ => 1
            componentLength_pos := fun _ => Nat.one_pos
            edge := fun _ _ => e
            vertex := fun _ => ![Sum.inl e.species, Sum.inr ⟨e.reaction, e.internal⟩]
            edge_on_C := fun _ _ => hCe
            edge_on_D := fun _ _ => hDe
            connects := ?_
            edge_simple := ?_
            vertex_simple := ?_
            starts_at_species := ?_
            ends_at_reaction := ?_
            covers_common := ?_
            components_separated := ?_ }⟩
  · intro c i
    have hi : i = 0 := Subsingleton.elim i 0
    subst hi
    exact Or.inl ⟨by simp, by simp⟩
  · intro c i j _
    exact Subsingleton.elim i j
  · intro c a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  · intro c
    exact ⟨e.species, by simp⟩
  · intro c
    exact ⟨⟨e.reaction, e.internal⟩, by simp⟩
  · intro f hfC hfD
    exact ⟨0, 0, hunique f hfC hfD⟩
  · intro c d hcd
    exact absurd (Subsingleton.elim c d) hcd

/-- The criterion therefore forbids two even cycles from meeting in exactly one edge. -/
theorem false_of_single_shared_edge_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {m k : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle k) (hC : C.Even) (hD : D.Even)
    (e : N.TrueSREdge) (hCe : C.ContainsEdge e) (hDe : D.ContainsEdge e)
    (hunique : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f → f.SameIncidence e) :
    False :=
  hSR.2 C D hC hD (N.sToRIntersection_of_single_shared_edge C D e hCe hDe hunique)

end CRNT.Network
