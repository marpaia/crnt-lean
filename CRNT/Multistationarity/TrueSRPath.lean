import CRNT.Multistationarity.TrueSRSingleSharedEdge

/-!
# Species-to-reaction paths in the true-SR graph

The development so far only ever touches the true-SR graph through the rigid `TrueSRCycle`
structure.  Both remaining obligations of the true-SR theorem — `hreac` and `hrestM` — need
*paths*: the producer lemmas from the literature are

* Banaji--Craciun (arXiv:0809.1308, Lemma 10): an e-cycle `C` plus a path joining a species
  vertex of `C` to a reaction vertex of `C` and edge-disjoint from `C` yields two e-cycles with
  S-to-R intersection;
* Shinar--Feinberg (arXiv:1203.6560, Appendix A.2, Lemmas A.4/A.5): three edge-disjoint paths
  between two reaction vertices (resp. two species vertices) — if two of the three cycles formed
  are even, so is the third.

This file introduces the path notion those lemmas quantify over.  It is the component data of
`TrueSRCycle.SToRIntersection` packaged on its own, so a path is exactly what
`no_single_shared_path_of_trueSRCriterion` consumes.

The substantive result here is `TrueSRPath.odd_length`: a species-to-reaction path has **odd**
length.  This is forced by alternation — a path's vertices alternate between species and
reaction vertices — and it confirms that the repository's `SToRIntersection` matches the
literature's characterisation of an S-to-R intersection as one whose components have odd length
(Banaji, arXiv:0903.1190).
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- A simple species-to-reaction path in the true-SR graph: a vertex-injective alternating edge
sequence starting at a species vertex and ending at a reaction vertex. -/
structure TrueSRPath (N : Network S) (L : ℕ) where
  length_pos : 0 < L
  edge : Fin L → N.TrueSREdge
  vertex : Fin (L + 1) → N.TrueSRVertex
  connects : ∀ i, (edge i).Connects (vertex (Fin.castSucc i)) (vertex i.succ)
  edge_simple : ∀ {i j}, (edge i).SameIncidence (edge j) → i = j
  vertex_simple : Function.Injective vertex
  starts_at_species : ∃ s : S, vertex 0 = Sum.inl s
  ends_at_reaction : ∃ ρ : N.InternalTrueReaction, vertex (Fin.last L) = Sum.inr ρ

namespace TrueSRPath

variable {L : ℕ}

/-- Every vertex is a species vertex or a reaction vertex. -/
private theorem reaction_of_not_species (v : N.TrueSRVertex)
    (h : ¬ ∃ s : S, v = Sum.inl s) : ∃ ρ : N.InternalTrueReaction, v = Sum.inr ρ := by
  cases v with
  | inl s => exact absurd ⟨s, rfl⟩ h
  | inr ρ => exact ⟨ρ, rfl⟩

/-- A species vertex is followed by a reaction vertex. -/
theorem succ_of_species (P : N.TrueSRPath L) {k : ℕ} (hk : k < L)
    (h : ∃ s : S, P.vertex ⟨k, by omega⟩ = Sum.inl s) :
    ∃ ρ : N.InternalTrueReaction, P.vertex ⟨k + 1, by omega⟩ = Sum.inr ρ := by
  obtain ⟨s, hs⟩ := h
  have hc := P.connects ⟨k, hk⟩
  have h1 : (Fin.castSucc (⟨k, hk⟩ : Fin L)) = (⟨k, by omega⟩ : Fin (L + 1)) := by
    apply Fin.ext; simp
  have h2 : (⟨k, hk⟩ : Fin L).succ = (⟨k + 1, by omega⟩ : Fin (L + 1)) := by
    apply Fin.ext; simp
  rw [h1, h2] at hc
  rcases hc with ⟨_, hv⟩ | ⟨hu, _⟩
  · exact ⟨_, hv⟩
  · rw [hs] at hu; exact absurd hu (by simp)

/-- A reaction vertex is followed by a species vertex. -/
theorem succ_of_reaction (P : N.TrueSRPath L) {k : ℕ} (hk : k < L)
    (h : ∃ ρ : N.InternalTrueReaction, P.vertex ⟨k, by omega⟩ = Sum.inr ρ) :
    ∃ s : S, P.vertex ⟨k + 1, by omega⟩ = Sum.inl s := by
  obtain ⟨ρ, hρ⟩ := h
  have hc := P.connects ⟨k, hk⟩
  have h1 : (Fin.castSucc (⟨k, hk⟩ : Fin L)) = (⟨k, by omega⟩ : Fin (L + 1)) := by
    apply Fin.ext; simp
  have h2 : (⟨k, hk⟩ : Fin L).succ = (⟨k + 1, by omega⟩ : Fin (L + 1)) := by
    apply Fin.ext; simp
  rw [h1, h2] at hc
  rcases hc with ⟨hu, _⟩ | ⟨_, hv⟩
  · rw [hρ] at hu; exact absurd hu (by simp)
  · exact ⟨_, hv⟩

/-- **Alternation.**  A path's position `k` carries a species vertex exactly when `k` is even. -/
theorem species_iff_even (P : N.TrueSRPath L) :
    ∀ k : ℕ, ∀ hk : k ≤ L, (∃ s : S, P.vertex ⟨k, by omega⟩ = Sum.inl s) ↔ Even k := by
  intro k
  induction k with
  | zero =>
    intro _
    have h0 : (0 : Fin (L + 1)) = (⟨0, by omega⟩ : Fin (L + 1)) := by apply Fin.ext; simp
    constructor
    · intro _
      exact ⟨0, rfl⟩
    · intro _
      rw [← h0]
      exact P.starts_at_species
  | succ m ih =>
    intro hk
    have hm : m < L := by omega
    have hmle : m ≤ L := by omega
    rcases Nat.even_or_odd m with hev | hod
    · -- species at `m`, so a reaction at `m+1`
      obtain ⟨ρ, hρ⟩ := P.succ_of_species hm ((ih hmle).mpr hev)
      constructor
      · rintro ⟨s, hs⟩
        rw [hρ] at hs
        exact absurd hs (by simp)
      · intro hodd
        exact absurd hev (Nat.even_add_one.mp hodd)
    · -- reaction at `m`, so a species at `m+1`
      have hns : ¬ ∃ s : S, P.vertex ⟨m, by omega⟩ = Sum.inl s := by
        intro hs
        exact absurd ((ih hmle).mp hs) (Nat.not_even_iff_odd.mpr hod)
      obtain ⟨s, hs⟩ := P.succ_of_reaction hm (reaction_of_not_species _ hns)
      exact ⟨fun _ => Nat.even_add_one.mpr (Nat.not_even_iff_odd.mpr hod),
        fun _ => ⟨s, hs⟩⟩

/-- **A species-to-reaction path has odd length.**  This matches the literature's
characterisation of an S-to-R intersection as one all of whose components have odd length. -/
theorem odd_length (P : N.TrueSRPath L) : Odd L := by
  obtain ⟨ρ, hρ⟩ := P.ends_at_reaction
  have hL : (Fin.last L) = (⟨L, by omega⟩ : Fin (L + 1)) := by apply Fin.ext; simp
  rw [hL] at hρ
  have hns : ¬ ∃ s : S, P.vertex ⟨L, by omega⟩ = Sum.inl s := by
    rintro ⟨s, hs⟩
    rw [hρ] at hs
    exact absurd hs (by simp)
  have : ¬ Even L := fun h => hns ((P.species_iff_even L le_rfl).mpr h)
  exact Nat.not_even_iff_odd.mp this

end TrueSRPath

/-- **Two even cycles cannot intersect in a single species-to-reaction path**, stated against
the path structure.  This is the interface the producer lemmas should target. -/
theorem no_shared_path_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {m n : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n) (hC : C.Even) (hD : D.Even)
    {L : ℕ} (P : N.TrueSRPath L)
    (hEC : ∀ i, C.ContainsEdge (P.edge i)) (hED : ∀ i, D.ContainsEdge (P.edge i))
    (hcov : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      ∃ i, f.SameIncidence (P.edge i)) :
    False :=
  no_single_shared_path_of_trueSRCriterion N hSR C D hC hD L P.length_pos P.edge P.vertex
    hEC hED P.connects P.edge_simple P.vertex_simple P.starts_at_species P.ends_at_reaction hcov

end CRNT.Network
