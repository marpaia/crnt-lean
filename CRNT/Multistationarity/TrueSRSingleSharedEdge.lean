import CRNT.Multistationarity.TrueChemistrySRGraph

/-!
# Making `hSR.2` usable: two even cycles cannot share exactly one edge

`TrueSRStrongCriterion`'s second conjunct — no species-to-reaction intersection between two even
cycles — is the one hypothesis unused anywhere in the true-SR development.  Establishing
`hreac` (reaction-class injectivity along the causal orbit) provably *requires* it: see
`hreac_needs_hSR.py`, which exhibits a separated, flow-free network with a valid witness and a
valid causal choice whose unique periodic orbit has period 3 with only two active true-reaction
classes, so class-injectivity fails by pigeonhole.  Since `trueInternalCauseReaction` is
`Classical.choose`, no proof of `hreac` from the witness structure plus separation can exist.

This file supplies the primitive that turns `hSR.2` into a usable tool.  A single shared edge is
already a legitimate S-to-R intersection certificate: as a one-edge component it is a simple
path whose two vertices are the edge's species and its reaction, so `starts_at_species` and
`ends_at_reaction` hold on the nose.  Hence **two even cycles sharing exactly one edge are
forbidden**.

This is the lemma the project's own design notes list as established ("two even cycles sharing
exactly one common edge produce a forbidden nonempty species-to-reaction intersection") but
which is in fact absent from the tree.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- **A single common S-to-R path is an intersection certificate.**

This is the general consumer form.  Banaji--Craciun's chord construction (arXiv:0809.1308,
Lemma 10) produces two even cycles whose intersection is a *path* — the chord — not necessarily
a single edge, so `hSR.2` has to be usable at that generality.  The path data are hypotheses
here; producing them from an e-cycle plus a chord is the open half. -/
noncomputable def TrueSRCycle.sToRIntersectionOfPath {m n : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n)
    (L : ℕ) (hL : 0 < L)
    (edge : Fin L → N.TrueSREdge) (vertex : Fin (L + 1) → N.TrueSRVertex)
    (hEC : ∀ i, C.ContainsEdge (edge i)) (hED : ∀ i, D.ContainsEdge (edge i))
    (hconn : ∀ i, (edge i).Connects (vertex (Fin.castSucc i)) (vertex i.succ))
    (hsimp : ∀ {i j}, (edge i).SameIncidence (edge j) → i = j)
    (hvinj : Function.Injective vertex)
    (hstart : ∃ s : S, vertex 0 = Sum.inl s)
    (hend : ∃ ρ : N.InternalTrueReaction, vertex (Fin.last L) = Sum.inr ρ)
    (hcov : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      ∃ i, f.SameIncidence (edge i)) :
    C.SToRIntersection D where
  componentCount := 1
  componentCount_pos := Nat.one_pos
  componentLength := fun _ => L
  componentLength_pos := fun _ => hL
  edge := fun _ => edge
  vertex := fun _ => vertex
  edge_on_C := fun _ => hEC
  edge_on_D := fun _ => hED
  connects := fun _ => hconn
  edge_simple := by
    intro _ i j h
    exact hsimp h
  vertex_simple := fun _ => hvinj
  starts_at_species := fun _ => hstart
  ends_at_reaction := fun _ => hend
  covers_common := by
    intro f h1 h2
    obtain ⟨i, hi⟩ := hcov f h1 h2
    exact ⟨0, i, hi⟩
  components_separated := by
    intro c d hcd
    exact absurd (Subsingleton.elim c d) hcd

/-- **Two even cycles cannot intersect in a single S-to-R path.** -/
theorem no_single_shared_path_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {m n : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n) (hC : C.Even) (hD : D.Even)
    (L : ℕ) (hL : 0 < L)
    (edge : Fin L → N.TrueSREdge) (vertex : Fin (L + 1) → N.TrueSRVertex)
    (hEC : ∀ i, C.ContainsEdge (edge i)) (hED : ∀ i, D.ContainsEdge (edge i))
    (hconn : ∀ i, (edge i).Connects (vertex (Fin.castSucc i)) (vertex i.succ))
    (hsimp : ∀ {i j}, (edge i).SameIncidence (edge j) → i = j)
    (hvinj : Function.Injective vertex)
    (hstart : ∃ s : S, vertex 0 = Sum.inl s)
    (hend : ∃ ρ : N.InternalTrueReaction, vertex (Fin.last L) = Sum.inr ρ)
    (hcov : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      ∃ i, f.SameIncidence (edge i)) :
    False :=
  hSR.2 C D hC hD
    ⟨C.sToRIntersectionOfPath D L hL edge vertex hEC hED hconn hsimp hvinj hstart hend hcov⟩

/-- A single common edge is an S-to-R intersection certificate. -/
noncomputable def TrueSRCycle.sToRIntersectionOfSingleEdge {m n : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n) (e : N.TrueSREdge)
    (heC : C.ContainsEdge e) (heD : D.ContainsEdge e)
    (huniq : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f → f.SameIncidence e) :
    C.SToRIntersection D where
  componentCount := 1
  componentCount_pos := Nat.one_pos
  componentLength := fun _ => 1
  componentLength_pos := fun _ => Nat.one_pos
  edge := fun _ _ => e
  vertex := fun _ i => if i = 0 then Sum.inl e.species else Sum.inr ⟨e.reaction, e.internal⟩
  edge_on_C := fun _ _ => heC
  edge_on_D := fun _ _ => heD
  connects := by
    intro c i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact Or.inl ⟨by simp, by simp⟩
  edge_simple := by
    intro c i j _
    exact Subsingleton.elim _ _
  vertex_simple := by
    intro c a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  starts_at_species := fun _ => ⟨e.species, by simp⟩
  ends_at_reaction := fun _ => ⟨⟨e.reaction, e.internal⟩, by simp⟩
  covers_common := by
    intro f hfC hfD
    exact ⟨0, 0, huniq f hfC hfD⟩
  components_separated := by
    intro c d hcd
    exact absurd (Subsingleton.elim c d) hcd

/-- **Two even cycles cannot share exactly one edge.**  First use of `hSR.2` in the
development. -/
theorem no_single_shared_edge_of_trueSRCriterion (N : Network S)
    (hSR : N.TrueSRStrongCriterion) {m n : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n) (hC : C.Even) (hD : D.Even)
    (e : N.TrueSREdge) (heC : C.ContainsEdge e) (heD : D.ContainsEdge e)
    (huniq : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f → f.SameIncidence e) :
    False :=
  hSR.2 C D hC hD ⟨C.sToRIntersectionOfSingleEdge D e heC heD huniq⟩

end CRNT.Network
