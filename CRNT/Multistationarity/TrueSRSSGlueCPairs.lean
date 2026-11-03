import CRNT.Multistationarity.TrueSRSpeciesPath
import CRNT.Multistationarity.TrueSRGlueCPairs
import CRNT.Multistationarity.TrueChemistrySRGraph

/-!
# c-pairs of a species-to-species glue

`ssGlueCycle P Q h` is literally a `glueCycle`, obtained by moving `P`'s last edge onto `Q` so
that two species-to-species paths become two species-to-reaction ones.  So the bookkeeping of
`TrueSRGlueCPairs.lean` applies — but it applies in *shifted* coordinates, and the shift is the
whole point of this file.

For the species-to-reaction glue the identity reads `c(P') + seam + c(Q')`, with a genuine seam
term at the shared end reaction.  For the species-to-species glue that seam term is **not** an
extra degree of freedom: the shared end reaction of the reduced pair is the reaction of `P`'s last
edge, so the seam compares `P`'s two edges at its own last reaction — it *is* the c-pair
indicator of `P` there.  Every reaction vertex of `P ∪ Q` has both of its cycle edges drawn from a
single one of the two paths, because the two shared vertices are species and a c-pair lives only
at a reaction.  Hence

  `numCPairs (P ∪ Q) = c(P) + c(Q)`  with no seam term,

the opposite parity behaviour from `TrueSRParityLemma.three_glued_parity`.  The three pointwise
lemmas below are that statement position by position; `ssCPairAt_of_isCPair` packages them.

Consequence for the `hSR.2` route.  For a species-to-species chord `P` and the two species-arcs
`Q₁`, `Q₂` of a cycle `C`, the three pairwise glues satisfy, modulo 2,

  `numCPairs (P ∪ Q₁) + numCPairs (P ∪ Q₂) ≡ numCPairs (Q₁ ∪ Q₂) = numCPairs C`,

so `C.Even` forces `P ∪ Q₁` and `P ∪ Q₂` to have the *same* parity.  They are therefore both
even or both odd, and every pair among the three cycles meets in a species-to-species path
(`C ∩ (P ∪ Qₘ) = Qₘ`, and `(P ∪ Q₁) ∩ (P ∪ Q₂) = P`), so `SToRIntersection` is never available.
That is why a species-to-species chord is invisible to `TrueSRStrongCriterion`.
-/

namespace CRNT.Network.TrueSRSSPath

open CRNT.Network.TrueSRPath

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {i j : ℕ}
  (P : N.TrueSRSSPath (2 * j + 2)) (Q : N.TrueSRSSPath (2 * i + 2))
  (h : SSGluable P Q)

/-- The c-pair indicator at the `r`-th reaction of a species-to-species path. -/
def ssCPairAt {j : ℕ} (P : N.TrueSRSSPath (2 * j + 2)) (r : Fin (j + 1)) : Prop :=
  (P.edge ⟨2 * r.1, by have := r.isLt; omega⟩).endpoint
    = (P.edge ⟨2 * r.1 + 1, by have := r.isLt; omega⟩).endpoint

/-- Below the seam the condition is intrinsic to `P`. -/
theorem ssGlueCycle_isCPair_below (t : Fin (i + 1 + j + 1)) (ht : t.1 < j) :
    (ssGlueCycle P Q h).isCPair t ↔ ssCPairAt P ⟨t.1, by omega⟩ := by
  have htl := t.isLt
  rw [ssGlueCycle_eq,
    glueCycle_isCPair_below P.toPath (partner P Q h) (gluable_of_ssGluable P Q h) (by omega) t ht]
  rw [toPath_edge, toPath_edge]
  rfl

/-- At the seam the condition is still intrinsic to `P`: it compares `P`'s two edges at `P`'s own
last reaction, because the reduction to `glueCycle` moved `P`'s last edge onto `Q`. -/
theorem ssGlueCycle_isCPair_seam (hj : j < i + 1 + j + 1) :
    (ssGlueCycle P Q h).isCPair ⟨j, hj⟩ ↔ ssCPairAt P ⟨j, by omega⟩ := by
  rw [ssGlueCycle_eq,
    glueCycle_isCPair_seam (i := i + 1) (j := j) P.toPath (partner P Q h)
      (gluable_of_ssGluable P Q h) (by omega) (by omega)]
  rw [toPath_edge, partner,
    extend_edge_last Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h) (extend_hedge P Q h)
      ⟨2 * (i + 1), by omega⟩ (by show ¬ (2 * (i + 1) < 2 * i + 2); omega),
    lastEdge]
  constructor
  · intro hx
    exact hx.trans (congrArg _ (congrArg P.edge (Fin.ext (by show 2 * j + 2 - 1 = 2 * j + 1; omega))))
  · intro hx
    exact hx.trans (congrArg _ (congrArg P.edge (Fin.ext (by show 2 * j + 1 = 2 * j + 2 - 1; omega))))

/-- Above the seam the condition is intrinsic to `Q`, at the reversed index. -/
theorem ssGlueCycle_isCPair_above (t : Fin (i + 1 + j + 1)) (ht : j < t.1) :
    (ssGlueCycle P Q h).isCPair t ↔ ssCPairAt Q ⟨i + j + 1 - t.1, by have := t.isLt; omega⟩ := by
  have htl := t.isLt
  have hb2 : 2 * (i + 1) + 2 * j - 2 * t.1 < 2 * i + 2 := by omega
  have hb1 : 2 * (i + 1) + 2 * j - 2 * t.1 + 1 < 2 * i + 2 := by omega
  rw [ssGlueCycle_eq,
    glueCycle_isCPair_above P.toPath (partner P Q h) (gluable_of_ssGluable P Q h) (by omega) t ht]
  rw [partner,
    extend_edge_lt Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h) (extend_hedge P Q h)
      ⟨2 * (i + 1) + 2 * j - 2 * t.1 + 1, by omega⟩ hb1,
    extend_edge_lt Q P.lastEdge (extend_hes P Q h) (extend_hnew P Q h) (extend_hedge P Q h)
      ⟨2 * (i + 1) + 2 * j - 2 * t.1, by omega⟩ hb2]
  unfold ssCPairAt
  rw [show (⟨2 * (i + 1) + 2 * j - 2 * t.1, by omega⟩ : Fin (2 * i + 2))
      = ⟨2 * (i + j + 1 - t.1), by omega⟩ from
        Fin.ext (by show 2 * (i + 1) + 2 * j - 2 * t.1 = 2 * (i + j + 1 - t.1); omega),
    show (⟨2 * (i + 1) + 2 * j - 2 * t.1 + 1, by omega⟩ : Fin (2 * i + 2))
      = ⟨2 * (i + j + 1 - t.1) + 1, by omega⟩ from
        Fin.ext (by show 2 * (i + 1) + 2 * j - 2 * t.1 + 1 = 2 * (i + j + 1 - t.1) + 1; omega)]
  exact ⟨Eq.symm, Eq.symm⟩


/-! ### The count identity and its parity consequence -/

/-- The number of c-pairs of a species-to-species path. -/
noncomputable def ssNumCPairs {j : ℕ} (P : N.TrueSRSSPath (2 * j + 2)) : ℕ := by
  classical
  exact (Finset.univ.filter (ssCPairAt P)).card

/-- **The species-to-species glue count has no seam term.** -/
theorem ssGlueCycle_numCPairs :
    (ssGlueCycle P Q h).numCPairs = ssNumCPairs P + ssNumCPairs Q := by
  classical
  unfold TrueSRCycle.numCPairs ssNumCPairs
  have hsplit : (Finset.univ.filter (ssGlueCycle P Q h).isCPair).card
      = ((Finset.univ.filter (ssGlueCycle P Q h).isCPair).filter
            (fun t : Fin (i + 1 + j + 1) => t.1 ≤ j)).card
        + ((Finset.univ.filter (ssGlueCycle P Q h).isCPair).filter
            (fun t : Fin (i + 1 + j + 1) => ¬ t.1 ≤ j)).card :=
    (Finset.card_filter_add_card_filter_not
      (s := Finset.univ.filter (ssGlueCycle P Q h).isCPair)
      (fun t : Fin (i + 1 + j + 1) => t.1 ≤ j)).symm
  rw [hsplit]
  congr 1
  · -- below and at the seam: the low block matches `P`
    refine Finset.card_bij
      (fun t _ => (⟨min t.1 j, by omega⟩ : Fin (j + 1))) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      obtain ⟨hcp, hle⟩ := ht
      rcases Nat.lt_or_ge t.1 j with hlt | hge
      · rw [show (⟨min t.1 j, by omega⟩ : Fin (j + 1)) = ⟨t.1, by omega⟩ from
          Fin.ext (by show min t.1 j = t.1; omega)]
        exact (ssGlueCycle_isCPair_below P Q h t hlt).mp hcp
      · have heq : t.1 = j := by omega
        rw [show (⟨min t.1 j, by omega⟩ : Fin (j + 1)) = ⟨j, by omega⟩ from
          Fin.ext (by show min t.1 j = j; omega)]
        rw [show t = (⟨j, by omega⟩ : Fin (i + 1 + j + 1)) from Fin.ext heq] at hcp
        exact (ssGlueCycle_isCPair_seam P Q h (by omega)).mp hcp
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hv : min a.1 j = min b.1 j := congrArg Fin.val hab
      refine Fin.ext ?_
      show a.1 = b.1
      omega
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      have hrlt := r.isLt
      refine ⟨⟨r.1, by omega⟩, ⟨?_, by show r.1 ≤ j; omega⟩, ?_⟩
      · rcases Nat.lt_or_ge r.1 j with hlt | hge
        · refine (ssGlueCycle_isCPair_below P Q h ⟨r.1, by omega⟩ hlt).mpr ?_
          rw [show (⟨(⟨r.1, by omega⟩ : Fin (i + 1 + j + 1)).1, by omega⟩ : Fin (j + 1)) = r from
            Fin.ext (by show r.1 = r.1; rfl)]
          exact hr
        · have heq : r.1 = j := by omega
          rw [show (⟨r.1, by omega⟩ : Fin (i + 1 + j + 1))
              = (⟨j, by omega⟩ : Fin (i + 1 + j + 1)) from Fin.ext (by show r.1 = j; omega)]
          refine (ssGlueCycle_isCPair_seam P Q h (by omega)).mpr ?_
          rw [show (⟨j, by omega⟩ : Fin (j + 1)) = r from Fin.ext (by show j = r.1; omega)]
          exact hr
      · exact Fin.ext (by show min r.1 j = r.1; omega)
  · -- above the seam: the high block matches `Q`, at the reversed index
    refine Finset.card_bij
      (fun t _ => (⟨min (i + j + 1 - t.1) i, by omega⟩ : Fin (i + 1))) ?_ ?_ ?_
    · intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
      obtain ⟨hcp, hgt⟩ := ht
      have htl := t.isLt
      rw [show (⟨min (i + j + 1 - t.1) i, by omega⟩ : Fin (i + 1))
          = ⟨i + j + 1 - t.1, by omega⟩ from
        Fin.ext (by show min (i + j + 1 - t.1) i = i + j + 1 - t.1; omega)]
      exact (ssGlueCycle_isCPair_above P Q h t (by omega)).mp hcp
    · intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      have hal := a.isLt
      have hbl := b.isLt
      have hv : min (i + j + 1 - a.1) i = min (i + j + 1 - b.1) i := congrArg Fin.val hab
      refine Fin.ext ?_
      show a.1 = b.1
      omega
    · intro r hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
      have hrlt := r.isLt
      have hb : i + j + 1 - r.1 < i + 1 + j + 1 := by omega
      have hb2 : i + j + 1 - (i + j + 1 - r.1) < i + 1 := by omega
      refine ⟨⟨i + j + 1 - r.1, hb⟩, ⟨?_, by show ¬ i + j + 1 - r.1 ≤ j; omega⟩, ?_⟩
      · refine (ssGlueCycle_isCPair_above P Q h ⟨i + j + 1 - r.1, hb⟩
          (by show j < i + j + 1 - r.1; omega)).mpr ?_
        rw [show (⟨i + j + 1 - (⟨i + j + 1 - r.1, hb⟩ : Fin (i + 1 + j + 1)).1, hb2⟩
            : Fin (i + 1)) = r from
          Fin.ext (by show i + j + 1 - (i + j + 1 - r.1) = r.1; omega)]
        exact hr
      · exact Fin.ext (by
          show min (i + j + 1 - (i + j + 1 - r.1)) i = r.1
          omega)

/-- **The parity obstruction.**  Two species-to-species glues sharing the chord `P` always have
the *same* parity, as soon as the two partners' c-pair counts do — which is exactly what
`C.Even` supplies when the partners are the two species-arcs of `C`.

So the `hSR.2` route is unavailable for a species-to-species chord: the two candidate cycles are
either both even or both odd, and every pair among them and `C` meets in a species-to-species
path. -/
theorem ssGlueCycle_even_iff_even {i₁ i₂ j : ℕ}
    (P : N.TrueSRSSPath (2 * j + 2))
    (Q₁ : N.TrueSRSSPath (2 * i₁ + 2)) (Q₂ : N.TrueSRSSPath (2 * i₂ + 2))
    (h₁ : SSGluable P Q₁) (h₂ : SSGluable P Q₂)
    (hQ : (ssNumCPairs Q₁ + ssNumCPairs Q₂) % 2 = 0) :
    (ssGlueCycle P Q₁ h₁).Even ↔ (ssGlueCycle P Q₂ h₂).Even := by
  unfold TrueSRCycle.Even
  rw [Nat.even_iff, Nat.even_iff, ssGlueCycle_numCPairs P Q₁ h₁, ssGlueCycle_numCPairs P Q₂ h₂]
  omega

end CRNT.Network.TrueSRSSPath

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- **A species-to-species common subgraph cannot certify an `SToRIntersection`.**

When the common-edge subgraph of two true-SR cycles is one simple path with species at both
ends, criterion (ii) has no certificate for that pair.  The final vertex of any certificate
component is an endpoint of the component's last edge, hence one of the listed path's vertices.
If it were an interior vertex of the list, the list's other edge at that vertex is common as
well, so some component must cover it: the same component would then reach that vertex twice
against `vertex_simple`, a different component would share it against `components_separated`.
So the final vertex is one of the list's two endpoints — a species — contradicting
`ends_at_reaction`.

This is the formal version of "a species-to-species chord is invisible to
`TrueSRStrongCriterion`" from this file's header.  Note the subtle case is covered: the common
path may pass through reaction vertices in its interior — indeed it does when the common
subgraph is an arc closed off by a cycle right edge, which runs `s_{k+1} — r_k — … — s`, both
endpoints species — and still fails, because only the two *endpoints* of the whole common
subgraph matter. -/
theorem no_sToRIntersection_of_speciesSpecies_common {m n K : ℕ}
    (C : N.TrueSRCycle m) (D : N.TrueSRCycle n)
    (edge : Fin K → N.TrueSREdge) (vertex : Fin (K + 1) → N.TrueSRVertex)
    (hconn : ∀ i : Fin K, (edge i).Connects (vertex (Fin.castSucc i)) (vertex i.succ))
    (hvsimp : Function.Injective vertex)
    (hstart : ∃ s : S, vertex 0 = Sum.inl s)
    (hend : ∃ s : S, vertex (Fin.last K) = Sum.inl s)
    (hmem : ∀ i : Fin K, C.ContainsEdge (edge i) ∧ D.ContainsEdge (edge i))
    (hcover : ∀ f : N.TrueSREdge, C.ContainsEdge f → D.ContainsEdge f →
      ∃ i : Fin K, f.SameIncidence (edge i)) :
    ¬ Nonempty (C.SToRIntersection D) := by
  rintro ⟨I⟩
  have htrans : ∀ {e f g : N.TrueSREdge}, e.SameIncidence f → f.SameIncidence g →
      e.SameIncidence g := by
    intro e f g h1 h2
    exact ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩
  -- A vertex of the listed path at an edge is the edge's species- or reaction-endpoint.
  have hendsR : ∀ i : Fin K, ∀ u,
      u = vertex (Fin.castSucc i) ∨ u = vertex (Fin.succ i) →
      u = Sum.inl (edge i).species ∨
        u = Sum.inr ⟨(edge i).reaction, (edge i).internal⟩ := by
    intro i u hu
    rcases hconn i with hc | hc
    · obtain ⟨h1, h2⟩ := hc
      rcases hu with h | h
      · exact Or.inl (h.trans h1)
      · exact Or.inr (h.trans h2)
    · obtain ⟨h1, h2⟩ := hc
      rcases hu with h | h
      · exact Or.inr (h.trans h1)
      · exact Or.inl (h.trans h2)
  -- SameIncidence classes among the listed edges are unique.
  have hidx : ∀ i j : Fin K, (edge i).SameIncidence (edge j) → i = j := by
    intro i j h
    obtain ⟨hsi, hri, -⟩ := h
    rcases hconn i with hci | hci <;> rcases hconn j with hcj | hcj
    · obtain ⟨hi, hi'⟩ := hci
      obtain ⟨hj, hj'⟩ := hcj
      have hv : vertex (Fin.castSucc i) = vertex (Fin.castSucc j) := by
        rw [hi, hj, hsi]
      exact Fin.castSucc_injective _ (hvsimp hv)
    · obtain ⟨hi, hi'⟩ := hci
      obtain ⟨hj, hj'⟩ := hcj
      have ha : vertex (Fin.castSucc i) = vertex (Fin.succ j) := by
        rw [hi, hj', hsi]
      have hb : vertex (Fin.succ i) = vertex (Fin.castSucc j) := by
        rw [hi', hj]
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hri
      have hvala : i.val = j.val + 1 := congrArg Fin.val (hvsimp ha)
      have hvalb : i.val + 1 = j.val := congrArg Fin.val (hvsimp hb)
      omega
    · obtain ⟨hi, hi'⟩ := hci
      obtain ⟨hj, hj'⟩ := hcj
      have ha : vertex (Fin.succ i) = vertex (Fin.castSucc j) := by
        rw [hi', hj, hsi]
      have hb : vertex (Fin.castSucc i) = vertex (Fin.succ j) := by
        rw [hi, hj']
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hri
      have hvala : i.val + 1 = j.val := congrArg Fin.val (hvsimp ha)
      have hvalb : i.val = j.val + 1 := congrArg Fin.val (hvsimp hb)
      omega
    · obtain ⟨hi, hi'⟩ := hci
      obtain ⟨hj, hj'⟩ := hcj
      have hv : vertex (Fin.succ i) = vertex (Fin.succ j) := by
        rw [hi', hj', hsi]
      have h1 : Fin.succ i = Fin.succ j := hvsimp hv
      apply Fin.ext
      have hval : i.val + 1 = j.val + 1 := congrArg Fin.val h1
      omega
  -- The component that carries the certificate's final vertex.
  set c : Fin I.componentCount := ⟨0, I.componentCount_pos⟩
  have hclenpos : 0 < I.componentLength c := I.componentLength_pos c
  set lastIdx : Fin (I.componentLength c) := ⟨I.componentLength c - 1, by omega⟩
  have hlasteq : (Fin.last (I.componentLength c)) = Fin.succ lastIdx := by
    apply Fin.ext
    show I.componentLength c = (I.componentLength c - 1) + 1
    omega
  obtain ⟨ρ, hρ⟩ := I.ends_at_reaction c
  have hEnd : I.vertex c (Fin.succ lastIdx) = Sum.inr ρ := by
    rw [← hlasteq]; exact hρ
  have hcon : (I.edge c lastIdx).Connects (I.vertex c (Fin.castSucc lastIdx))
      (I.vertex c (Fin.succ lastIdx)) := I.connects c lastIdx
  have hEndInr : I.vertex c (Fin.succ lastIdx) =
      Sum.inr ⟨(I.edge c lastIdx).reaction, (I.edge c lastIdx).internal⟩ := by
    rcases hcon with h | h
    · exact h.2
    · have hbad : Sum.inr ρ = Sum.inl (I.edge c lastIdx).species := by
        rw [← hEnd]; exact h.2
      exact absurd hbad Sum.inr_ne_inl
  -- The component's last edge is common, hence listed.
  obtain ⟨iL, hiL⟩ := hcover (I.edge c lastIdx)
    (I.edge_on_C c lastIdx) (I.edge_on_D c lastIdx)
  have hEndListed : I.vertex c (Fin.succ lastIdx) = vertex (Fin.castSucc iL) ∨
      I.vertex c (Fin.succ lastIdx) = vertex (Fin.succ iL) := by
    rcases hconn iL with hc | hc
    · obtain ⟨h1, h2⟩ := hc
      right
      rw [h2, hEndInr]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact hiL.2.1
    · obtain ⟨h1, h2⟩ := hc
      left
      rw [h1, hEndInr]
      apply congrArg Sum.inr
      apply Subtype.ext
      exact hiL.2.1
  -- The final vertex is either an endpoint of the list (contradiction) or an interior
  -- vertex, in which case the neighbouring listed edge gives the covering component.
  obtain ⟨iElse, hiE, hEe⟩ : ∃ iElse : Fin K, iElse ≠ iL ∧
      (I.vertex c (Fin.succ lastIdx) = vertex (Fin.castSucc iElse) ∨
        I.vertex c (Fin.succ lastIdx) = vertex (Fin.succ iElse)) := by
    rcases hEndListed with hE | hE
    · -- final vertex = list vertex at castSucc iL
      by_cases hz : iL.1 = 0
      · obtain ⟨s0, hs0⟩ := hstart
        have hE0 : vertex (Fin.castSucc iL) = vertex (0 : Fin (K + 1)) := by
          apply congrArg vertex
          apply Fin.ext
          exact hz
        have hbad : Sum.inr ρ = Sum.inl s0 := by
          rw [← hEnd, hE, hE0]; exact hs0
        exact absurd hbad Sum.inr_ne_inl
      · refine ⟨⟨iL.1 - 1, by have := iL.isLt; omega⟩, ?_, ?_⟩
        · intro hcon2
          have hval : iL.1 - 1 = iL.1 := congrArg Fin.val hcon2
          omega
        · right
          have hfin : Fin.castSucc iL =
              Fin.succ ⟨iL.1 - 1, by have := iL.isLt; omega⟩ := by
            apply Fin.ext
            show iL.1 = (iL.1 - 1) + 1
            omega
          rw [hE, hfin]
    · -- final vertex = list vertex at Fin.succ iL
      by_cases hk : iL.1 + 1 = K
      · obtain ⟨sK, hsK⟩ := hend
        have hE0 : vertex (Fin.succ iL) = vertex (Fin.last K) := by
          apply congrArg vertex
          apply Fin.ext
          exact hk
        have hbad : Sum.inr ρ = Sum.inl sK := by
          rw [← hEnd, hE, hE0]; exact hsK
        exact absurd hbad Sum.inr_ne_inl
      · refine ⟨⟨iL.1 + 1, by have := iL.isLt; omega⟩, ?_, ?_⟩
        · intro hcon2
          have hval : iL.1 + 1 = iL.1 := congrArg Fin.val hcon2
          omega
        · left
          have hfin : Fin.succ iL =
              Fin.castSucc ⟨iL.1 + 1, by have := iL.isLt; omega⟩ := by
            apply Fin.ext
            rfl
          rw [hE, hfin]
  have hEndI : I.vertex c (Fin.succ lastIdx) =
      Sum.inr ⟨(edge iElse).reaction, (edge iElse).internal⟩ := by
    have hm := hendsR iElse (I.vertex c (Fin.succ lastIdx)) hEe
    rcases hm with h | h
    · exact absurd (h.symm.trans hEndInr) Sum.inl_ne_inr
    · exact h
  -- The neighbouring listed edge is common, hence covered by some component.
  obtain ⟨d, b, hd⟩ := I.covers_common (edge iElse) (hmem iElse).1 (hmem iElse).2
  by_cases hdc : d = c
  · subst hdc
    have hbne : b ≠ lastIdx := by
      intro hbe
      rw [hbe] at hd
      exact hiE (hidx iElse iL (htrans hd hiL))
    have hEqB : I.vertex c (Fin.succ lastIdx) = I.vertex c (Fin.castSucc b) ∨
        I.vertex c (Fin.succ lastIdx) = I.vertex c (Fin.succ b) := by
      have hconb := I.connects c b
      rcases hconb with hcb | hcb
      · obtain ⟨h1b, h2b⟩ := hcb
        right
        rw [h2b, hEndI]
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hd.2.1
      · obtain ⟨h1b, h2b⟩ := hcb
        left
        rw [h1b, hEndI]
        apply congrArg Sum.inr
        apply Subtype.ext
        exact hd.2.1
    rcases hEqB with hEq | hEq
    · have hfin : Fin.succ lastIdx = Fin.castSucc b := I.vertex_simple c hEq
      have hval : (I.componentLength c - 1) + 1 = b.1 := congrArg Fin.val hfin
      have hblt := b.isLt
      omega
    · have hfin : Fin.succ lastIdx = Fin.succ b := I.vertex_simple c hEq
      have hval : Nat.succ (I.componentLength c - 1) = Nat.succ b.1 := congrArg Fin.val hfin
      have hbeq : b = lastIdx := Fin.ext (Nat.succ_injective hval).symm
      exact hbne hbeq
  · -- distinct components cannot share the final vertex
    have hdc' : c ≠ d := Ne.symm hdc
    have h1 : (I.edge c lastIdx).reaction = (edge iElse).reaction :=
      (congrArg Subtype.val (Sum.inr.inj (hEndI.symm.trans hEndInr))).symm
    have h2 : (edge iElse).reaction = (I.edge d b).reaction := hd.2.1
    exact I.components_separated hdc' lastIdx b (Or.inr (h1.trans h2))

end CRNT.Network
