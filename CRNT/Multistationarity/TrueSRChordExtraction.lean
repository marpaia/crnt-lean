import CRNT.Multistationarity.TrueSRCycleSplit
import CRNT.Multistationarity.TrueSRMidSegment
import CRNT.Multistationarity.TrueSREdgePath

/-!
# Extracting a chord from a path whose ends lie on the cycle

This closes the graph-theoretic half of the `hSR.2` route.  `TrueSRCycleSplit.lean` forbids a
chord of an even cycle -- a species-to-reaction path with both endpoints on the cycle, interior
off it, and no cycle edge.  What a producer actually hands over is weaker: a species-to-reaction
path whose two *endpoints* lie on the cycle, with no control at all over what happens in
between.

`no_spanning_path_of_trueSRCriterion` bridges the gap.  Mark the positions of the path that
carry cycle vertices; positions `0` and `L` are marked and `L` is odd, so by
`exists_odd_gap_of_odd` two consecutive marked positions sit an odd distance apart.  That gap
has no marked position inside it, and odd length means it runs species-to-reaction (use
`midSegment`) or reaction-to-species (use `midSegmentRev`).  Either way it is a path of the
right shape with interior off the cycle, and
`no_offCycle_interior_path_of_trueSRCriterion` supplies the missing edge-disjointness for free.

The one hypothesis that survives is `hnd`: no such gap is a single edge.  A one-edge gap joins
a cycle species directly to a cycle reaction, and that edge may itself be a cycle edge, in
which case no chord arises -- the same degeneracy the existing `no_nonneighbor_chord` isolates
with its non-neighbour side conditions.
-/

namespace CRNT.Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S} {n : ℕ}

open TrueSRPath TrueSRCycle

/-- **The single-edge chord.**  An SR edge joining a species of `C` to a reaction of `C` which
is not itself a cycle edge forces `False`.

`huniq` is what reactant/product separation supplies: two SR edges with the same reaction class
and the same species carry the same endpoint complex.  With it, the edge's species index can be
neither the reaction's own index nor its successor -- in either case `huniq` would identify the
edge with the corresponding cycle edge -- so the one-edge degeneracy hypothesis of
`no_chord_at_of_trueSRCriterion` is discharged rather than assumed. -/
theorem no_single_edge_chord_of_trueSRCriterion (hSR : N.TrueSRStrongCriterion)
    (C : N.TrueSRCycle n) (hC : C.Even)
    (huniq : ∀ e f : N.TrueSREdge, e.reaction = f.reaction → e.species = f.species →
      e.endpoint = f.endpoint)
    (e : N.TrueSREdge) (j k : Fin n)
    (hes : e.species = C.species j) (her : e.reaction = C.reaction k)
    (hoffL : ∀ t : Fin n, ¬ e.SameIncidence (C.leftEdge t))
    (hoffR : ∀ t : Fin n, ¬ e.SameIncidence (C.rightEdge t)) :
    False := by
  have hn : 2 ≤ n := C.nontrivial
  have hj := j.isLt
  have hk := k.isLt
  -- the species index is not the reaction's own index
  have hkj : k.1 ≠ j.1 := by
    intro heq
    have hjk : j = k := Fin.ext heq.symm
    refine hoffL k ⟨?_, ?_, ?_⟩
    · rw [hes, C.left_species k, hjk]
    · rw [her, C.left_reaction k]
    · exact huniq e (C.leftEdge k) (by rw [her, C.left_reaction k])
        (by rw [hes, C.left_species k, hjk])
  -- nor its successor
  have hjk1 : j.1 ≠ (k.1 + 1) % n := by
    intro heq
    have hjk : j = ⟨(k.1 + 1) % n, Nat.mod_lt _ (by omega)⟩ := Fin.ext heq
    refine hoffR k ⟨?_, ?_, ?_⟩
    · rw [hes, C.right_species k, hjk]
    · rw [her, C.right_reaction k]
    · exact huniq e (C.rightEdge k) (by rw [her, C.right_reaction k])
        (by rw [hes, C.right_species k, hjk])
  -- so the rotated reaction position is neither `0` nor `n - 1`
  have hmod : (k.1 + (n - j.1)) % n = if j.1 ≤ k.1 then k.1 - j.1 else k.1 + (n - j.1) := by
    by_cases hle : j.1 ≤ k.1
    · rw [if_pos hle]
      have hrw : k.1 + (n - j.1) = (k.1 - j.1) + n := by omega
      rw [hrw, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    · rw [if_neg hle, Nat.mod_eq_of_lt (by omega)]
  have hsucc : (k.1 + 1) % n = if k.1 + 1 < n then k.1 + 1 else 0 := by
    by_cases hlt : k.1 + 1 < n
    · rw [if_pos hlt, Nat.mod_eq_of_lt hlt]
    · rw [if_neg hlt]
      have : k.1 + 1 = n := by omega
      rw [this, Nat.mod_self]
  have hnd : 0 < (k.1 + (n - j.1)) % n ∧ (k.1 + (n - j.1)) % n + 1 < n := by
    rw [hmod]
    by_cases hle : j.1 ≤ k.1
    · rw [if_pos hle]
      refine ⟨by omega, ?_⟩
      rw [hsucc] at hjk1
      by_cases hlt : k.1 + 1 < n
      · rw [if_pos hlt] at hjk1; omega
      · rw [if_neg hlt] at hjk1; omega
    · rw [if_neg hle]
      refine ⟨by omega, ?_⟩
      rw [hsucc] at hjk1
      by_cases hlt : k.1 + 1 < n
      · rw [if_pos hlt] at hjk1; omega
      · rw [if_neg hlt] at hjk1; omega
  refine no_chord_at_of_trueSRCriterion hSR C hC j k (TrueSREdge.toPath e) ?_ ?_ ?_ ?_ ?_
    (fun _ => hnd)
  · rw [TrueSREdge.toPath_startSpecies, hes]
  · rw [TrueSREdge.toPath_endReaction]
    exact her
  · intro p hp0 hp1 _
    have := p.isLt
    omega
  · intro p t hsame
    rw [TrueSREdge.toPath_edge] at hsame
    exact hoffL t hsame
  · intro p t hsame
    rw [TrueSREdge.toPath_edge] at hsame
    exact hoffR t hsame

/-- **A species-to-reaction path with both endpoints on an even cycle is forbidden**, provided
the path never traverses a cycle edge between two on-cycle positions.

Mark the positions carrying cycle vertices.  Position `0` and position `M` are marked and `M`
is odd, so `exists_odd_gap_of_odd` produces two consecutive marked positions an odd distance
apart, with nothing marked strictly between.  A gap of length at least three is a chord with
interior off the cycle (`no_offCycle_interior_path_of_trueSRCriterion`); a gap of length one is
a single-edge chord (`no_single_edge_chord_of_trueSRCriterion`), which `hnd` says is not a cycle
edge. -/
theorem no_spanning_path_of_trueSRCriterion (hSR : N.TrueSRStrongCriterion) {M : ℕ}
    (C : N.TrueSRCycle n) (hC : C.Even)
    (huniq : ∀ e f : N.TrueSREdge, e.reaction = f.reaction → e.species = f.species →
      e.endpoint = f.endpoint)
    (Q : N.TrueSRPath M)
    (h0 : C.HasVertex (Q.vertex ⟨0, by omega⟩))
    (hlast : C.HasVertex (Q.vertex ⟨M, by omega⟩))
    (hnd : ∀ p : Fin M, C.HasVertex (Q.vertex (Fin.castSucc p)) →
      C.HasVertex (Q.vertex p.succ) →
      (∀ t : Fin n, ¬ (Q.edge p).SameIncidence (C.leftEdge t)) ∧
      (∀ t : Fin n, ¬ (Q.edge p).SameIncidence (C.rightEdge t))) :
    False := by
  classical
  have hModd : M % 2 = 1 := Nat.odd_iff.mp Q.odd_length
  obtain ⟨a, b, hab, hbM, hMa, hMb, hpar, hbetween⟩ :=
    CRNT.exists_odd_gap_of_odd
      (fun p => ∃ h : p < M + 1, C.HasVertex (Q.vertex ⟨p, h⟩)) M
      ⟨by omega, h0⟩ ⟨by omega, hlast⟩ hModd
  obtain ⟨ha, hCa⟩ := hMa
  obtain ⟨hb, hCb⟩ := hMb
  by_cases hb1 : b - a = 1
  · -- a single-edge gap: the edge joins a cycle species to a cycle reaction
    have hbeq : b = a + 1 := by omega
    subst hbeq
    have hae : a < M := by omega
    have hcast : C.HasVertex (Q.vertex (Fin.castSucc (⟨a, hae⟩ : Fin M))) := hCa
    have hsucc : C.HasVertex (Q.vertex ((⟨a, hae⟩ : Fin M).succ)) := hCb
    obtain ⟨hoffL, hoffR⟩ := hnd ⟨a, hae⟩ hcast hsucc
    rcases Q.connects ⟨a, hae⟩ with ⟨hu, hv⟩ | ⟨hu, hv⟩
    · rw [hu] at hcast
      rw [hv] at hsucc
      obtain ⟨j, hj⟩ := hcast
      obtain ⟨k, hk⟩ := hsucc
      exact no_single_edge_chord_of_trueSRCriterion hSR C hC huniq
        (Q.edge ⟨a, hae⟩) j k hj.symm hk.symm hoffL hoffR
    · rw [hu] at hcast
      rw [hv] at hsucc
      obtain ⟨k, hk⟩ := hcast
      obtain ⟨j, hj⟩ := hsucc
      exact no_single_edge_chord_of_trueSRCriterion hSR C hC huniq
        (Q.edge ⟨a, hae⟩) j k hj.symm hk.symm hoffL hoffR
  · -- a longer gap: a chord with interior off the cycle
    rcases Nat.even_or_odd a with hae | hao
    · have ha2 : a % 2 = 0 := Nat.even_iff.mp hae
      have hb2 : b % 2 = 1 := by omega
      refine no_offCycle_interior_path_of_trueSRCriterion hSR C hC
        (Q.midSegment a b ha2 hb2 hab hbM) ?_ ?_ ?_ (by omega)
      · rw [Q.midSegment_startSpecies a b ha2 hb2 hab hbM]
        have hv := hCa
        rw [Q.vertex_eq_speciesAt ⟨a, ha⟩ ha2] at hv
        exact hv
      · rw [Q.midSegment_endReaction a b ha2 hb2 hab hbM]
        have hv := hCb
        rw [Q.vertex_eq_reactionAt ⟨b, hb⟩ (by show b % 2 ≠ 0; omega)] at hv
        exact hv
      · intro p hp0 hpK hv
        have hplt := p.isLt
        rw [Q.midSegment_vertex a b ha2 hb2 hab hbM p] at hv
        exact hbetween (a + p.1) (by omega) (by omega) ⟨by omega, hv⟩
    · have ha2 : a % 2 = 1 := Nat.odd_iff.mp hao
      have hb2 : b % 2 = 0 := by omega
      refine no_offCycle_interior_path_of_trueSRCriterion hSR C hC
        (Q.midSegmentRev a b ha2 hb2 hab hbM) ?_ ?_ ?_ (by omega)
      · rw [Q.midSegmentRev_startSpecies a b ha2 hb2 hab hbM]
        have hv := hCb
        rw [Q.vertex_eq_speciesAt ⟨b, hb⟩ hb2] at hv
        exact hv
      · rw [Q.midSegmentRev_endReaction a b ha2 hb2 hab hbM]
        have hv := hCa
        rw [Q.vertex_eq_reactionAt ⟨a, ha⟩ (by show a % 2 ≠ 0; omega)] at hv
        exact hv
      · intro p hp0 hpK hv
        have hplt := p.isLt
        rw [Q.midSegmentRev_vertex a b ha2 hb2 hab hbM p] at hv
        exact hbetween (b - p.1) (by omega) (by omega) ⟨by omega, hv⟩

end CRNT.Network
