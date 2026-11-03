import CRNT.Dynamics.SingleLinkageGAC
import CRNT.Decision.Linkage
import CRNT.Geometry.EndotacticGlobal

/-!
# Single-linkage structure for global persistence

This module turns the numerical/propositional single-linkage condition into the concrete graph
statement needed by geometric persistence proofs: every pair of network complexes is linked.
For a weakly reversible network that immediately upgrades to directed reachability in both
directions through `WeaklyReversible.reaches_of_linked`.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every pair of complexes that actually occurs in the network lies in the same linkage class. -/
def AllComplexesLinked (N : Network S) : Prop :=
  ∀ (c : Complex S), c ∈ N.complexes →
    ∀ (d : Complex S), d ∈ N.complexes → N.Linked c d

/-- A one-linkage-class network has all of its occurring complexes linked.  The proof goes through
Mathlib's connected-component quotient, whose cardinality is exactly `numLinkageClasses`. -/
theorem allComplexesLinked_of_singleLinkageClass (N : Network S)
    (hslc : N.SingleLinkageClass) : N.AllComplexesLinked := by
  intro c hc d hd
  have hcard : Fintype.card N.linkageGraph.ConnectedComponent = 1 := by
    rw [← N.numLinkageClasses_eq_card_connectedComponent]
    exact hslc
  obtain ⟨q, hq⟩ := Fintype.card_eq_one_iff.mp hcard
  let c' : {z : Complex S // z ∈ N.complexes} := ⟨c, hc⟩
  let d' : {z : Complex S // z ∈ N.complexes} := ⟨d, hd⟩
  have heq : N.linkageGraph.connectedComponentMk c' =
      N.linkageGraph.connectedComponentMk d' := by
    calc
      N.linkageGraph.connectedComponentMk c' = q := hq _
      _ = N.linkageGraph.connectedComponentMk d' := (hq _).symm
  exact (N.linked_iff_reachable c' d').2 (SimpleGraph.ConnectedComponent.exact heq)

/-- In the weakly reversible single-linkage case, every occurring complex reaches every other
occurring complex by a directed reaction path. -/
theorem WeaklyReversible.reaches_of_singleLinkageClass {N : Network S}
    (hwr : N.WeaklyReversible) (hslc : N.SingleLinkageClass)
    {c d : Complex S} (hc : c ∈ N.complexes) (hd : d ∈ N.complexes) : N.Reaches c d :=
  hwr.reaches_of_linked (N.allComplexesLinked_of_singleLinkageClass hslc c hc d hd)

/-- A nonempty finite reaction set always has a source maximizing `wValue`. -/
theorem exists_isMaxSource_of_nonempty (N : Network S) (w : S → ℝ)
    (hne : Nonempty N.R) : ∃ r : N.R, N.IsMaxSource w r := by
  classical
  let vals : Finset ℝ := Finset.univ.image (N.wValue w)
  have hvals : vals.Nonempty := by
    obtain ⟨r₀⟩ := hne
    exact ⟨N.wValue w r₀, by simp [vals]⟩
  let m : ℝ := vals.max' hvals
  have hm : m ∈ vals := by
    dsimp [m]
    exact Finset.max'_mem vals hvals
  obtain ⟨r, _hruniv, hrm⟩ := Finset.mem_image.mp hm
  refine ⟨r, ?_⟩
  intro r'
  have hr'mem : N.wValue w r' ∈ vals := by simp [vals]
  have hle : N.wValue w r' ≤ m := by
    dsimp [m]
    exact Finset.le_max' vals (N.wValue w r') hr'mem
  rw [hrm]
  exact hle

/-- Along a directed path that starts at a `w`-maximal reaction source and ends at a
strictly lower-valued reaction source, some reaction on the path leaves a maximal source
and has strictly negative `wRate`.

This is the finite path lemma behind the standard proof that a weakly reversible
single-linkage network is strongly endotactic. -/
theorem Reaches.exists_maxSource_strict_drop {N : Network S} {w : S → ℝ}
    {rmax rlow : N.R} (hmax : N.IsMaxSource w rmax)
    (hreach : N.Reaches (N.reaction rmax).source (N.reaction rlow).source)
    (hlow : N.wValue w rlow < N.wValue w rmax) :
    ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0 := by
  classical
  let cmax : Complex S := (N.reaction rmax).source
  have hpath : ∀ {d : Complex S}, N.Reaches cmax d →
      (∃ rd : N.R, (N.reaction rd).source = d) →
      complexWValue w d < complexWValue w cmax →
      ∃ r : N.R, N.IsMaxSource w r ∧ N.wRate w r < 0 := by
    intro d hcd hdsrc hdlt
    induction hcd with
    | refl => exact (lt_irrefl _ hdlt).elim
    | @tail e f hce hef ih =>
        obtain ⟨redge, hs, ht⟩ := hef
        have he_le : complexWValue w e ≤ complexWValue w cmax := by
          have hm := hmax redge
          rw [wValue_eq_complexWValue_source, hs] at hm
          rw [wValue_eq_complexWValue_source] at hm
          exact hm
        by_cases heq : complexWValue w e = complexWValue w cmax
        · refine ⟨redge, ?_, ?_⟩
          · intro r'
            have hm := hmax r'
            rw [wValue_eq_complexWValue_source] at hm ⊢
            rw [N.wValue_eq_complexWValue_source w redge] at *
            rw [hs, heq]
            exact hm
          · rw [N.wRate_eq_complexWValue_sub w redge, hs, ht, heq]
            linarith
        · have helt : complexWValue w e < complexWValue w cmax := lt_of_le_of_ne he_le heq
          exact ih ⟨redge, hs⟩ helt
  apply hpath hreach
  · exact ⟨rlow, rfl⟩
  · simpa only [wValue_eq_complexWValue_source] using hlow

/-- **Weakly reversible + one linkage class ⇒ strongly endotactic (standard definition).**

For a stoichiometrically active direction, weak reversibility turns the target of an active
reaction into another reaction source, so the source functional is nonconstant.  Choose a
maximal source.  Single linkage plus weak reversibility provides a directed path from that
maximal source to a lower source.  `Reaches.exists_maxSource_strict_drop` extracts the first
strict drop from the maximal face. -/
theorem WeaklyReversible.stronglyEndotacticStd_of_singleLinkageClass {N : Network S}
    (hwr : N.WeaklyReversible) (hslc : N.SingleLinkageClass) : N.StronglyEndotacticStd := by
  refine ⟨hwr.endotactic, ?_⟩
  intro w hactive
  obtain ⟨ra, hrate_ne⟩ := hactive
  obtain ⟨rt, hrt⟩ := hwr.exists_source_eq_target ra
  have hsrc_ne : N.wValue w ra ≠ N.wValue w rt := by
    intro heq
    apply hrate_ne
    rw [N.wRate_eq_complexWValue_sub w ra]
    have hpot : complexWValue w (N.reaction ra).target =
        complexWValue w (N.reaction ra).source := by
      calc
        complexWValue w (N.reaction ra).target = N.wValue w rt := by
          rw [wValue_eq_complexWValue_source, hrt]
        _ = N.wValue w ra := heq.symm
        _ = complexWValue w (N.reaction ra).source := wValue_eq_complexWValue_source N w ra
    rw [hpot, sub_self]
  obtain ⟨rmax, hmax⟩ := N.exists_isMaxSource_of_nonempty w ⟨ra⟩
  have hra_le : N.wValue w ra ≤ N.wValue w rmax := hmax ra
  have hrt_le : N.wValue w rt ≤ N.wValue w rmax := hmax rt
  obtain ⟨rlow, hlow⟩ : ∃ rlow : N.R, N.wValue w rlow < N.wValue w rmax := by
    by_cases hra_eq : N.wValue w ra = N.wValue w rmax
    · refine ⟨rt, ?_⟩
      have hne : N.wValue w rt ≠ N.wValue w rmax := by
        intro h
        apply hsrc_ne
        calc
          N.wValue w ra = N.wValue w rmax := hra_eq
          _ = N.wValue w rt := h.symm
      exact lt_of_le_of_ne hrt_le hne
    · exact ⟨ra, lt_of_le_of_ne hra_le hra_eq⟩
  have hreach : N.Reaches (N.reaction rmax).source (N.reaction rlow).source :=
    hwr.reaches_of_singleLinkageClass hslc (N.source_mem_complexes rmax)
      (N.source_mem_complexes rlow)
  exact Reaches.exists_maxSource_strict_drop hmax hreach hlow

end Network
end CRNT
