import CRNT.Multistationarity.TrueSRParityLemma
import CRNT.Multistationarity.TrueSRSingleSharedEdge

/-!
# An S-to-R chord splits an even cycle into a forbidden intersection

Three pairwise edge-disjoint paths with the same species and reaction endpoints form three
cycles.  The parity lemma says their c-pair counts sum to an odd number.  If the cycle made from
the two original arcs is even, exactly one of the two cycles using the chord is even.  That cycle
and the original cycle share one of the arcs, itself an S-to-R path, contradicting the second
conjunct of `TrueSRStrongCriterion`.
-/

namespace CRNT.Network

open Finset TrueSRPath TrueSREdge

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

private theorem even_iff_mod_two_count (m : ℕ) : Even m ↔ m % 2 = 0 := by
  constructor
  · rintro ⟨k, hk⟩
    omega
  · intro hm
    refine ⟨m / 2, ?_⟩
    omega

/-- An edge-disjoint S-to-R path between the endpoints of the two arcs of an even cycle
produces an even cycle sharing an S-to-R arc with it, which `hSR.2` forbids. -/
theorem no_edge_disjoint_sToR_chord_of_trueSRCriterion
    (hSR : N.TrueSRStrongCriterion) {i j k : ℕ}
    (P : N.TrueSRPath (2 * j + 1))
    (Q₁ : N.TrueSRPath (2 * i + 1))
    (Q₂ : N.TrueSRPath (2 * k + 1))
    (hPQ₁ : Gluable P Q₁) (hPQ₂ : Gluable P Q₂) (hQ₁Q₂ : Gluable Q₁ Q₂)
    (hn₁ : 2 ≤ i + j + 1) (hn₂ : 2 ≤ k + j + 1) (hn₀ : 2 ≤ k + i + 1)
    (hC : (glueCycle Q₁ Q₂ hQ₁Q₂ hn₀).Even) : False := by
  classical
  let C := glueCycle Q₁ Q₂ hQ₁Q₂ hn₀
  let D₁ := glueCycle P Q₁ hPQ₁ hn₁
  let D₂ := glueCycle P Q₂ hPQ₂ hn₂
  let x := (univ.filter D₁.isCPair).card
  let y := (univ.filter D₂.isCPair).card
  let z := (univ.filter C.isCPair).card
  have hpar : (x + y + z) % 2 = 1 := by
    simpa [x, y, z, C, D₁, D₂] using
      TrueSRPath.three_glued_parity P Q₁ Q₂ hPQ₁ hPQ₂ hQ₁Q₂ hn₁ hn₂ hn₀
  have hCEven : Even z := by
    simpa [z, C, TrueSRCycle.Even, TrueSRCycle.numCPairs] using hC
  have hz0 : z % 2 = 0 := even_iff_mod_two_count z |>.mp hCEven
  have hOneChordEven : Even x ∨ Even y := by
    by_cases hx0 : x % 2 = 0
    · exact Or.inl (even_iff_mod_two_count x |>.mpr hx0)
    · have hx1 : x % 2 = 1 := by omega
      have hy0 : y % 2 = 0 := by omega
      exact Or.inr (even_iff_mod_two_count y |>.mpr hy0)
  have hD₁Even_iff : D₁.Even ↔ Even x := by
    change Even x ↔ Even x
    rfl
  have hD₂Even_iff : D₂.Even ↔ Even y := by
    change Even y ↔ Even y
    rfl
  have hC1D₁ : D₁.Even → False := by
    intro hD₁Even
    apply no_single_shared_path_of_trueSRCriterion N hSR D₁ C hD₁Even hC
      (2 * i + 1) (by omega) Q₁.edge Q₁.vertex
    · intro a
      exact (glueCycle_containsEdge_iff P Q₁ hPQ₁ hn₁ (Q₁.edge a)).mpr
        (Or.inr ⟨a, SameIncidence.refl _⟩)
    · intro a
      exact (glueCycle_containsEdge_iff Q₁ Q₂ hQ₁Q₂ hn₀ (Q₁.edge a)).mpr
        (Or.inl ⟨a, SameIncidence.refl _⟩)
    · exact Q₁.connects
    · exact Q₁.edge_simple
    · exact Q₁.vertex_simple
    · exact Q₁.starts_at_species
    · exact Q₁.ends_at_reaction
    · intro e heD₁ heC
      rcases (glueCycle_containsEdge_iff P Q₁ hPQ₁ hn₁ e).mp heD₁ with ⟨p, hp⟩ | ⟨q, hq⟩
      · rcases (glueCycle_containsEdge_iff Q₁ Q₂ hQ₁Q₂ hn₀ e).mp heC with ⟨q, hqC⟩ | ⟨r, hr⟩
        · exact False.elim (hPQ₁.edge_disjoint p q
            (SameIncidence.trans (SameIncidence.symm hp) hqC))
        · exact False.elim (hPQ₂.edge_disjoint p r
            (SameIncidence.trans (SameIncidence.symm hp) hr))
      · rcases (glueCycle_containsEdge_iff Q₁ Q₂ hQ₁Q₂ hn₀ e).mp heC with ⟨q', hqC⟩ | ⟨r, hr⟩
        · exact ⟨q, hq⟩
        · exact False.elim (hQ₁Q₂.edge_disjoint q r
            (SameIncidence.trans (SameIncidence.symm hq) hr))
  have hC1D₂ : D₂.Even → False := by
    intro hD₂Even
    apply no_single_shared_path_of_trueSRCriterion N hSR D₂ C hD₂Even hC
      (2 * k + 1) (by omega) Q₂.edge Q₂.vertex
    · intro a
      exact (glueCycle_containsEdge_iff P Q₂ hPQ₂ hn₂ (Q₂.edge a)).mpr
        (Or.inr ⟨a, SameIncidence.refl _⟩)
    · intro a
      exact (glueCycle_containsEdge_iff Q₁ Q₂ hQ₁Q₂ hn₀ (Q₂.edge a)).mpr
        (Or.inr ⟨a, SameIncidence.refl _⟩)
    · exact Q₂.connects
    · exact Q₂.edge_simple
    · exact Q₂.vertex_simple
    · exact Q₂.starts_at_species
    · exact Q₂.ends_at_reaction
    · intro e heD₂ heC
      rcases (glueCycle_containsEdge_iff P Q₂ hPQ₂ hn₂ e).mp heD₂ with ⟨p, hp⟩ | ⟨q, hq⟩
      · rcases (glueCycle_containsEdge_iff Q₁ Q₂ hQ₁Q₂ hn₀ e).mp heC with ⟨r, hr⟩ | ⟨q', hqC⟩
        · exact False.elim (hPQ₁.edge_disjoint p r
            (SameIncidence.trans (SameIncidence.symm hp) hr))
        · exact False.elim (hPQ₂.edge_disjoint p q'
            (SameIncidence.trans (SameIncidence.symm hp) hqC))
      · rcases (glueCycle_containsEdge_iff Q₁ Q₂ hQ₁Q₂ hn₀ e).mp heC with ⟨r, hr⟩ | ⟨q', hqC⟩
        · exact False.elim (hQ₁Q₂.edge_disjoint r q
            (SameIncidence.trans (SameIncidence.symm hr) hq))
        · exact ⟨q, hq⟩
  rcases hOneChordEven with hx | hy
  · exact hC1D₁ (hD₁Even_iff.mpr hx)
  · exact hC1D₂ (hD₂Even_iff.mpr hy)

end CRNT.Network
