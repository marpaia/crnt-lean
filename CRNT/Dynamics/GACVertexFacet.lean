import CRNT.Dynamics.GACLowRank
import CRNT.Dynamics.BoundaryOmegaSiphon
import CRNT.Geometry.CompatibilityFaces

/-!
# The global attractor theorem when critical siphons are vertices or facets

**Theorem (Anderson–Shiu 2010; Craciun–Dickenstein–Shiu–Sturmfels 2009).**  If every critical
siphon whose face has codimension at least two is a *vertex* zero set (no nonzero stoichiometric
vector vanishes on it), then every complex-balanced mass-action system on the network has the
global attractor property.  Critical siphons of codimension one (facets) are handled by the
Anderson–Shiu facet estimate already in the reduction chain; vertices by the entropy argument of
`false_of_vertex_omegaPoint`.

This module repeats the reduction chain of `complexBalanced_genuinePermanent` under the
network-level hypothesis `CodimTwoCriticalSiphonsAreVertices`.  In the residual, `Pmax` is the
zero set of an ω-point (a siphon, `isSiphon_zeroSet_of_mem_omegaLimit`) with a nonempty face in
the class of `x₀`, hence a critical siphon (`criticalSiphon_of_compatibilityFace_nonempty`), so
the hypothesis makes its face a vertex and the open non-vertex branch never arises.  All
theorems here are axiom-clean.

`codimTwoCriticalSiphonsAreVertices_of_stoichRank_le_two` shows the hypothesis holds in
stoichiometric rank at most two, so this generalizes `CRNT.Dynamics.GACLowRank`; it also holds
vacuously for networks without critical siphons.

Nothing here is an axiom or a `sorry`.
-/

open scoped NNReal ENNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every critical siphon whose face has codimension at least two is a vertex zero set. -/
def CodimTwoCriticalSiphonsAreVertices (N : Network S) : Prop :=
  ∀ P : Finset S, N.IsCriticalSiphon P →
    2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn P)) → N.IsVertexZeroSet P

/-- In stoichiometric rank at most two the hypothesis always holds. -/
theorem codimTwoCriticalSiphonsAreVertices_of_stoichRank_le_two (N : Network S)
    (hr2 : N.stoichRank ≤ 2) : N.CodimTwoCriticalSiphonsAreVertices := by
  intro P _ hcodim
  by_contra hnv
  have := N.three_le_stoichRank_of_nonVertex hcodim hnv
  omega

/-- Networks without critical siphons satisfy the hypothesis vacuously. -/
theorem codimTwoCriticalSiphonsAreVertices_of_hasNoCriticalSiphon (N : Network S)
    (h : N.HasNoCriticalSiphon) : N.CodimTwoCriticalSiphonsAreVertices :=
  fun P hP _ => (h P hP).elim

/-- The residual of the Global Attractor Theorem when codimension-two critical siphons are vertices. -/
theorem exists_positive_omegaPoint_of_highCodimension_siphonFace_of_codimTwoCriticalSiphonsAreVertices
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    {K : Set (Concentration S)} (hK : IsCompact K) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ K)
    (hωnn : ∀ y ∈ omegaLimit atTop ϕ {x₀}, Concentration.Nonnegative y)
    (hgenω : ∀ y ∈ omegaLimit atTop ϕ {x₀}, ∀ t : ℝ, 0 ≤ t →
      HasDerivAt (γ y) (N.massActionVectorField κ (γ y t)) t)
    (hωaff : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (z - x₀ : Concentration S) ∈ N.stoichSubspace)
    (hx₀ : x₀.Positive)
    {Pmax : Finset S} (hPmaxne : Pmax.Nonempty)
    {wmax : Concentration S} (hwmax : wmax ∈ omegaLimit atTop ϕ {x₀})
    (hzeroMax : ∀ s, s ∈ Pmax ↔ wmax s = 0)
    (hmaxExact : ∀ z ∈ omegaLimit atTop ϕ {x₀}, (∀ s ∈ Pmax, z s = 0) →
      ∀ s, z s = 0 ↔ s ∈ Pmax)
    (hzcard : ∀ z ∈ omegaLimit atTop ϕ {x₀},
      (Finset.univ.filter (fun s => z s = 0)).card ≤ Pmax.card)
    (hcodim : 2 ≤ Module.finrank ℝ (N.stoichSubspace.map (projOn Pmax)))
    (hcard : 2 ≤ Pmax.card)
    (hvx : N.CodimTwoCriticalSiphonsAreVertices) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  by_cases hvert : N.IsVertexZeroSet Pmax
  · exact (N.false_of_vertex_omegaPoint κ hxs hcb hϕγ hsol hx₀ hwmax (hωnn wmax hwmax)
      (hωaff wmax hwmax) hzeroMax hPmaxne hvert).elim
  · have hsiph := N.isSiphon_zeroSet_of_mem_omegaLimit κ hϕγ hK hmaps hωnn hgenω hwmax hzeroMax
    have hcrit := N.criticalSiphon_of_compatibilityFace_nonempty hx₀ hPmaxne hsiph
      ⟨wmax, hωaff wmax hwmax, hωnn wmax hwmax, fun s hs => (hzeroMax s).1 hs⟩
    exact absurd (hvx Pmax hcrit hcodim) hvert


/-- **Global Attractor Theorem when every critical siphon of codimension `≥ 2` is a vertex**
(permanence form, axiom-clean). -/
theorem complexBalanced_genuinePermanent_of_codimTwoCriticalSiphonsAreVertices
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hvx : N.CodimTwoCriticalSiphonsAreVertices) :
    N.GenuinePermanentForRates κ := by
  apply N.complexBalanced_genuinePermanent_of_positiveOmegaPointForRates κ hxs hcb
  by_cases hncs : N.HasNoCriticalSiphon
  · exact N.positiveOmegaPointForRates_of_boundaryOmegaExcluded κ
      (N.boundaryOmegaExcluded_of_hasNoCriticalSiphon κ hncs)
  · by_cases hzero : N.stoichSubspace = ⊥
    · exact N.positiveOmegaPointForRates_of_trivialStoichSubspace κ hzero
    · by_cases hrank : N.stoichRank = 1
      · exact N.positiveOmegaPointForRates_of_complexBalanced_of_stoichRank_one
          κ hxs hcb hrank
      · -- Remaining deep kernel, narrowed to its sharp form by
        -- `positiveOmega_or_criticalSiphonFaceEquilibrium`.  The dichotomy discharges every
        -- orbit that already has a positive omega-point, so what is left is exactly the
        -- critical-siphon boundary case.
        intro hϕγ hsol hbounded hωnn hgenω hωaff hx₀
        obtain ⟨K, hK, hmaps⟩ := hbounded
        rcases N.positiveOmega_or_nonstationary_criticalSiphonFaceEquilibrium κ hxs hcb
            hϕγ hsol hK hmaps hωnn hgenω hωaff hx₀ with hgood | ⟨_, hbad⟩
        · exact hgood
        · obtain ⟨w, hw, P, hPne, hzeroSet, -, -, -, -, -, -⟩ := hbad
          obtain ⟨wmax, hwmax, Pmax, hPmaxne, hzeroMax, hmaxExact, hzcard⟩ :=
            exists_maximal_zeroSet_omegaPoint hw hPne hzeroSet
          by_cases hfacet : Module.finrank ℝ
              (LinearMap.ker ((projOn Pmax).domRestrict N.stoichSubspace)) + 1 =
                Module.finrank ℝ N.stoichSubspace
          · have hwr : N.WeaklyReversible :=
              N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
            exact False.elim
              (N.no_omegaLimit_meets_locally_repelling_face κ hϕγ hK hmaps
                hPmaxne
                ⟨wmax, hwmax, fun s hs => (hzeroMax s).1 hs⟩
                (N.genuineOrbit_pos κ (by
                  have hγ0 := fun x => by simpa using (hϕγ x 0).symm
                  rw [hγ0]
                  exact hx₀) hsol)
                hsol
                (by
                  intro z hz hzP
                  have hpositiveOutside : ∀ s, s ∈ Pmaxᶜ → 0 < z s := by
                    intro s hs
                    have hsnot : s ∉ Pmax := by simpa using hs
                    have hnonzero : z s ≠ 0 := by
                      intro hzs
                      exact hsnot ((hmaxExact z hz hzP s).1 hzs)
                    rcases lt_or_eq_of_le (hωnn z hz s) with hpos | heq
                    · exact hpos
                    · exact (hnonzero heq.symm).elim
                  exact N.facet_repelling_near_facet_point_of_facet κ hwr hPmaxne hfacet hx₀
                    (hωaff z hz) (hωnn z hz) hzP hpositiveOutside))
          · -- Remaining case: the maximal boundary face is not a facet.  The degenerate failure
            -- (the `Pmax`-projection of the stoichiometric subspace being zero) is impossible,
            -- because every stoichiometric displacement would then vanish on `Pmax` and force
            -- `wmax s = x₀ s > 0` against `wmax s = 0`; `highCodimension_of_not_facet` also
            -- returns `2 ≤ Pmax.card`, since a one-species face always satisfies the facet
            -- count.  So this branch is exactly the codimension `≥ 2` case, and the whole
            -- residual content is isolated in
            -- `CRNT.Dynamics.HighCodimensionSiphonFace`.
            have hcompatMax := hωaff wmax hwmax
            have hzerosMax : ∀ s ∈ Pmax, wmax s = 0 := fun s hs => (hzeroMax s).1 hs
            obtain ⟨hcodim, hcard⟩ :=
              N.highCodimension_of_not_facet hx₀ hcompatMax hzerosMax hPmaxne hfacet
            exact N.exists_positive_omegaPoint_of_highCodimension_siphonFace_of_codimTwoCriticalSiphonsAreVertices
              κ hxs hcb hϕγ hsol hK hmaps hωnn hgenω hωaff hx₀ hPmaxne hwmax hzeroMax hmaxExact
              hzcard hcodim hcard hvx

/-- **Global Attractor Theorem when every critical siphon of codimension `≥ 2` is a vertex**
(convergence form, axiom-clean). -/
theorem complexBalanced_trajectory_converges_of_codimTwoCriticalSiphonsAreVertices
    (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) (hvx : N.CodimTwoCriticalSiphonsAreVertices) :
    N.PositiveClassTrajectoryConverges κ xstar := by
  intro Γ hΓ0pos hcompat hΓd
  have hxclass : Γ 0 ∈ N.positiveCompatibilityClass xstar :=
    ⟨hcompat.symm, hΓ0pos⟩
  have hpermClass : N.GenuinePermanentOnPositiveClass κ xstar :=
    N.complexBalanced_genuinePermanent_of_codimTwoCriticalSiphonsAreVertices κ hxs hcb hvx xstar hxs
  have hpers : N.PersistentFrom κ (Γ 0) :=
    GenuinePermanentOnPositiveClass.persistentFrom_of_trajectory
      (N := N) κ hxs hcb hpermClass hxclass rfl hΓd
  rcases hpers with ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have hwr : N.WeaklyReversible :=
    N.weaklyReversible_of_positive_complexBalanced κ hxs hcb
  obtain ⟨ϕ, γ, hγ0, hϕγ, hsol, hω⟩ :=
    N.gac_of_persistent hwr κ hxs hcb hΓ0pos hcompat
      ⟨K₀, hK₀cpt, hK₀pos, hgen⟩
  have horbitK : ∀ t : ℝ≥0, ϕ t (Γ 0) ∈ K₀ := by
    intro t
    rw [hϕγ]
    exact hgen (γ (Γ 0)) (hγ0 (Γ 0)) hsol (t : ℝ) t.coe_nonneg
  have htendNN : Tendsto (fun t : ℝ≥0 => ϕ t (Γ 0)) atTop (𝓝 xstar) := by
    apply hK₀cpt.tendsto_nhds_of_unique_mapClusterPt
    · exact Filter.Eventually.of_forall horbitK
    · intro y _hy hcluster
      have hyω : y ∈ omegaLimit atTop ϕ {Γ 0} :=
        (mem_omegaLimit_singleton_iff_mapClusterPt atTop ϕ (Γ 0) y).2 hcluster
      rw [hω, Set.mem_singleton_iff] at hyω
      exact hyω
  have htendReal : Tendsto (fun t : ℝ => ϕ (Real.toNNReal t) (Γ 0)) atTop (𝓝 xstar) :=
    htendNN.comp Real.tendsto_toNNReal_atTop
  have hevent : (fun t : ℝ => ϕ (Real.toNNReal t) (Γ 0)) =ᶠ[atTop] Γ := by
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [hϕγ, Real.coe_toNNReal t ht]
    exact (N.genuineOrbit_unique κ hxs hcb hΓ0pos rfl (hγ0 (Γ 0))
      hΓd hsol t ht).symm
  exact Filter.Tendsto.congr' hevent htendReal

end Network
end CRNT
