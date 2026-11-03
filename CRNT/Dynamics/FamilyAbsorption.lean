import Mathlib.Dynamics.OmegaLimit
import Mathlib.Dynamics.Flow
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Absorption through a monotone family of trapping regions

A family of regions `R l = {x | ∀ i, g i x ≤ c i l}` (`l ∈ [lo, hi]`, finitely many continuous
`g i`, offsets `c i` continuous and nondecreasing in `l`) such that

* a trajectory that is in `R l` at some time stays in `R l` afterwards, and
* at every point of a compact set `A` lying on a face `g i = c i l` of `R l`, the value of
  `g i` drops strictly below `c i l` right after time `0`,

absorbs every trajectory contained in `A` and starting in `R hi`: for every `l > lo` the
trajectory is eventually in `R l` (`eventually_mem_of_monotone_family`).

Proof: let `L` be the infimum of the levels that eventually contain the trajectory and suppose
`L > lo`.  The ω-limit set `Ω` is nonempty and compact, contained in `R L` (continuity of the
offsets from the right), and disjoint from the interior `{∀ i, g i < c i L}` (otherwise the
trajectory would enter a lower level, by continuity from the left and invariance).  A point of
`Ω` therefore lies on a face of `R L`; by strict descent and continuity, its forward orbit is in
the interior right after time `0`, and it stays in `Ω` (`Flow.isInvariant_omegaLimit`):
a contradiction.

Nothing here is an axiom or a `sorry`.
-/

open Set Filter Topology NNReal

namespace CRNT
namespace Dynamics

variable {X ι : Type*} [TopologicalSpace X] [T2Space X] [Fintype ι]

/-- **Absorption through a monotone family of regions with strict descent on the faces.** -/
theorem eventually_mem_of_monotone_family (ϕ : Flow ℝ≥0 X) (g : ι → X → ℝ)
    (hg : ∀ i, Continuous (g i)) (c : ι → ℝ → ℝ) {lo hi : ℝ} (hlo : lo < hi)
    (hcont : ∀ i, ContinuousOn (c i) (Icc lo hi)) (hmono : ∀ i, MonotoneOn (c i) (Icc lo hi))
    (x₀ : X) (A : Set X) (hA : IsCompact A) (htraj : ∀ t, ϕ t x₀ ∈ A)
    (hstart : ∀ i, g i x₀ ≤ c i hi)
    (hinv : ∀ l ∈ Ioc lo hi, ∀ t₁ : ℝ≥0, (∀ i, g i (ϕ t₁ x₀) ≤ c i l) →
      ∀ t, t₁ ≤ t → ∀ i, g i (ϕ t x₀) ≤ c i l)
    (hstrict : ∀ l ∈ Ioc lo hi, ∀ p ∈ A, (∀ i, g i p ≤ c i l) → ∀ i, g i p = c i l →
      ∀ᶠ t in 𝓝[>] (0 : ℝ≥0), g i (ϕ t p) < c i l) :
    ∀ l ∈ Ioc lo hi, ∃ T : ℝ≥0, ∀ t, T ≤ t → ∀ i, g i (ϕ t x₀) ≤ c i l := by
  classical
  -- the levels that eventually contain the trajectory
  set E : Set ℝ := {l | l ∈ Icc lo hi ∧ ∃ T : ℝ≥0, ∀ t, T ≤ t → ∀ i, g i (ϕ t x₀) ≤ c i l}
    with hE
  have hiE : hi ∈ E := ⟨⟨hlo.le, le_rfl⟩, 0, hinv hi ⟨hlo, le_rfl⟩ 0
    (by rw [ϕ.map_zero_apply]; exact hstart)⟩
  have hup : ∀ l ∈ E, ∀ l', l ≤ l' → l' ≤ hi → l' ∈ E := by
    rintro l ⟨hl, T, hT⟩ l' hll' hl'
    refine ⟨⟨le_trans hl.1 hll', hl'⟩, T, fun t ht i => ?_⟩
    exact le_trans (hT t ht i) (hmono i hl ⟨le_trans hl.1 hll', hl'⟩ hll')
  have hEne : E.Nonempty := ⟨hi, hiE⟩
  have hEbdd : BddBelow E := ⟨lo, fun l hl => hl.1.1⟩
  set L := sInf E with hL
  have hloL : lo ≤ L := le_csInf hEne fun l hl => hl.1.1
  have hLhi : L ≤ hi := csInf_le hEbdd hiE
  -- every level above the infimum is in `E`
  have habove : ∀ l, L < l → l ≤ hi → l ∈ E := by
    intro l hLl hl
    obtain ⟨l', hl'E, hl'⟩ := exists_lt_of_csInf_lt hEne hLl
    exact hup l' hl'E l hl'.le hl
  suffices hL' : L ≤ lo by
    intro l hl
    exact (habove l (lt_of_le_of_lt hL' hl.1) hl.2).2
  by_contra hcon
  push Not at hcon
  -- the ω-limit set
  set Ω := omegaLimit atTop (fun t x => ϕ t x) ({x₀} : Set X) with hΩ
  have hAcl : IsClosed A := hA.isClosed
  have himA : closure (image2 (fun t x => ϕ t x) (univ : Set ℝ≥0) {x₀}) ⊆ A := by
    refine closure_minimal ?_ hAcl
    rintro _ ⟨t, -, y, hy, rfl⟩
    rw [mem_singleton_iff] at hy
    subst hy
    exact htraj t
  have hΩne : Ω.Nonempty :=
    nonempty_omegaLimit_of_isCompact_absorbing _ _ _ hA ⟨univ, univ_mem, himA⟩
      (singleton_nonempty x₀)
  have hΩA : Ω ⊆ A := fun p hp =>
    himA (omegaLimit_subset_closure_image2 _ _ _ univ_mem hp)
  -- (c) the ω-limit set lies in `R L`
  have hΩR : ∀ p ∈ Ω, ∀ i, g i p ≤ c i L := by
    intro p hp i
    by_cases hLeq : L = hi
    · obtain ⟨-, T, hT⟩ := hiE
      have hcl := omegaLimit_subset_closure_image2 _ _ _ (Ici_mem_atTop T) hp
      have hsub : closure (image2 (fun t x => ϕ t x) (Ici T) ({x₀} : Set X)) ⊆
          {x | g i x ≤ c i hi} := by
        refine closure_minimal ?_ (isClosed_le (hg i) continuous_const)
        rintro _ ⟨t, ht, y, hy, rfl⟩
        rw [mem_singleton_iff] at hy
        subst hy
        exact hT t ht i
      rw [hLeq]
      exact hsub hcl
    · have hLlt : L < hi := lt_of_le_of_ne hLhi hLeq
      by_contra hgt
      push Not at hgt
      -- a level slightly above `L` with offset below `g i p`
      have hcw : ContinuousWithinAt (c i) (Icc lo hi) L := hcont i L ⟨hloL, hLhi⟩
      have hev : ∀ᶠ l in 𝓝[Icc lo hi] L, c i l < g i p :=
        hcw.eventually (gt_mem_nhds hgt)
      have hsub : 𝓝[Ioc L hi] L ≤ 𝓝[Icc lo hi] L :=
        nhdsWithin_mono _ fun l hl => ⟨le_trans hloL hl.1.le, hl.2⟩
      have hne : (𝓝[Ioc L hi] L).NeBot := by
        rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioc hLlt.ne]
        exact ⟨le_rfl, hLhi⟩
      have hev2 : ∀ᶠ l in 𝓝[Ioc L hi] L, c i l < g i p := hsub hev
      obtain ⟨l, hlc, hlm⟩ := (hev2.and self_mem_nhdsWithin).exists
      obtain ⟨-, T, hT⟩ := habove l hlm.1 hlm.2
      have hcl := omegaLimit_subset_closure_image2 _ _ _ (Ici_mem_atTop T) hp
      have hsub2 : closure (image2 (fun t x => ϕ t x) (Ici T) ({x₀} : Set X)) ⊆
          {x | g i x ≤ c i l} := by
        refine closure_minimal ?_ (isClosed_le (hg i) continuous_const)
        rintro _ ⟨t, ht, y, hy, rfl⟩
        rw [mem_singleton_iff] at hy
        subst hy
        exact hT t ht i
      have := hsub2 hcl
      simp only [mem_ofPred_eq] at this
      linarith
  -- (d) no point of the ω-limit set is strictly inside `R L`
  have hΩint : ∀ p ∈ Ω, ¬ ∀ i, g i p < c i L := by
    intro p hp hlt
    -- a level slightly below `L`
    have hev : ∀ i, ∀ᶠ l in 𝓝[Icc lo hi] L, g i p < c i l := fun i =>
      (hcont i L ⟨hloL, hLhi⟩).eventually (lt_mem_nhds (hlt i))
    have hsub : 𝓝[Ioo lo L] L ≤ 𝓝[Icc lo hi] L :=
      nhdsWithin_mono _ fun l hl => ⟨hl.1.le, le_trans hl.2.le hLhi⟩
    have hne : (𝓝[Ioo lo L] L).NeBot := by
      rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hcon.ne]
      exact ⟨hloL, le_rfl⟩
    have hall : ∀ᶠ l in 𝓝[Ioo lo L] L, ∀ i, g i p < c i l :=
      eventually_all.mpr fun i => hsub (hev i)
    obtain ⟨l, hlc, hlm⟩ := (hall.and self_mem_nhdsWithin).exists
    -- the trajectory enters the open set `{∀ i, g i < c i l}`
    have hU : {x | ∀ i, g i x < c i l} ∈ 𝓝 p := by
      have : {x | ∀ i, g i x < c i l} = ⋂ i, {x | g i x < c i l} := by ext; simp
      rw [this]
      exact (isOpen_iInter_of_finite fun i => isOpen_lt (hg i) continuous_const).mem_nhds
        (by simpa using hlc)
    have hcp := (mem_omegaLimit_singleton_iff_mapClusterPt _ _ _ _).mp hp
    obtain ⟨t₁, ht₁⟩ := ((mapClusterPt_iff_frequently.mp hcp) _ hU).exists
    have hinvl := hinv l ⟨hlm.1, le_trans hlm.2.le hLhi⟩ t₁ (fun i => (ht₁ i).le)
    have hlE : l ∈ E := ⟨⟨hlm.1.le, le_trans hlm.2.le hLhi⟩, t₁, hinvl⟩
    have := csInf_le hEbdd hlE
    linarith [hlm.2]
  -- (e) a point of the ω-limit set moves strictly inside
  obtain ⟨p, hp⟩ := hΩne
  have hpA := hΩA hp
  have hpR := hΩR p hp
  have hLmem : L ∈ Ioc lo hi := ⟨hcon, hLhi⟩
  have hevi : ∀ i, ∀ᶠ t in 𝓝[>] (0 : ℝ≥0), g i (ϕ t p) < c i L := by
    intro i
    rcases (hpR i).lt_or_eq with hlt | heq
    · have hc : Continuous fun t : ℝ≥0 => g i (ϕ t p) :=
        (hg i).comp (ϕ.continuous continuous_id continuous_const)
      have h0 : g i (ϕ 0 p) < c i L := by rw [ϕ.map_zero_apply]; exact hlt
      exact nhdsWithin_le_nhds ((hc.tendsto 0).eventually (gt_mem_nhds h0))
    · exact hstrict L hLmem p hpA hpR i heq
  have hall := eventually_all.mpr hevi
  have : (𝓝[>] (0 : ℝ≥0)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    have : closure (Ioi (0 : ℝ≥0)) = Ici 0 := closure_Ioi' ⟨1, mem_Ioi.mpr one_pos⟩
    rw [this]
    exact Set.self_mem_Ici
  obtain ⟨t, ht⟩ := hall.exists
  have hinvΩ := Flow.isInvariant_omegaLimit atTop ϕ ({x₀} : Set X)
    (fun t => tendsto_atTop_mono (fun x => le_add_self) tendsto_id) t hp
  exact hΩint _ hinvΩ ht

end Dynamics
end CRNT
