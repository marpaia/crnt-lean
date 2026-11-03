import CRNT.Persistence.TwoSpeciesEndotactic
import CRNT.Dynamics.FamilyAbsorption
import CRNT.Dynamics.GlobalPermanence
import CRNT.Dynamics.KnownGlobalPersistenceClasses
import CRNT.Dynamics.GlobalAttractorTheorem
import CRNT.Dynamics.DissipationBound
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Two-species endotactic networks are permanent

Craciun–Nazarov–Pantea 2013: for a two-species network that is endotactic in the standard sense
and any positive rate constants, every positive stoichiometric compatibility class contains one
compact set of positive states that eventually contains every forward solution starting in the
class, also for rate constants varying in time inside a band `[ρ, 1/ρ]`, with one absorbing set
for the whole band (`twoSpecies_endotacticStd_permanent_varK`).  Fixed rates, trajectory form:
`twoSpecies_endotacticStd_genuinePermanent` (the library's `GenuinePermanentForRates`, no global
flow and no uniqueness of solutions assumed); flow form:
`twoSpecies_endotacticStd_structurallyPermanent`; frontier claims:
`twoSpeciesEndotacticPermanenceClaim`, `twoSpeciesWRPermanenceClaim`.

Proof, for a class through `xref` and a solution `Γ` from a point of the class:
1. The infinity facets of the planar region (`exists_planar_infinity`) at every scale `λ ≥ C₀`
   form a nested family with nondecreasing continuous offsets (`exists_offs_monotone`).  With twice
   the slack the field strictly decreases every active functional whose normal is not orthogonal
   to the stoichiometric subspace (`dot_massActionField_pos_of_endotacticStd`); functionals
   orthogonal to it are constant on the class and inactive above a class-dependent level.  With
   time-dependent rates the velocity of each functional is bounded by its value for the extremal
   rate vector of the band (`1/ρ` on reactions increasing it, `ρ` on the others), which is a fixed
   continuous function of the state.
   `eventually_mem_of_monotone_family_traj` puts `Γ` eventually inside the infinity facets at a
   fixed scale `Λ` depending only on the class.
2. Inside the box `x ≤ 2Λ`, the facets near the axes (`exists_zsh_family`) at the scales
   `ε ∈ (0, ε₁)` form a second nested family; the same lemma puts `Γ` eventually in the region at
   a fixed scale `ε*/2` depending only on the class.

`eventually_mem_of_monotone_family_traj` (one solution in a compact set): if the infimum `L` of
the levels eventually containing `Γ` exceeds `lo`, compactness gives a neighbourhood of the
active part of each face of `R L` on which the functional decreases at a rate `≥ α > 0`
(`exists_subset_nhds_of_isCompact'`); by the mean value theorem each functional eventually drops
below `c_i(L) − η`, and by the band barrier lemma it stays there; continuity of the offsets from
the left then puts `Γ` eventually in a lower level, a contradiction.  (`FamilyAbsorption` has the
ω-limit version for flows.)

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT

open Finset Real Filter Topology NNReal

/-- A negative derivative at `0` makes the function drop below its value at `0` right after `0`
(on `ℝ≥0`). -/
theorem eventually_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {d : ℝ} (hf : HasDerivAt f d 0)
    (hd : d < 0) : ∀ᶠ t : ℝ≥0 in 𝓝[>] 0, f (t : ℝ) < f 0 := by
  have h1 := hf.tendsto_slope_zero_right
  have h2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t⁻¹ • (f (0 + t) - f 0) < 0 := h1.eventually (gt_mem_nhds hd)
  have h3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), f t < f 0 := by
    filter_upwards [h2, self_mem_nhdsWithin] with t ht htpos
    rw [zero_add, smul_eq_mul] at ht
    have htpos' : 0 < t := htpos
    have : f t - f 0 < 0 := by
      by_contra hc
      push Not at hc
      have := mul_nonneg (inv_nonneg.mpr htpos'.le) hc
      linarith
    linarith
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) (𝓝[>] 0) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · exact (NNReal.continuous_coe.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ht
  exact hcoe.eventually h3

namespace Network

open CRNT.Persistence CRNT.PolyhedralBarrier

variable {S : Type} [DecidableEq S] [Fintype S]

omit [DecidableEq S] in
/-- **Invariance from descent in a band.** A forward solution starting in the polyhedron
`{∀ i, ⟨nS i, x⟩ ≤ c i}` stays in it if the field does not increase any active functional at
points of the solution in the enlargements by `σ ∈ [0, R']`. -/
theorem stays_of_band {ι : Type} [Fintype ι] [Nonempty ι] (F : Concentration S → Concentration S)
    (nS : ι → S → ℝ) (c : ι → ℝ) {R' : ℝ} (hR' : 0 < R') (Γ : ℝ → Concentration S)
    (hΓ : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (F (Γ t)) t)
    (h0 : ∀ i, ∑ s, nS i s * Γ 0 s ≤ c i)
    (hdesc : ∀ t : ℝ, 0 ≤ t → ∀ σ, 0 ≤ σ → σ ≤ R' → (∀ i, ∑ s, nS i s * Γ t s ≤ c i + σ) →
      ∀ i, ∑ s, nS i s * Γ t s = c i + σ → ∑ s, nS i s * F (Γ t) s ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ i, ∑ s, nS i s * Γ t s ≤ c i := by
  set L : ι → ((S → ℝ) →L[ℝ] ℝ) := fun i =>
    ∑ s, nS i s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s with hL
  have hLapp : ∀ i (x : S → ℝ), L i x = ∑ s, nS i s * x s := by
    intro i x
    simp [hL, smul_eq_mul]
  have hγcont : ContinuousOn Γ (Set.Ici 0) := fun t ht =>
    (hΓ t ht).continuousAt.continuousWithinAt
  have hinv := barrier_le_of_local_descent_in_band (L := L) (b := c) (R := 0) (R' := R') hR'
    hγcont hΓ (by
      rw [barrier_le_iff]
      intro i
      rw [hLapp]
      linarith [h0 i]) (by
      intro t ht hlev hband i hact
      set σ := barrier L c (Γ t) with hσ
      have hall : ∀ i', ∑ s, nS i' s * Γ t s ≤ c i' + σ := by
        intro i'
        have := le_barrier L c (Γ t) i'
        rw [hLapp] at this
        linarith
      have hacteq : ∑ s, nS i s * Γ t s = c i + σ := by
        rw [hLapp] at hact
        linarith
      rw [hLapp]
      exact hdesc t ht σ hlev hband hall i hacteq)
  intro t ht i
  have hb := hinv t ht
  rw [barrier_le_iff] at hb
  have := hb i
  rw [hLapp] at this
  linarith

omit [DecidableEq S] in
/-- **Invariance from descent in a band**, for a time-dependent velocity. A forward solution starting in the polyhedron
`{∀ i, ⟨nS i, x⟩ ≤ c i}` stays in it if the field does not increase any active functional at
points of the solution in the enlargements by `σ ∈ [0, R']`. -/
theorem stays_of_band_vel {ι : Type} [Fintype ι] [Nonempty ι] (v : ℝ → Concentration S)
    (nS : ι → S → ℝ) (c : ι → ℝ) {R' : ℝ} (hR' : 0 < R') (Γ : ℝ → Concentration S)
    (hΓ : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (v t) t)
    (h0 : ∀ i, ∑ s, nS i s * Γ 0 s ≤ c i)
    (hdesc : ∀ t : ℝ, 0 ≤ t → ∀ σ, 0 ≤ σ → σ ≤ R' → (∀ i, ∑ s, nS i s * Γ t s ≤ c i + σ) →
      ∀ i, ∑ s, nS i s * Γ t s = c i + σ → ∑ s, nS i s * v t s ≤ 0) :
    ∀ t : ℝ, 0 ≤ t → ∀ i, ∑ s, nS i s * Γ t s ≤ c i := by
  set L : ι → ((S → ℝ) →L[ℝ] ℝ) := fun i =>
    ∑ s, nS i s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s with hL
  have hLapp : ∀ i (x : S → ℝ), L i x = ∑ s, nS i s * x s := by
    intro i x
    simp [hL, smul_eq_mul]
  have hγcont : ContinuousOn Γ (Set.Ici 0) := fun t ht =>
    (hΓ t ht).continuousAt.continuousWithinAt
  have hinv := barrier_le_of_local_descent_in_band (L := L) (b := c) (R := 0) (R' := R') hR'
    hγcont hΓ (by
      rw [barrier_le_iff]
      intro i
      rw [hLapp]
      linarith [h0 i]) (by
      intro t ht hlev hband i hact
      set σ := barrier L c (Γ t) with hσ
      have hall : ∀ i', ∑ s, nS i' s * Γ t s ≤ c i' + σ := by
        intro i'
        have := le_barrier L c (Γ t) i'
        rw [hLapp] at this
        linarith
      have hacteq : ∑ s, nS i s * Γ t s = c i + σ := by
        rw [hLapp] at hact
        linarith
      rw [hLapp]
      exact hdesc t ht σ hlev hband hall i hacteq)
  intro t ht i
  have hb := hinv t ht
  rw [barrier_le_iff] at hb
  have := hb i
  rw [hLapp] at this
  linarith

omit [DecidableEq S] in
/-- A linear functional along a solution has the expected derivative. -/
theorem hasDerivAt_sum_mul_of_hasDerivAt {F : Concentration S → Concentration S}
    {Γ : ℝ → Concentration S} {t : ℝ} (hΓ : HasDerivAt Γ (F (Γ t)) t) (w : S → ℝ) :
    HasDerivAt (fun τ => ∑ s, w s * Γ τ s) (∑ s, w s * F (Γ t) s) t := by
  have h1 := HasDerivAt.sum (u := Finset.univ) (A := fun s τ => w s * Γ τ s)
      (fun s _ => HasDerivAt.const_mul (w s) ((hasDerivAt_pi.mp hΓ) s))
  have h2 : (∑ s ∈ Finset.univ, fun τ => w s * Γ τ s) = fun τ => ∑ s, w s * Γ τ s := by
    funext τ; simp [Finset.sum_apply]
  rw [h2] at h1
  exact h1

omit [DecidableEq S] in
/-- **Absorption through a monotone family of regions, trajectory form.** For one solution `Γ`
contained in a compact set `A`, eventually inside `R hi`, where
`R l = {x | ∀ i, ⟨n i, x⟩ ≤ c i l}` with offsets continuous and nondecreasing in `l`, and with the
field strictly decreasing every active functional at the points of `A` on the boundary of every
`R l`, `l ∈ (lo, hi]`: the solution is eventually inside `R l` for every `l ∈ (lo, hi]`.  No flow
and no uniqueness of solutions are used. -/
theorem eventually_mem_of_monotone_family_traj {ι : Type} [Fintype ι]
    (F : Concentration S → Concentration S) (hF : Continuous F)
    (n : ι → S → ℝ) (c : ι → ℝ → ℝ) {lo hi : ℝ} (hlo : lo < hi)
    (hcont : ∀ i, ContinuousOn (c i) (Set.Icc lo hi))
    (hmono : ∀ i, MonotoneOn (c i) (Set.Icc lo hi))
    (Γ : ℝ → Concentration S) (hΓ : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (F (Γ t)) t)
    (A : Set (Concentration S)) (hA : IsCompact A) (htraj : ∀ t : ℝ, 0 ≤ t → Γ t ∈ A)
    (hhi : ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ i, ∑ s, n i s * Γ t s ≤ c i hi)
    (hstrict : ∀ l ∈ Set.Ioc lo hi, ∀ p ∈ A, (∀ i, ∑ s, n i s * p s ≤ c i l) → ∀ i,
      ∑ s, n i s * p s = c i l → ∑ s, n i s * F p s < 0) :
    ∀ l ∈ Set.Ioc lo hi, ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ i, ∑ s, n i s * Γ t s ≤ c i l := by
  classical
  set g : ι → Concentration S → ℝ := fun i x => ∑ s, n i s * x s with hgdef
  have hg : ∀ i, Continuous (g i) := fun i =>
    continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_apply s)
  have hD : ∀ i, Continuous fun x => g i (F x) := fun i => (hg i).comp hF
  set E : Set ℝ := {l | l ∈ Set.Icc lo hi ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ i, g i (Γ t) ≤ c i l}
    with hE
  have hiE : hi ∈ E := ⟨⟨hlo.le, le_rfl⟩, hhi⟩
  have hup : ∀ l ∈ E, ∀ l', l ≤ l' → l' ≤ hi → l' ∈ E := by
    rintro l ⟨hl, T, hT0, hT⟩ l' hll' hl'
    refine ⟨⟨le_trans hl.1 hll', hl'⟩, T, hT0, fun t ht i => ?_⟩
    exact le_trans (hT t ht i) (hmono i hl ⟨le_trans hl.1 hll', hl'⟩ hll')
  have hEne : E.Nonempty := ⟨hi, hiE⟩
  have hEbdd : BddBelow E := ⟨lo, fun l hl => hl.1.1⟩
  set L := sInf E with hL
  have hloL : lo ≤ L := le_csInf hEne fun l hl => hl.1.1
  have hLhi : L ≤ hi := csInf_le hEbdd hiE
  have habove : ∀ l, L < l → l ≤ hi → l ∈ E := by
    intro l hLl hl
    obtain ⟨l', hl'E, hl'⟩ := exists_lt_of_csInf_lt hEne hLl
    exact hup l' hl'E l hl'.le hl
  suffices hL' : L ≤ lo by
    intro l hl
    exact (habove l (lt_of_le_of_lt hL' hl.1) hl.2).2
  by_contra hcon
  push Not at hcon
  have hLmem : L ∈ Set.Ioc lo hi := ⟨hcon, hLhi⟩
  -- levels above `L`
  set lk : ℕ → ℝ := fun k => L + (hi - L) / ((k : ℝ) + 1) with hlk
  have hlk_ge : ∀ k, L ≤ lk k := fun k => by
    have : 0 ≤ (hi - L) / ((k : ℝ) + 1) := div_nonneg (by linarith) (by positivity)
    simp only [hlk]; linarith
  have hlk_le : ∀ k, lk k ≤ hi := fun k => by
    have h1 : (hi - L) / ((k : ℝ) + 1) ≤ hi - L :=
      div_le_self (by linarith) (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    simp only [hlk]; linarith
  have hlk_mem : ∀ k, lk k ∈ Set.Icc lo hi := fun k => ⟨le_trans hloL (hlk_ge k), hlk_le k⟩
  have hlkE : ∀ k, lk k ∈ E := by
    intro k
    rcases (hlk_ge k).lt_or_eq with h | h
    · exact habove _ h (hlk_le k)
    · have hL' : L = hi := by
        have : (hi - L) / ((k : ℝ) + 1) = 0 := by simp only [hlk] at h; linarith
        rcases div_eq_zero_iff.mp this with h' | h'
        · linarith
        · have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
      rw [← h, hL']; exact hiE
  have hlk_anti : ∀ k k', k ≤ k' → lk k' ≤ lk k := by
    intro k k' hkk'
    simp only [hlk]
    have hk : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkk' 1
    have : (hi - L) / ((k' : ℝ) + 1) ≤ (hi - L) / ((k : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hk
    linarith
  have hlk_tend : Tendsto lk atTop (𝓝 L) := by
    have h1 : Tendsto (fun k : ℕ => (hi - L) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (hi - L)
      rw [mul_zero] at this
      exact this.congr fun k => by rw [mul_one_div]
    have := h1.const_add L
    rw [add_zero] at this
    exact this
  have hck_tend : ∀ j, Tendsto (fun k => c j (lk k)) atTop (𝓝 (c j L)) := by
    intro j
    have hcw := hcont j L ⟨hloL, hLhi⟩
    exact hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlk_tend, Eventually.of_forall hlk_mem⟩)
  -- Step 1: uniform descent near the active part of each face
  have hstep1 : ∀ i, ∃ k : ℕ, ∃ α : ℝ, 0 < α ∧ ∀ q ∈ A, (∀ j, g j q ≤ c j (lk k)) →
      c i L - 1 / ((k : ℝ) + 1) ≤ g i q → g i (F q) < -α := by
    intro i
    have hclosed_all : ∀ l : ℝ, IsClosed {q : Concentration S | ∀ j, g j q ≤ c j l} := by
      intro l
      have : {q : Concentration S | ∀ j, g j q ≤ c j l} = ⋂ j, {q | g j q ≤ c j l} := by
        ext; simp
      rw [this]
      exact isClosed_iInter fun j => isClosed_le (hg j) continuous_const
    set Z : Set (Concentration S) :=
      A ∩ ({q | ∀ j, g j q ≤ c j L} ∩ {q | c i L ≤ g i q}) with hZ
    have hZc : IsCompact Z :=
      hA.inter_right ((hclosed_all L).inter (isClosed_le continuous_const (hg i)))
    obtain ⟨α, hα, hαZ⟩ : ∃ α : ℝ, 0 < α ∧ ∀ q ∈ Z, g i (F q) < -α := by
      rcases Z.eq_empty_or_nonempty with h | h
      · exact ⟨1, one_pos, fun q hq => by rw [h] at hq; exact absurd hq (Set.notMem_empty q)⟩
      · obtain ⟨q₀, hq₀, hmax⟩ := hZc.exists_isMaxOn h (hD i).continuousOn
        have hneg : g i (F q₀) < 0 := hstrict L hLmem q₀ hq₀.1 hq₀.2.1 i
          (le_antisymm (hq₀.2.1 i) hq₀.2.2)
        refine ⟨-(g i (F q₀)) / 2, by linarith, fun q hq => ?_⟩
        have := hmax hq
        simp only [Set.mem_setOf_eq] at this
        linarith
    set V : ℕ → Set (Concentration S) := fun k =>
      A ∩ ({q | ∀ j, g j q ≤ c j (lk k)} ∩ {q | c i L - 1 / ((k : ℝ) + 1) ≤ g i q}) with hV
    have hVcl : ∀ k, IsClosed (V k) := fun k =>
      hA.isClosed.inter ((hclosed_all _).inter (isClosed_le continuous_const (hg i)))
    have hVc : ∀ k, IsCompact (V k) := fun k =>
      hA.of_isClosed_subset (hVcl k) fun q hq => hq.1
    have hVdir : Directed (· ⊇ ·) V := by
      intro k k'
      have key : ∀ k₀, k₀ ≤ max k k' → V (max k k') ⊆ V k₀ := by
        intro k₀ hk₀ q hq
        obtain ⟨hqA, hq1, hq2⟩ := hq
        have hq1' : ∀ j, g j q ≤ c j (lk (max k k')) := hq1
        have hq2' : c i L - 1 / (((max k k' : ℕ) : ℝ) + 1) ≤ g i q := hq2
        refine ⟨hqA, ?_, ?_⟩
        · show ∀ j, g j q ≤ c j (lk k₀)
          intro j
          exact le_trans (hq1' j) (hmono j (hlk_mem _) (hlk_mem _) (hlk_anti _ _ hk₀))
        · show c i L - 1 / ((k₀ : ℝ) + 1) ≤ g i q
          have h1 : (0 : ℝ) < (k₀ : ℝ) + 1 := by positivity
          have hk : (k₀ : ℝ) ≤ ((max k k' : ℕ) : ℝ) := by exact_mod_cast hk₀
          have := one_div_le_one_div_of_le h1
            (by linarith : (k₀ : ℝ) + 1 ≤ ((max k k' : ℕ) : ℝ) + 1)
          linarith
      exact ⟨max k k', key k (le_max_left _ _), key k' (le_max_right _ _)⟩
    have hinter : (⋂ k, V k) ⊆ Z := by
      intro q hq
      simp only [Set.mem_iInter] at hq
      refine ⟨(hq 0).1, fun j => ?_, ?_⟩
      · exact ge_of_tendsto' (hck_tend j) fun k => (hq k).2.1 j
      · have ht : Tendsto (fun k : ℕ => c i L - 1 / ((k : ℝ) + 1)) atTop (𝓝 (c i L)) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (c i L)
          rw [sub_zero] at this
          exact this
        exact le_of_tendsto' ht fun k => (hq k).2.2
    have hU : {q : Concentration S | g i (F q) < -α} ∈ 𝓝ˢ (⋂ k, V k) := by
      refine (isOpen_lt (hD i) continuous_const).mem_nhdsSet.mpr ?_
      intro q hq
      exact hαZ q (hinter hq)
    obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact' hVdir hVc hVcl hU
    exact ⟨k, α, hα, fun q hqA hq1 hq2 => hk ⟨hqA, hq1, hq2⟩⟩
  choose kf αf hαf hkf using hstep1
  set k := Finset.univ.sup kf with hkdef
  set η : ℝ := 1 / ((k : ℝ) + 1) with hη
  have hη0 : 0 < η := by positivity
  have hprop : ∀ i, ∀ q ∈ A, (∀ j, g j q ≤ c j (lk k)) → c i L - η ≤ g i q →
      g i (F q) < -αf i := by
    intro i q hqA hq1 hq2
    have hki : kf i ≤ k := Finset.le_sup (f := kf) (Finset.mem_univ i)
    refine hkf i q hqA (fun j => le_trans (hq1 j) (hmono j (hlk_mem _) (hlk_mem _)
      (hlk_anti _ _ hki))) (le_trans ?_ hq2)
    have h1 : (0 : ℝ) < (kf i : ℝ) + 1 := by positivity
    have hki' : (kf i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hki
    have := one_div_le_one_div_of_le h1 (by linarith : (kf i : ℝ) + 1 ≤ (k : ℝ) + 1)
    simp only [hη]
    linarith
  obtain ⟨-, T₀, hT₀, hT₀P⟩ := hlkE k
  -- the functional along the solution
  have hφ : ∀ i t, 0 ≤ t → HasDerivAt (fun τ => g i (Γ τ)) (g i (F (Γ t))) t :=
    fun i t ht => hasDerivAt_sum_mul_of_hasDerivAt (hΓ t ht) (n i)
  -- Step 3: each functional eventually drops below `c i L - η`
  have hstep3 : ∀ i, ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → g i (Γ t) ≤ c i L - η := by
    intro i
    -- some time after `T₀` at which the functional is below `c i L - η`
    obtain ⟨t₁, ht₁, ht₁v⟩ : ∃ t₁, T₀ ≤ t₁ ∧ g i (Γ t₁) ≤ c i L - η := by
      by_contra hno
      push Not at hno
      have hderiv : ∀ t, T₀ ≤ t → g i (F (Γ t)) < -αf i := fun t ht =>
        hprop i (Γ t) (htraj t (le_trans hT₀ ht)) (hT₀P t ht) (hno t ht).le
      set t₂ := T₀ + (g i (Γ T₀) - (c i L - η)) / αf i + 1 with ht₂
      have hdiv : 0 ≤ (g i (Γ T₀) - (c i L - η)) / αf i :=
        div_nonneg (by linarith [hno T₀ le_rfl]) (hαf i).le
      have ht₂T₀ : T₀ ≤ t₂ := by linarith
      have hmvt := (convex_Icc T₀ t₂).image_sub_le_mul_sub_of_deriv_le
        (f := fun τ => g i (Γ τ)) (C := -αf i)
        (fun τ hτ => (hφ i τ (le_trans hT₀ hτ.1)).continuousAt.continuousWithinAt)
        (fun τ hτ => by
          rw [interior_Icc] at hτ
          exact (hφ i τ (by linarith [hτ.1])).differentiableAt.differentiableWithinAt)
        (fun τ hτ => by
          rw [interior_Icc] at hτ
          rw [(hφ i τ (by linarith [hτ.1])).deriv]
          exact (hderiv τ hτ.1.le).le)
        T₀ ⟨le_rfl, ht₂T₀⟩ t₂ ⟨ht₂T₀, le_rfl⟩ ht₂T₀
      have hmul : -αf i * (t₂ - T₀) = -(g i (Γ T₀) - (c i L - η)) - αf i := by
        have hα0 : αf i ≠ 0 := (hαf i).ne'
        have e1 : t₂ - T₀ = (g i (Γ T₀) - (c i L - η)) / αf i + 1 := by simp only [ht₂]; ring
        rw [e1, mul_add, mul_one]
        have : -αf i * ((g i (Γ T₀) - (c i L - η)) / αf i) = -(g i (Γ T₀) - (c i L - η)) := by
          field_simp
        linarith
      have := hno t₂ ht₂T₀
      linarith [hαf i]
    -- after that time the functional stays below `c i L - η`
    have hcap : c i L ≤ c i (lk k) := hmono i ⟨hloL, hLhi⟩ (hlk_mem k) (hlk_ge k)
    have hst := stays_of_band (ι := Unit) F (fun _ => n i) (fun _ => c i L - η)
      (R' := c i (lk k) - (c i L - η)) (by linarith) (fun τ => Γ (t₁ + τ))
      (fun τ hτ => (hΓ (t₁ + τ) (by linarith)).comp_const_add t₁ τ)
      (fun _ => by simpa using ht₁v)
      (by
        intro τ hτ σ hσ0 hσ1 _ _ hact
        have hτ' : T₀ ≤ t₁ + τ := by linarith
        have := hprop i (Γ (t₁ + τ)) (htraj _ (le_trans hT₀ hτ')) (hT₀P _ hτ')
          (by simp only [hgdef]; linarith)
        simp only [hgdef] at this
        linarith [hαf i])
    refine ⟨t₁, le_trans hT₀ ht₁, fun t ht => ?_⟩
    have := hst (t - t₁) (by linarith) ()
    have e : t₁ + (t - t₁) = t := by ring
    simpa [e, hgdef] using this
  choose Tf hTf0 hTf using hstep3
  set T := ∑ i, Tf i with hT
  have hTi : ∀ i, Tf i ≤ T := fun i =>
    single_le_sum (f := Tf) (fun i _ => hTf0 i) (Finset.mem_univ i)
  -- Step 4: a level below `L` contains the solution eventually
  have hev : ∀ i, ∀ᶠ l in 𝓝[Set.Ioo lo L] L, c i L - η ≤ c i l := by
    intro i
    have hcw : ContinuousWithinAt (c i) (Set.Icc lo hi) L := hcont i L ⟨hloL, hLhi⟩
    have hsub : 𝓝[Set.Ioo lo L] L ≤ 𝓝[Set.Icc lo hi] L :=
      nhdsWithin_mono _ fun l hl => ⟨hl.1.le, le_trans hl.2.le hLhi⟩
    have h1 : ∀ᶠ l in 𝓝[Set.Ioo lo L] L, c i L - η < c i l :=
      hsub (hcw.eventually (lt_mem_nhds (by linarith : c i L - η < c i L)))
    exact h1.mono fun l hl => hl.le
  have hne : (𝓝[Set.Ioo lo L] L).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hcon.ne]
    exact ⟨hloL, le_rfl⟩
  obtain ⟨l, hlc, hlm⟩ := ((eventually_all.mpr hev).and self_mem_nhdsWithin).exists
  have hlE : l ∈ E := by
    refine ⟨⟨hlm.1.le, le_trans hlm.2.le hLhi⟩, T, ?_, fun t ht i => ?_⟩
    · exact sum_nonneg fun i _ => hTf0 i
    · exact le_trans (hTf i t (le_trans (hTi i) ht)) (hlc i)
  have := csInf_le hEbdd hlE
  linarith [hlm.2]

omit [DecidableEq S] in
/-- **Absorption through a monotone family of regions, trajectory form**, with a velocity bounded
by continuous functions `D i` on each functional. For one solution `Γ`
contained in a compact set `A`, eventually inside `R hi`, where
`R l = {x | ∀ i, ⟨n i, x⟩ ≤ c i l}` with offsets continuous and nondecreasing in `l`, and with the
field strictly decreasing every active functional at the points of `A` on the boundary of every
`R l`, `l ∈ (lo, hi]`: the solution is eventually inside `R l` for every `l ∈ (lo, hi]`.  No flow
and no uniqueness of solutions are used. -/
theorem eventually_mem_of_monotone_family_vel {ι : Type} [Fintype ι]
    (v : ℝ → Concentration S) (D : ι → Concentration S → ℝ) (hDc : ∀ i, Continuous (D i))
    (n : ι → S → ℝ) (c : ι → ℝ → ℝ) {lo hi : ℝ} (hlo : lo < hi)
    (hcont : ∀ i, ContinuousOn (c i) (Set.Icc lo hi))
    (hmono : ∀ i, MonotoneOn (c i) (Set.Icc lo hi))
    (Γ : ℝ → Concentration S) (hΓ : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (v t) t)
    (hvD : ∀ t : ℝ, 0 ≤ t → ∀ i, ∑ s, n i s * v t s ≤ D i (Γ t))
    (A : Set (Concentration S)) (hA : IsCompact A) (htraj : ∀ t : ℝ, 0 ≤ t → Γ t ∈ A)
    (hhi : ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ i, ∑ s, n i s * Γ t s ≤ c i hi)
    (hstrict : ∀ l ∈ Set.Ioc lo hi, ∀ p ∈ A, (∀ i, ∑ s, n i s * p s ≤ c i l) → ∀ i,
      ∑ s, n i s * p s = c i l → D i p < 0) :
    ∀ l ∈ Set.Ioc lo hi, ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ i, ∑ s, n i s * Γ t s ≤ c i l := by
  classical
  set g : ι → Concentration S → ℝ := fun i x => ∑ s, n i s * x s with hgdef
  have hg : ∀ i, Continuous (g i) := fun i =>
    continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_apply s)
  have hD : ∀ i, Continuous fun x => D i x := hDc
  set E : Set ℝ := {l | l ∈ Set.Icc lo hi ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → ∀ i, g i (Γ t) ≤ c i l}
    with hE
  have hiE : hi ∈ E := ⟨⟨hlo.le, le_rfl⟩, hhi⟩
  have hup : ∀ l ∈ E, ∀ l', l ≤ l' → l' ≤ hi → l' ∈ E := by
    rintro l ⟨hl, T, hT0, hT⟩ l' hll' hl'
    refine ⟨⟨le_trans hl.1 hll', hl'⟩, T, hT0, fun t ht i => ?_⟩
    exact le_trans (hT t ht i) (hmono i hl ⟨le_trans hl.1 hll', hl'⟩ hll')
  have hEne : E.Nonempty := ⟨hi, hiE⟩
  have hEbdd : BddBelow E := ⟨lo, fun l hl => hl.1.1⟩
  set L := sInf E with hL
  have hloL : lo ≤ L := le_csInf hEne fun l hl => hl.1.1
  have hLhi : L ≤ hi := csInf_le hEbdd hiE
  have habove : ∀ l, L < l → l ≤ hi → l ∈ E := by
    intro l hLl hl
    obtain ⟨l', hl'E, hl'⟩ := exists_lt_of_csInf_lt hEne hLl
    exact hup l' hl'E l hl'.le hl
  suffices hL' : L ≤ lo by
    intro l hl
    exact (habove l (lt_of_le_of_lt hL' hl.1) hl.2).2
  by_contra hcon
  push Not at hcon
  have hLmem : L ∈ Set.Ioc lo hi := ⟨hcon, hLhi⟩
  -- levels above `L`
  set lk : ℕ → ℝ := fun k => L + (hi - L) / ((k : ℝ) + 1) with hlk
  have hlk_ge : ∀ k, L ≤ lk k := fun k => by
    have : 0 ≤ (hi - L) / ((k : ℝ) + 1) := div_nonneg (by linarith) (by positivity)
    simp only [hlk]; linarith
  have hlk_le : ∀ k, lk k ≤ hi := fun k => by
    have h1 : (hi - L) / ((k : ℝ) + 1) ≤ hi - L :=
      div_le_self (by linarith) (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    simp only [hlk]; linarith
  have hlk_mem : ∀ k, lk k ∈ Set.Icc lo hi := fun k => ⟨le_trans hloL (hlk_ge k), hlk_le k⟩
  have hlkE : ∀ k, lk k ∈ E := by
    intro k
    rcases (hlk_ge k).lt_or_eq with h | h
    · exact habove _ h (hlk_le k)
    · have hL' : L = hi := by
        have : (hi - L) / ((k : ℝ) + 1) = 0 := by simp only [hlk] at h; linarith
        rcases div_eq_zero_iff.mp this with h' | h'
        · linarith
        · have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
      rw [← h, hL']; exact hiE
  have hlk_anti : ∀ k k', k ≤ k' → lk k' ≤ lk k := by
    intro k k' hkk'
    simp only [hlk]
    have hk : (k : ℝ) + 1 ≤ (k' : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hkk' 1
    have : (hi - L) / ((k' : ℝ) + 1) ≤ (hi - L) / ((k : ℝ) + 1) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hk
    linarith
  have hlk_tend : Tendsto lk atTop (𝓝 L) := by
    have h1 : Tendsto (fun k : ℕ => (hi - L) / ((k : ℝ) + 1)) atTop (𝓝 0) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (hi - L)
      rw [mul_zero] at this
      exact this.congr fun k => by rw [mul_one_div]
    have := h1.const_add L
    rw [add_zero] at this
    exact this
  have hck_tend : ∀ j, Tendsto (fun k => c j (lk k)) atTop (𝓝 (c j L)) := by
    intro j
    have hcw := hcont j L ⟨hloL, hLhi⟩
    exact hcw.tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hlk_tend, Eventually.of_forall hlk_mem⟩)
  -- Step 1: uniform descent near the active part of each face
  have hstep1 : ∀ i, ∃ k : ℕ, ∃ α : ℝ, 0 < α ∧ ∀ q ∈ A, (∀ j, g j q ≤ c j (lk k)) →
      c i L - 1 / ((k : ℝ) + 1) ≤ g i q → D i q < -α := by
    intro i
    have hclosed_all : ∀ l : ℝ, IsClosed {q : Concentration S | ∀ j, g j q ≤ c j l} := by
      intro l
      have : {q : Concentration S | ∀ j, g j q ≤ c j l} = ⋂ j, {q | g j q ≤ c j l} := by
        ext; simp
      rw [this]
      exact isClosed_iInter fun j => isClosed_le (hg j) continuous_const
    set Z : Set (Concentration S) :=
      A ∩ ({q | ∀ j, g j q ≤ c j L} ∩ {q | c i L ≤ g i q}) with hZ
    have hZc : IsCompact Z :=
      hA.inter_right ((hclosed_all L).inter (isClosed_le continuous_const (hg i)))
    obtain ⟨α, hα, hαZ⟩ : ∃ α : ℝ, 0 < α ∧ ∀ q ∈ Z, D i q < -α := by
      rcases Z.eq_empty_or_nonempty with h | h
      · exact ⟨1, one_pos, fun q hq => by rw [h] at hq; exact absurd hq (Set.notMem_empty q)⟩
      · obtain ⟨q₀, hq₀, hmax⟩ := hZc.exists_isMaxOn h (hD i).continuousOn
        have hneg : D i q₀ < 0 := hstrict L hLmem q₀ hq₀.1 hq₀.2.1 i
          (le_antisymm (hq₀.2.1 i) hq₀.2.2)
        refine ⟨-(D i q₀) / 2, by linarith, fun q hq => ?_⟩
        have := hmax hq
        simp only [Set.mem_setOf_eq] at this
        linarith
    set V : ℕ → Set (Concentration S) := fun k =>
      A ∩ ({q | ∀ j, g j q ≤ c j (lk k)} ∩ {q | c i L - 1 / ((k : ℝ) + 1) ≤ g i q}) with hV
    have hVcl : ∀ k, IsClosed (V k) := fun k =>
      hA.isClosed.inter ((hclosed_all _).inter (isClosed_le continuous_const (hg i)))
    have hVc : ∀ k, IsCompact (V k) := fun k =>
      hA.of_isClosed_subset (hVcl k) fun q hq => hq.1
    have hVdir : Directed (· ⊇ ·) V := by
      intro k k'
      have key : ∀ k₀, k₀ ≤ max k k' → V (max k k') ⊆ V k₀ := by
        intro k₀ hk₀ q hq
        obtain ⟨hqA, hq1, hq2⟩ := hq
        have hq1' : ∀ j, g j q ≤ c j (lk (max k k')) := hq1
        have hq2' : c i L - 1 / (((max k k' : ℕ) : ℝ) + 1) ≤ g i q := hq2
        refine ⟨hqA, ?_, ?_⟩
        · show ∀ j, g j q ≤ c j (lk k₀)
          intro j
          exact le_trans (hq1' j) (hmono j (hlk_mem _) (hlk_mem _) (hlk_anti _ _ hk₀))
        · show c i L - 1 / ((k₀ : ℝ) + 1) ≤ g i q
          have h1 : (0 : ℝ) < (k₀ : ℝ) + 1 := by positivity
          have hk : (k₀ : ℝ) ≤ ((max k k' : ℕ) : ℝ) := by exact_mod_cast hk₀
          have := one_div_le_one_div_of_le h1
            (by linarith : (k₀ : ℝ) + 1 ≤ ((max k k' : ℕ) : ℝ) + 1)
          linarith
      exact ⟨max k k', key k (le_max_left _ _), key k' (le_max_right _ _)⟩
    have hinter : (⋂ k, V k) ⊆ Z := by
      intro q hq
      simp only [Set.mem_iInter] at hq
      refine ⟨(hq 0).1, fun j => ?_, ?_⟩
      · exact ge_of_tendsto' (hck_tend j) fun k => (hq k).2.1 j
      · have ht : Tendsto (fun k : ℕ => c i L - 1 / ((k : ℝ) + 1)) atTop (𝓝 (c i L)) := by
          have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_sub (c i L)
          rw [sub_zero] at this
          exact this
        exact le_of_tendsto' ht fun k => (hq k).2.2
    have hU : {q : Concentration S | D i q < -α} ∈ 𝓝ˢ (⋂ k, V k) := by
      refine (isOpen_lt (hD i) continuous_const).mem_nhdsSet.mpr ?_
      intro q hq
      exact hαZ q (hinter hq)
    obtain ⟨k, hk⟩ := exists_subset_nhds_of_isCompact' hVdir hVc hVcl hU
    exact ⟨k, α, hα, fun q hqA hq1 hq2 => hk ⟨hqA, hq1, hq2⟩⟩
  choose kf αf hαf hkf using hstep1
  set k := Finset.univ.sup kf with hkdef
  set η : ℝ := 1 / ((k : ℝ) + 1) with hη
  have hη0 : 0 < η := by positivity
  have hprop : ∀ i, ∀ q ∈ A, (∀ j, g j q ≤ c j (lk k)) → c i L - η ≤ g i q →
      D i q < -αf i := by
    intro i q hqA hq1 hq2
    have hki : kf i ≤ k := Finset.le_sup (f := kf) (Finset.mem_univ i)
    refine hkf i q hqA (fun j => le_trans (hq1 j) (hmono j (hlk_mem _) (hlk_mem _)
      (hlk_anti _ _ hki))) (le_trans ?_ hq2)
    have h1 : (0 : ℝ) < (kf i : ℝ) + 1 := by positivity
    have hki' : (kf i : ℝ) ≤ (k : ℝ) := by exact_mod_cast hki
    have := one_div_le_one_div_of_le h1 (by linarith : (kf i : ℝ) + 1 ≤ (k : ℝ) + 1)
    simp only [hη]
    linarith
  obtain ⟨-, T₀, hT₀, hT₀P⟩ := hlkE k
  -- the functional along the solution
  have hφ : ∀ i t, 0 ≤ t → HasDerivAt (fun τ => g i (Γ τ)) (g i (v t)) t := by
    intro i t ht
    have h1 := HasDerivAt.sum (u := Finset.univ) (A := fun s τ => n i s * Γ τ s)
        (fun s _ => HasDerivAt.const_mul (n i s) ((hasDerivAt_pi.mp (hΓ t ht)) s))
    have h2 : (∑ s ∈ Finset.univ, fun τ => n i s * Γ τ s) = fun τ => g i (Γ τ) := by
      funext τ; simp [hgdef, Finset.sum_apply]
    rw [h2] at h1
    exact h1
  -- Step 3: each functional eventually drops below `c i L - η`
  have hstep3 : ∀ i, ∃ T : ℝ, 0 ≤ T ∧ ∀ t, T ≤ t → g i (Γ t) ≤ c i L - η := by
    intro i
    -- some time after `T₀` at which the functional is below `c i L - η`
    obtain ⟨t₁, ht₁, ht₁v⟩ : ∃ t₁, T₀ ≤ t₁ ∧ g i (Γ t₁) ≤ c i L - η := by
      by_contra hno
      push Not at hno
      have hderiv : ∀ t, T₀ ≤ t → g i (v t) < -αf i := fun t ht =>
        lt_of_le_of_lt (hvD t (le_trans hT₀ ht) i)
          (hprop i (Γ t) (htraj t (le_trans hT₀ ht)) (hT₀P t ht) (hno t ht).le)
      set t₂ := T₀ + (g i (Γ T₀) - (c i L - η)) / αf i + 1 with ht₂
      have hdiv : 0 ≤ (g i (Γ T₀) - (c i L - η)) / αf i :=
        div_nonneg (by linarith [hno T₀ le_rfl]) (hαf i).le
      have ht₂T₀ : T₀ ≤ t₂ := by linarith
      have hmvt := (convex_Icc T₀ t₂).image_sub_le_mul_sub_of_deriv_le
        (f := fun τ => g i (Γ τ)) (C := -αf i)
        (fun τ hτ => (hφ i τ (le_trans hT₀ hτ.1)).continuousAt.continuousWithinAt)
        (fun τ hτ => by
          rw [interior_Icc] at hτ
          exact (hφ i τ (by linarith [hτ.1])).differentiableAt.differentiableWithinAt)
        (fun τ hτ => by
          rw [interior_Icc] at hτ
          rw [(hφ i τ (by linarith [hτ.1])).deriv]
          exact (hderiv τ hτ.1.le).le)
        T₀ ⟨le_rfl, ht₂T₀⟩ t₂ ⟨ht₂T₀, le_rfl⟩ ht₂T₀
      have hmul : -αf i * (t₂ - T₀) = -(g i (Γ T₀) - (c i L - η)) - αf i := by
        have hα0 : αf i ≠ 0 := (hαf i).ne'
        have e1 : t₂ - T₀ = (g i (Γ T₀) - (c i L - η)) / αf i + 1 := by simp only [ht₂]; ring
        rw [e1, mul_add, mul_one]
        have : -αf i * ((g i (Γ T₀) - (c i L - η)) / αf i) = -(g i (Γ T₀) - (c i L - η)) := by
          field_simp
        linarith
      have := hno t₂ ht₂T₀
      linarith [hαf i]
    -- after that time the functional stays below `c i L - η`
    have hcap : c i L ≤ c i (lk k) := hmono i ⟨hloL, hLhi⟩ (hlk_mem k) (hlk_ge k)
    have hst := stays_of_band_vel (ι := Unit) (fun τ => v (t₁ + τ)) (fun _ => n i)
      (fun _ => c i L - η)
      (R' := c i (lk k) - (c i L - η)) (by linarith) (fun τ => Γ (t₁ + τ))
      (fun τ hτ => (hΓ (t₁ + τ) (by linarith)).comp_const_add t₁ τ)
      (fun _ => by simpa using ht₁v)
      (by
        intro τ hτ σ hσ0 hσ1 _ _ hact
        have hτ' : T₀ ≤ t₁ + τ := by linarith
        have := hprop i (Γ (t₁ + τ)) (htraj _ (le_trans hT₀ hτ')) (hT₀P _ hτ')
          (by simp only [hgdef]; linarith)
        have hb := hvD (t₁ + τ) (le_trans hT₀ hτ') i
        linarith [hαf i])
    refine ⟨t₁, le_trans hT₀ ht₁, fun t ht => ?_⟩
    have := hst (t - t₁) (by linarith) ()
    have e : t₁ + (t - t₁) = t := by ring
    simpa [e, hgdef] using this
  choose Tf hTf0 hTf using hstep3
  set T := ∑ i, Tf i with hT
  have hTi : ∀ i, Tf i ≤ T := fun i =>
    single_le_sum (f := Tf) (fun i _ => hTf0 i) (Finset.mem_univ i)
  -- Step 4: a level below `L` contains the solution eventually
  have hev : ∀ i, ∀ᶠ l in 𝓝[Set.Ioo lo L] L, c i L - η ≤ c i l := by
    intro i
    have hcw : ContinuousWithinAt (c i) (Set.Icc lo hi) L := hcont i L ⟨hloL, hLhi⟩
    have hsub : 𝓝[Set.Ioo lo L] L ≤ 𝓝[Set.Icc lo hi] L :=
      nhdsWithin_mono _ fun l hl => ⟨hl.1.le, le_trans hl.2.le hLhi⟩
    have h1 : ∀ᶠ l in 𝓝[Set.Ioo lo L] L, c i L - η < c i l :=
      hsub (hcw.eventually (lt_mem_nhds (by linarith : c i L - η < c i L)))
    exact h1.mono fun l hl => hl.le
  have hne : (𝓝[Set.Ioo lo L] L).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo hcon.ne]
    exact ⟨hloL, le_rfl⟩
  obtain ⟨l, hlc, hlm⟩ := ((eventually_all.mpr hev).and self_mem_nhdsWithin).exists
  have hlE : l ∈ E := by
    refine ⟨⟨hlm.1.le, le_trans hlm.2.le hLhi⟩, T, ?_, fun t ht i => ?_⟩
    · exact sum_nonneg fun i _ => hTf0 i
    · exact le_trans (hTf i t (le_trans (hTi i) ht)) (hlc i)
  have := csInf_le hEbdd hlE
  linarith [hlm.2]

set_option maxHeartbeats 8000000 in
/-- **Two-species endotactic networks are permanent with tempered rates** (Craciun–Nazarov–Pantea
2013, `k`-variable systems). For every band `[ρ, 1/ρ]` and every positive stoichiometric
compatibility class there is one compact set of positive states in the class that eventually
contains every forward solution starting in the class, for every choice of time-dependent rate
constants in the band.  No global flow and no uniqueness of solutions are assumed. -/
theorem twoSpecies_endotacticStd_permanent_varK (N : Network S)
    (hS : Fintype.card S = 2) (hend : N.EndotacticStd) {ρ : ℝ} (hρ : 0 < ρ)
    (xref : Concentration S) (hxref : xref.Positive) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → N.RateConstants, (∀ t r, ρ ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ρ) →
      ∀ x₀ ∈ N.positiveCompatibilityClass xref, ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → Γ t ∈ K := by
  obtain e : S ≃ Fin 2 := Fintype.equivFinOfCardEq hS
  -- complex differences, closed under permutations
  obtain ⟨D, hD⟩ : ∃ D : Complex S × Complex S → Fin 2 → ℝ,
      D = fun p q => ((p.1 (e.symm q) : ℝ) - p.2 (e.symm q)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Finset (Fin 2 → ℝ), H =
      (Finset.univ : Finset (Equiv.Perm (Fin 2))).biUnion
        fun ρ => (N.complexes ×ˢ N.complexes).image fun p => D p ∘ ρ := ⟨_, rfl⟩
  have hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin 2), h ∘ ρ ∈ H := by
    intro h hh ρ'
    rw [hH] at hh ⊢
    simp only [mem_biUnion, mem_univ, true_and, mem_image] at hh ⊢
    obtain ⟨ρ, p, hp, rfl⟩ := hh
    exact ⟨ρ * ρ', p, hp, by funext q; simp⟩
  have hDmem : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes, D (c, c') ∈ H := by
    intro c hc c' hc'
    rw [hH]
    simp only [mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨1, (c, c'), mem_product.mpr ⟨hc, hc'⟩, by funext q; simp⟩
  have htr : ∀ (a x : S → ℝ), fdot (a ∘ e.symm) (x ∘ e.symm) = ∑ s, a s * x s := by
    intro a x
    unfold fdot
    exact Equiv.sum_comp e.symm (fun s => a s * x s)
  have htrlog : ∀ (h : Fin 2 → ℝ) (x : S → ℝ),
      ∑ q, h q * log (x (e.symm q)) = ∑ s, h (e s) * log (x s) := by
    intro h x
    rw [← Equiv.sum_comp e (fun q => h q * log (x (e.symm q)))]
    simp
  -- the facets
  obtain ⟨m, β, hm2, hβlast, hβinc, hβabs, hθ1, hinf⟩ := exists_planar_infinity H hsym
  obtain ⟨ιz, hFz, hNz, a, bf, hbmono, hbcont, hapos, hzf⟩ :=
    exists_zsh_family (n := 2) (by norm_num) H hsym
  have := hFz
  have := hNz
  set nrm : (Fin m × Bool) ⊕ ιz → Fin 2 → ℝ :=
    Sum.elim (fun p : Fin m × Bool => if p.2 then ![β p.1, 1] else ![1, β p.1])
      (fun j => -a j) with hnrm
  set nS : (Fin m × Bool) ⊕ ιz → S → ℝ := fun i s => nrm i (e s) with hnS
  have hdotS : ∀ i (x : S → ℝ), fdot (nrm i) (x ∘ e.symm) = ∑ s, nS i s * x s := by
    intro i x
    have : nrm i = nS i ∘ e.symm := by funext q; simp [hnS]
    rw [this, htr]
  have hfd : ∀ (u₀ u₁ : ℝ) (y : Fin 2 → ℝ), fdot ![u₀, u₁] y = u₀ * y 0 + u₁ * y 1 := by
    intro u₀ u₁ y; simp [fdot, Fin.sum_univ_two]
  have hfdneg : ∀ (j : ιz) (y : Fin 2 → ℝ), fdot (-a j) y = -fdot (a j) y := by
    intro j y; simp [fdot, sum_neg_distrib]
  -- the slack
  obtain ⟨C, hC0, hC⟩ := exists_ratio_bound
    (fun (i : (Fin m × Bool) ⊕ ιz) (r : N.R) => ∑ s, (-nS i s) * N.reactionVector r s)
  obtain ⟨δ, hδ⟩ := N.exists_slack_varK_ratio hρ (2 * C)
  have hδ2 : ∀ κ : N.RateConstants, (∀ r, ρ ≤ κ.k r ∧ κ.k r ≤ 1 / ρ) →
      ∀ i j : N.R, 2 * (Fintype.card N.R : ℝ) * C * κ.k i ≤ exp δ * κ.k j := by
    intro κ hκb i j
    have := hδ κ hκb i j
    linarith
  have hδ1 : ∀ κ : N.RateConstants, (∀ r, ρ ≤ κ.k r ∧ κ.k r ≤ 1 / ρ) →
      ∀ i j : N.R, (Fintype.card N.R : ℝ) * C * κ.k i ≤ exp δ * κ.k j := by
    intro κ hκb i j
    have h1 := hδ2 κ hκb i j
    have h2 : 0 ≤ (Fintype.card N.R : ℝ) * C * κ.k i :=
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hC0) (κ.positive i).le
    linarith
  -- the field on a facet, from the validity condition
  have hfield : ∀ κ : N.RateConstants, (∀ r, ρ ≤ κ.k r ∧ κ.k r ≤ 1 / ρ) →
      ∀ (i : (Fin m × Bool) ⊕ ιz) (x : Concentration S), x.Positive →
      (∀ h ∈ H, 0 < fdot (nrm i) h → δ ≤ ∑ q, h q * log (x (e.symm q))) →
      ∑ s, nS i s * N.massActionVectorField κ x s ≤ 0 ∧
      ((∃ r, ∑ s, nS i s * N.reactionVector r s ≠ 0) →
        ∑ s, nS i s * N.massActionVectorField κ x s < 0) := by
    intro κ hκb i x hx hv
    have hvalid : ∀ c₁ ∈ N.complexes, ∀ c₂ ∈ N.complexes,
        ∑ s, (-nS i s) * ((c₁ s : ℝ) - c₂ s) < 0 →
        δ ≤ ∑ s, ((c₁ s : ℝ) - c₂ s) * log (x s) := by
      intro c₁ hc₁ c₂ hc₂ hneg
      have hmem := hDmem c₁ hc₁ c₂ hc₂
      have hdot : fdot (nrm i) (D (c₁, c₂)) = ∑ s, nS i s * ((c₁ s : ℝ) - c₂ s) := by
        have : D (c₁, c₂) = (fun s => ((c₁ s : ℝ) - c₂ s)) ∘ e.symm := by
          rw [hD]; rfl
        rw [this, hdotS]
      have hpos' : 0 < fdot (nrm i) (D (c₁, c₂)) := by
        rw [hdot]
        have : ∑ s, (-nS i s) * ((c₁ s : ℝ) - c₂ s) = -∑ s, nS i s * ((c₁ s : ℝ) - c₂ s) := by
          rw [← sum_neg_distrib]; exact sum_congr rfl fun s _ => by ring
        linarith
      have := hv (D (c₁, c₂)) hmem hpos'
      rw [htrlog, hD] at this
      simpa using this
    have hneg : ∑ s, (-nS i s) * N.massActionVectorField κ x s =
        -∑ s, nS i s * N.massActionVectorField κ x s := by
      rw [← sum_neg_distrib]; exact sum_congr rfl fun s _ => by ring
    constructor
    · have := N.dot_massActionField_nonneg_of_endotacticStd κ hend hx (fun s => -nS i s) δ C
        (fun r r' h => hC i r r' h) (hδ1 κ hκb) hvalid
      linarith
    · rintro ⟨r, hr⟩
      have := N.dot_massActionField_pos_of_endotacticStd κ hend hx (fun s => -nS i s) δ C
        (fun r r' h => hC i r r' h) (hδ2 κ hκb) hvalid ⟨r, by
          have : ∑ s, (-nS i s) * N.reactionVector r s = -∑ s, nS i s * N.reactionVector r s := by
            rw [← sum_neg_distrib]; exact sum_congr rfl fun s _ => by ring
          rw [this]; exact neg_ne_zero.mpr hr⟩
      linarith
  -- the extremal rate vectors of the band, face by face
  set κs : (Fin m × Bool) ⊕ ιz → N.RateConstants := fun i =>
    ⟨fun r => if 0 ≤ ∑ s, nS i s * N.reactionVector r s then 1 / ρ else ρ,
     fun r => by split_ifs <;> positivity⟩ with hκs
  have hκsb : ρ ≤ 1 → ∀ i r, ρ ≤ (κs i).k r ∧ (κs i).k r ≤ 1 / ρ := by
    intro hρ1 i r
    have h1 : ρ ≤ 1 / ρ := by rw [le_div_iff₀ hρ]; nlinarith
    simp only [hκs]
    split_ifs
    · exact ⟨h1, le_rfl⟩
    · exact ⟨le_rfl, h1⟩
  have hdom : ∀ κ : N.RateConstants, (∀ r, ρ ≤ κ.k r ∧ κ.k r ≤ 1 / ρ) →
      ∀ i (x : Concentration S), (∀ s, 0 ≤ x s) →
      ∑ s, nS i s * N.massActionVectorField κ x s ≤
        ∑ s, nS i s * N.massActionVectorField (κs i) x s := by
    intro κ hκb i x hx
    have hexp : ∀ κ' : N.RateConstants, ∑ s, nS i s * N.massActionVectorField κ' x s =
        ∑ r, κ'.k r * ((N.reaction r).source.massActionMonomial x *
          ∑ s, nS i s * N.reactionVector r s) := by
      intro κ'
      simp only [massActionVectorField_apply, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun r _ => ?_
      simp only [massActionRate]
      refine sum_congr rfl fun s _ => ?_
      ring
    rw [hexp, hexp]
    refine sum_le_sum fun r _ => ?_
    have hmono : 0 ≤ (N.reaction r).source.massActionMonomial x :=
      Complex.massActionMonomial_nonneg hx _
    simp only [hκs]
    split_ifs with hd
    · exact mul_le_mul_of_nonneg_right (hκb r).2 (mul_nonneg hmono hd)
    · push Not at hd
      have : (N.reaction r).source.massActionMonomial x * ∑ s, nS i s * N.reactionVector r s ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hmono hd.le
      nlinarith [(hκb r).1]
  set Dm : (Fin m × Bool) ⊕ ιz → Concentration S → ℝ :=
    fun i x => ∑ s, nS i s * N.massActionVectorField (κs i) x s with hDm
  have hDmc : ∀ i, Continuous (Dm i) := fun i =>
    continuous_finsetSum _ fun s _ => continuous_const.mul
      ((continuous_apply s).comp (N.continuous_massActionVectorField (κs i)))
  -- validity of the infinity facets at every large scale
  obtain ⟨C₀, hC₀4, hinfC⟩ := hinf δ
  have hvinf : ∀ l, C₀ ≤ l → ∀ σ, 0 ≤ σ → σ ≤ 1 → ∀ y : Fin 2 → ℝ, (∀ q, 0 < y q) →
      (∀ p : Fin m × Bool, fdot (nrm (Sum.inl p)) y ≤ l + offs β l p.1 + σ) →
      ∀ p : Fin m × Bool, fdot (nrm (Sum.inl p)) y = l + offs β l p.1 + σ →
      ∀ h ∈ H, 0 < fdot (nrm (Sum.inl p)) h → δ ≤ ∑ q, h q * log (y q) := by
    intro l hl σ hσ0 hσ1 y hy hall p hact h hh hpos
    obtain ⟨-, hcore⟩ := hinfC l hl
    have hR : ∀ k, k < m → y 0 + β k * y 1 ≤ l + offs β l k + σ := fun k hk => by
      have := hall (⟨k, hk⟩, false)
      simpa [hnrm, hfd] using this
    have hTp : ∀ k, k < m → β k * y 0 + y 1 ≤ l + offs β l k + σ := fun k hk => by
      have := hall (⟨k, hk⟩, true)
      simpa [hnrm, hfd] using this
    have hlog : ∑ q, h q * log (y q) = h 0 * log (y 0) + h 1 * log (y 1) := Fin.sum_univ_two _
    obtain ⟨k, side⟩ := p
    cases side
    · simp only [hnrm, Sum.elim_inl, hfd, Bool.false_eq_true, ite_false] at hact hpos
      rw [hlog]
      exact hcore σ hσ0 hσ1 (y 0) (y 1) (hy 0) (hy 1) hR hTp k k.isLt (by linarith) h hh
        (by linarith)
    · simp only [hnrm, Sum.elim_inl, hfd, ite_true] at hact hpos
      set g : Fin 2 → ℝ := h ∘ Equiv.swap 0 1 with hg
      have hgH : g ∈ H := hsym h hh _
      have hg0 : g 0 = h 1 := by simp [hg]
      have hg1 : g 1 = h 0 := by simp [hg]
      have := hcore σ hσ0 hσ1 (y 1) (y 0) (hy 1) (hy 0)
        (fun k hk => by have := hTp k hk; linarith)
        (fun k hk => by have := hR k hk; linarith) k k.isLt (by linarith) g hgH
        (by rw [hg0, hg1]; linarith)
      rw [hg0, hg1] at this
      rw [hlog]
      linarith
  -- the region functionals
  set G : (Fin m × Bool) ⊕ ιz → Concentration S → ℝ := fun i x => ∑ s, nS i s * x s with hG
  have hGc : ∀ i, Continuous (G i) := fun i =>
    continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_apply s)
  have hGnrm : ∀ i (x : Concentration S), G i x = fdot (nrm i) (x ∘ e.symm) := fun i x =>
    (hdotS i x).symm
  -- functionals orthogonal to the stoichiometric subspace are constant on the class
  have hperp : ∀ i, (∀ r, ∑ s, nS i s * N.reactionVector r s = 0) →
      ∀ x, N.StoichCompatible xref x → G i x = G i xref := by
    intro i hi x hx
    have hw : nS i ∈ orthSum N.stoichSubspace := by
      unfold stoichSubspace
      refine mem_orthSum_span ?_
      rintro g ⟨r, rfl⟩
      exact hi r
    have h0 := (mem_orthSum.mp hw) _ hx
    have : ∑ s, nS i s * (x - xref) s = G i x - G i xref := by
      simp only [hG, Pi.sub_apply, mul_sub, sum_sub_distrib]
    linarith
  -- the class-dependent scale at infinity
  obtain ⟨C₁, hC₁1, hmon⟩ := exists_offs_monotone β m hθ1
  obtain ⟨lo₁, hlo₁⟩ : ∃ lo₁, lo₁ = max (max C₀ C₁) (1 + ∑ p : Fin m × Bool, |G (Sum.inl p) xref|) :=
    ⟨_, rfl⟩
  have hlo₁C₀ : C₀ ≤ lo₁ := by rw [hlo₁]; exact le_trans (le_max_left _ _) (le_max_left _ _)
  have hlo₁C₁ : C₁ ≤ lo₁ := by rw [hlo₁]; exact le_trans (le_max_right _ _) (le_max_left _ _)
  have hlo₁G : ∀ p : Fin m × Bool, G (Sum.inl p) xref < lo₁ := by
    intro p
    have h1 : |G (Sum.inl p) xref| ≤ ∑ p : Fin m × Bool, |G (Sum.inl p) xref| :=
      single_le_sum (f := fun p : Fin m × Bool => |G (Sum.inl p) xref|)
        (fun _ _ => abs_nonneg _) (mem_univ p)
    have h2 := le_abs_self (G (Sum.inl p) xref)
    have h3 : 1 + ∑ p : Fin m × Bool, |G (Sum.inl p) xref| ≤ lo₁ := by rw [hlo₁]; exact le_max_right _ _
    linarith
  set Λ := lo₁ + 1 with hΛ
  have hΛ4 : 4 ≤ Λ := by linarith
  have hΛC₀ : C₀ ≤ Λ := by linarith
  -- the scale near the axes
  obtain ⟨ε₁, hε₁, hzP⟩ := hzf δ (2 * Λ) (by linarith)
  obtain ⟨μr, hμr, -, hμrle⟩ := exists_pos_le_of_forall_pos (List.finRange 2)
    (fun q => xref (e.symm q) / 2) (fun q _ => by have := hxref (e.symm q); positivity)
  have hεs : ∀ᶠ ε in 𝓝[>] (0:ℝ), (0 < ε ∧ ε < ε₁ / 2) ∧
      ∀ m' ∈ range 2, ε ^ eexp H m' < μr / 2 := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < ε₁ / 2 := by
      filter_upwards [Ioo_mem_nhdsGT (by positivity : (0:ℝ) < ε₁ / 2)] with ε hε using hε
    refine h1.and ?_
    rw [Filter.eventually_all_finset]
    exact fun m' _ => eventually_small (eexp_pos H m') (by positivity)
  obtain ⟨εs, ⟨hεs0, hεs1⟩, hεsμ⟩ := hεs.exists
  have hzsS := hzP εs hεs0 (by linarith)
  have hzh : ∀ j, bf εs j < fdot (a j) (xref ∘ e.symm) := by
    intro j
    have h1 := hzsS.1 μr hμr (fun m' hm' => hεsμ m' (mem_range.mpr hm'))
      (fun q => xref (e.symm q) / 2) (fun q => hμrle q (List.mem_finRange q)) j
    have h2 := hapos j (xref ∘ e.symm) (fun q => hxref _)
    have h3 : fdot (a j) (fun q => xref (e.symm q) / 2) = fdot (a j) (xref ∘ e.symm) / 2 := by
      simp only [fdot, Function.comp_apply, sum_div]
      exact sum_congr rfl fun q _ => by ring
    linarith
  set εt := εs / 2 with hεt
  have hεt0 : 0 < εt := by positivity
  -- the absorbing set
  set K : Set (Concentration S) := {x | (∀ p : Fin m × Bool, G (Sum.inl p) x ≤ Λ + offs β Λ p.1) ∧
      (∀ j, bf εt j ≤ fdot (a j) (x ∘ e.symm)) ∧ N.StoichCompatible xref x} with hK
  -- bounds on the infinity region
  have hdiag : ∀ (l σ : ℝ) (x : Concentration S), C₀ ≤ l → σ ≤ 1 → (∀ s, 0 < x s) →
      (∀ p : Fin m × Bool, G (Sum.inl p) x ≤ l + offs β l p.1 + σ) → ∀ s, x s ≤ 2 * l := by
    intro l σ x hl hσ hx hall s
    have h1 := hall (⟨m - 1, by omega⟩, false)
    rw [hGnrm] at h1
    simp only [hnrm, Sum.elim_inl, Bool.false_eq_true, ite_false, hfd, hβlast] at h1
    have ho := ((hinfC l hl).1 (m - 1) (by omega)).2
    have hy0 := hx (e.symm 0)
    have hy1 := hx (e.symm 1)
    have hs : s = e.symm 0 ∨ s = e.symm 1 := by
      have : e s = 0 ∨ e s = 1 := (show ∀ q : Fin 2, q = 0 ∨ q = 1 by decide) (e s)
      rcases this with h | h
      · left; rw [← h, Equiv.symm_apply_apply]
      · right; rw [← h, Equiv.symm_apply_apply]
    have hl4 : 4 ≤ l := le_trans hC₀4 hl
    simp only [Function.comp_apply, one_mul] at h1
    rcases hs with rfl | rfl <;> linarith
  have hzsT := hzP εt hεt0 (by linarith)
  have hfdc : ∀ j, Continuous fun x : Concentration S => fdot (a j) (x ∘ e.symm) := by
    intro j
    unfold fdot
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_apply _)
  have hcompat_closed : IsClosed {x : Concentration S | N.StoichCompatible xref x} := by
    have hc : IsClosed (N.stoichSubspace : Set (S → ℝ)) := Submodule.closed_of_finiteDimensional _
    exact hc.preimage (continuous_id.sub continuous_const)
  have hKclosed : IsClosed K := by
    have h1 : IsClosed {x : Concentration S |
        ∀ p : Fin m × Bool, G (Sum.inl p) x ≤ Λ + offs β Λ p.1} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun p => isClosed_le (hGc _) continuous_const
    have h2 : IsClosed {x : Concentration S | ∀ j, bf εt j ≤ fdot (a j) (x ∘ e.symm)} := by
      simp only [Set.setOf_forall]
      exact isClosed_iInter fun j => isClosed_le continuous_const (hfdc j)
    have : K = ({x : Concentration S | ∀ p : Fin m × Bool, G (Sum.inl p) x ≤ Λ + offs β Λ p.1} ∩
        {x : Concentration S | ∀ j, bf εt j ≤ fdot (a j) (x ∘ e.symm)}) ∩
        {x : Concentration S | N.StoichCompatible xref x} := by
      ext x; simp [hK, and_assoc]
    rw [this]
    exact (h1.inter h2).inter hcompat_closed
  have hKbox : ∀ x ∈ K, ∀ s, εt ^ eexp H 0 ≤ x s ∧ x s ≤ 2 * Λ := by
    intro x hx s
    obtain ⟨hxi, hxz, -⟩ := hx
    have hfl : ∀ s, εt ^ eexp H 0 ≤ x s := fun s => by
      have := hzsT.2.1 (x ∘ e.symm) hxz (e s)
      simpa using this
    have hpos : ∀ s, 0 < x s := fun s => lt_of_lt_of_le (rpow_pos_of_pos hεt0 _) (hfl s)
    exact ⟨hfl s, hdiag Λ 0 x hΛC₀ zero_le_one hpos (fun p => by linarith [hxi p]) s⟩
  have hKcpt : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ =>
      isCompact_Icc (a := εt ^ eexp H 0) (b := 2 * Λ)) hKclosed ?_
    intro x hx s _
    exact hKbox x hx s
  have hKclass : K ⊆ N.positiveCompatibilityClass xref := by
    intro x hx
    refine ⟨hx.2.2, fun s => lt_of_lt_of_le (rpow_pos_of_pos hεt0 _) (hKbox x hx s).1⟩
  refine ⟨K, hKcpt, hKclass, fun κ hκ x₀ hx₀ Γ hΓ0 hΓd => ?_⟩
  obtain ⟨hx₀c, hx₀p⟩ := hx₀
  -- confinement of the trajectory
  obtain ⟨η₀, B₀, hη₀, hconf⟩ := N.twoSpecies_endotacticStd_confined_varK hS κ hend hρ hκ hx₀p
  set A : Set (Concentration S) := {x | (∀ s, η₀ ≤ x s ∧ x s ≤ B₀) ∧ N.StoichCompatible xref x}
    with hA
  have hAcpt : IsCompact A := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ =>
      isCompact_Icc (a := η₀) (b := B₀)) ?_ ?_
    · have h1 : IsClosed {x : Concentration S | ∀ s, η₀ ≤ x s ∧ x s ≤ B₀} := by
        simp only [Set.setOf_forall]
        exact isClosed_iInter fun s => (isClosed_le continuous_const (continuous_apply s)).inter
          (isClosed_le (continuous_apply s) continuous_const)
      exact h1.inter hcompat_closed
    · intro x hx s _
      exact hx.1 s
  have hApos : ∀ x ∈ A, ∀ s, 0 < x s := fun x hx s => lt_of_lt_of_le hη₀ (hx.1 s).1
  have htrajγ : ∀ t : ℝ, 0 ≤ t → Γ t ∈ A := by
    intro t ht
    refine ⟨hconf Γ hΓ0 hΓd t ht, ?_⟩
    have : N.StoichCompatible (Γ 0) (Γ t) :=
      N.sub_mem_stoichSubspace_of_solution_varK κ ht fun τ hτ => hΓd τ hτ.1
    rw [hΓ0] at this
    exact hx₀c.trans this
  -- a bound for the start point
  have hGbound : ∀ (p : Fin m × Bool) (x : Concentration S), (∀ s, 0 < x s) →
      G (Sum.inl p) x ≤ (|β 0| + 2) * (x (e.symm 0) + x (e.symm 1)) := by
    intro p x hx
    obtain ⟨k, side⟩ := p
    rw [hGnrm]
    have hx0 := hx (e.symm 0)
    have hx1 := hx (e.symm 1)
    have hbk := hβabs k k.isLt
    have hb1 : β k * x (e.symm 1) ≤ (|β 0| + 1) * x (e.symm 1) :=
      le_trans (le_abs_self _) (by
        rw [abs_mul, abs_of_pos hx1]; exact mul_le_mul_of_nonneg_right hbk hx1.le)
    have hb0 : β k * x (e.symm 0) ≤ (|β 0| + 1) * x (e.symm 0) :=
      le_trans (le_abs_self _) (by
        rw [abs_mul, abs_of_pos hx0]; exact mul_le_mul_of_nonneg_right hbk hx0.le)
    have h3 : 0 ≤ |β 0| * x (e.symm 0) := mul_nonneg (abs_nonneg _) hx0.le
    have h4 : 0 ≤ |β 0| * x (e.symm 1) := mul_nonneg (abs_nonneg _) hx1.le
    have e1 : (|β 0| + 2) * (x (e.symm 0) + x (e.symm 1)) =
        |β 0| * x (e.symm 0) + |β 0| * x (e.symm 1) + 2 * x (e.symm 0) + 2 * x (e.symm 1) := by ring
    have e2 : (|β 0| + 1) * x (e.symm 1) = |β 0| * x (e.symm 1) + x (e.symm 1) := by ring
    have e3 : (|β 0| + 1) * x (e.symm 0) = |β 0| * x (e.symm 0) + x (e.symm 0) := by ring
    cases side
    · simp only [hnrm, Sum.elim_inl, Bool.false_eq_true, ite_false, hfd, Function.comp_apply]
      linarith
    · simp only [hnrm, Sum.elim_inl, ite_true, hfd, Function.comp_apply]
      linarith
  have hρ1 : (∃ r : N.R, True) → ρ ≤ 1 := by
    rintro ⟨r, -⟩
    have h := hκ 0 r
    have h1 : ρ ≤ 1 / ρ := le_trans h.1 h.2
    rw [le_div_iff₀ hρ] at h1
    nlinarith
  have hvD : ∀ t : ℝ, 0 ≤ t → ∀ i,
      ∑ s, nS i s * N.massActionVectorField (κ t) (Γ t) s ≤ Dm i (Γ t) := fun t ht i =>
    hdom (κ t) (hκ t) i (Γ t) fun s => (hApos _ (htrajγ t ht) s).le
  have hstrictD : ∀ i (p : Concentration S), p ∈ A →
      (∀ h ∈ H, 0 < fdot (nrm i) h → δ ≤ ∑ q, h q * log (p (e.symm q))) →
      (∃ r, ∑ s, nS i s * N.reactionVector r s ≠ 0) → Dm i p < 0 := by
    intro i p hpA hv hne
    obtain ⟨r, hr⟩ := hne
    exact (hfield (κs i) (hκsb (hρ1 ⟨r, trivial⟩) i) i p (hApos p hpA) hv).2 ⟨r, hr⟩
  -- Stage 1: the infinity facets
  have : Nonempty (Fin m × Bool) := ⟨(⟨0, by omega⟩, false)⟩
  set B₁ := (|β 0| + 2) * (x₀ (e.symm 0) + x₀ (e.symm 1)) with hB₁
  set hi₁ := max (lo₁ + 2) B₁ with hhi₁
  have hlohi₁ : lo₁ < hi₁ := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hlo₁pos : 0 < lo₁ := by linarith
  -- invariance of the infinity region along the solution
  have hinv₁ : ∀ l, C₀ ≤ l → ∀ t₁ : ℝ, 0 ≤ t₁ →
      (∀ p : Fin m × Bool, G (Sum.inl p) (Γ t₁) ≤ l + offs β l p.1) →
      ∀ t, t₁ ≤ t → ∀ p : Fin m × Bool, G (Sum.inl p) (Γ t) ≤ l + offs β l p.1 := by
    intro l hlC₀ t₁ ht₁0 ht₁ t htt p
    have hst := stays_of_band_vel (ι := Fin m × Bool)
      (fun τ => N.massActionVectorField (κ (t₁ + τ)) (Γ (t₁ + τ)))
      (fun p => nS (Sum.inl p)) (fun p => l + offs β l p.1) one_pos
      (fun τ => Γ (t₁ + τ))
      (fun τ hτ => (hΓd (t₁ + τ) (by positivity)).comp_const_add t₁ τ)
      (by
        intro p
        have := ht₁ p
        simpa [hG] using this)
      (by
        intro τ hτ σ hσ0 hσ1 hall p hact
        have hxA := htrajγ (t₁ + τ) (by positivity)
        have hxpos := hApos _ hxA
        have hv := hvinf l hlC₀ σ hσ0 hσ1 (Γ (t₁ + τ) ∘ e.symm) (fun q => hxpos _)
          (fun p' => by rw [← hGnrm]; exact hall p') p (by rw [← hGnrm]; exact hact)
        exact (hfield (κ (t₁ + τ)) (hκ _) (Sum.inl p) _ hxpos hv).1)
    have := hst (t - t₁) (by linarith) p
    have e : t₁ + (t - t₁) = t := by ring
    simpa [hG, e] using this
  have hstage1 := eventually_mem_of_monotone_family_vel
    (fun t => N.massActionVectorField (κ t) (Γ t)) (fun p => Dm (Sum.inl p)) (fun p => hDmc _)
    (fun p => nS (Sum.inl p)) (fun p l => l + offs β l p.1) hlohi₁
    (fun p l hl => (hasDerivAt_add_offs β p.1 (by linarith [hl.1])).continuousAt.continuousWithinAt)
    (fun p => (hmon p.1 p.1.isLt).mono fun l hl => le_trans hlo₁C₁ hl.1)
    Γ hΓd (fun t ht p => hvD t ht (Sum.inl p)) A hAcpt htrajγ
    ⟨0, le_rfl, fun t ht p => by
      have := hinv₁ hi₁ (le_trans hlo₁C₀ hlohi₁.le) 0 le_rfl (by
        intro p
        rw [hΓ0]
        have h1 := hGbound p x₀ hx₀p
        have h2 := ((hinfC hi₁ (le_trans hlo₁C₀ hlohi₁.le)).1 p.1 p.1.isLt).1
        have h3 : B₁ ≤ hi₁ := le_max_right _ _
        linarith) t ht p
      simpa [hG] using this⟩
    (by
      intro l hl p hpA hpR q hq
      have hlC₀ : C₀ ≤ l := le_trans hlo₁C₀ hl.1.le
      have hppos := hApos p hpA
      have hv := hvinf l hlC₀ 0 le_rfl zero_le_one (p ∘ e.symm) (fun q => hppos _)
        (fun p' => by rw [← hGnrm, add_zero]; exact hpR p') q (by rw [← hGnrm, add_zero]; exact hq)
      have hne : ∃ r, ∑ s, nS (Sum.inl q) s * N.reactionVector r s ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have h1 := hperp (Sum.inl q) hcon p hpA.2
        have h2 := hlo₁G q
        have h3 := ((hinfC l hlC₀).1 q.1 q.1.isLt).1
        have h4 : G (Sum.inl q) p = l + offs β l q.1 := hq
        linarith [hl.1]
      exact hstrictD (Sum.inl q) p hpA hv hne)
  obtain ⟨T₁, hT₁0, hT₁⟩ := hstage1 Λ ⟨by linarith, le_trans (by linarith) (le_max_left _ _)⟩
  -- Stage 2: the facets near the axes, inside the box `x ≤ 2Λ`
  set y₁ := Γ T₁ with hy₁
  have hy₁A : y₁ ∈ A := htrajγ T₁ hT₁0
  have hy₁pos := hApos y₁ hy₁A
  obtain ⟨μ₁, hμ₁, -, hμ₁le⟩ := exists_pos_le_of_forall_pos (List.finRange 2)
    (fun q => y₁ (e.symm q)) (fun q _ => hy₁pos _)
  have hεx : ∀ᶠ ε in 𝓝[>] (0:ℝ), (0 < ε ∧ ε < εt) ∧ ∀ m' ∈ range 2, ε ^ eexp H m' < μ₁ / 2 := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < εt := by
      filter_upwards [Ioo_mem_nhdsGT hεt0] with ε hε using hε
    refine h1.and ?_
    rw [Filter.eventually_all_finset]
    exact fun m' _ => eventually_small (eexp_pos H m') (by positivity)
  obtain ⟨εx, ⟨hεx0, hεxt⟩, hεxμ⟩ := hεx.exists
  set Γ₂ : ℝ → Concentration S := fun τ => Γ (T₁ + τ) with hΓ₂
  have hΓ₂d : ∀ τ : ℝ, 0 ≤ τ →
      HasDerivAt Γ₂ (N.massActionVectorField (κ (T₁ + τ)) (Γ₂ τ)) τ :=
    fun τ hτ => (hΓd (T₁ + τ) (by positivity)).comp_const_add T₁ τ
  have hΓ₂A : ∀ τ : ℝ, 0 ≤ τ → Γ₂ τ ∈ A := fun τ hτ => htrajγ (T₁ + τ) (by positivity)
  set c₂ : (Fin m × Bool) ⊕ ιz → ℝ → ℝ :=
    fun i l => Sum.elim (fun p : Fin m × Bool => Λ + offs β Λ p.1) (fun j => -bf (-l) j) i
    with hc₂
  have hGinr : ∀ j (x : Concentration S), G (Sum.inr j) x = -fdot (a j) (x ∘ e.symm) := by
    intro j x
    rw [hGnrm]
    simp only [hnrm, Sum.elim_inr, hfdneg]
  -- the validity of the combined region at scale `ε`
  have hvz : ∀ ε, εx ≤ ε → ε < εs → ∀ σ, 0 ≤ σ → σ ≤ min 1 (ε ^ eexp H 0 / 2) →
      ∀ x : Concentration S, (∀ s, 0 < x s) →
      (∀ i, G i x ≤ c₂ i (-ε) + σ) → ∀ i, G i x = c₂ i (-ε) + σ →
      ∀ h ∈ H, 0 < fdot (nrm i) h → δ ≤ ∑ q, h q * log (x (e.symm q)) := by
    intro ε hε1 hε2 σ hσ0 hσ x hpos hall i hact
    have hσ1 : σ ≤ 1 := le_trans hσ (min_le_left _ _)
    have hall_inl : ∀ p : Fin m × Bool, fdot (nrm (Sum.inl p)) (x ∘ e.symm) ≤
        Λ + offs β Λ p.1 + σ := fun p => by rw [← hGnrm]; exact hall (Sum.inl p)
    rcases i with p | j
    · exact hvinf Λ hΛC₀ σ hσ0 hσ1 (x ∘ e.symm) (fun q => hpos _) hall_inl p
        (by rw [← hGnrm]; exact hact)
    · have hε0 : 0 < ε := lt_of_lt_of_le hεx0 hε1
      have hzε := hzP ε hε0 (by linarith)
      have hxM : ∀ q, (x ∘ e.symm) q ≤ 2 * Λ := fun q =>
        hdiag Λ σ x hΛC₀ hσ1 hpos (fun p => by rw [hGnrm]; exact hall_inl p) _
      have hcj : ∀ j', bf ε j' - σ ≤ fdot (a j') (x ∘ e.symm) := by
        intro j'
        have := hall (Sum.inr j')
        rw [hGinr] at this
        simp only [hc₂, Sum.elim_inr, neg_neg] at this
        linarith
      have hactj : fdot (a j) (x ∘ e.symm) = bf ε j - σ := by
        have := hact
        rw [hGinr] at this
        simp only [hc₂, Sum.elim_inr, neg_neg] at this
        linarith
      intro h hh hpos'
      have hneg : fdot (a j) h < 0 := by
        simp only [hnrm, Sum.elim_inr, hfdneg] at hpos'
        linarith
      exact hzε.2.2.2 σ hσ0 (le_trans hσ (min_le_right _ _)) (x ∘ e.symm) (fun q => hpos _)
        hxM hcj j hactj h hh hneg
  have hlohi₂ : -εs < -εx := by linarith
  -- the start region of stage 2 is invariant
  have hhi₂ : ∀ τ : ℝ, 0 ≤ τ → ∀ i, G i (Γ₂ τ) ≤ c₂ i (-εx) := by
    have hR' : 0 < min 1 (εx ^ eexp H 0 / 2) := lt_min one_pos (by
      have := rpow_pos_of_pos hεx0 (eexp H 0); positivity)
    have hst := stays_of_band_vel (fun τ => N.massActionVectorField (κ (T₁ + τ)) (Γ₂ τ)) nS
      (fun i => c₂ i (-εx)) hR' Γ₂ hΓ₂d
      (by
        intro i
        rcases i with p | j
        · have := hT₁ T₁ le_rfl p
          simpa [hc₂, hΓ₂, hG] using this
        · have h1 := (hzP εx hεx0 (by linarith)).1 μ₁ hμ₁
            (fun m' hm' => hεxμ m' (mem_range.mpr hm')) (y₁ ∘ e.symm)
            (fun q => hμ₁le q (List.mem_finRange q)) j
          have h2 : G (Sum.inr j) (Γ₂ 0) = -fdot (a j) (y₁ ∘ e.symm) := by
            rw [hGinr]; simp only [hΓ₂, add_zero, hy₁]
          show G (Sum.inr j) (Γ₂ 0) ≤ c₂ (Sum.inr j) (-εx)
          rw [h2]
          simp only [hc₂, Sum.elim_inr, neg_neg]
          linarith)
      (by
        intro τ hτ σ hσ0 hσ hall i hact
        have hxpos := hApos _ (hΓ₂A τ hτ)
        have hv := hvz εx le_rfl (by linarith) σ hσ0 hσ (Γ₂ τ) hxpos
          (fun i' => hall i') i hact
        exact (hfield (κ (T₁ + τ)) (hκ _) i _ hxpos hv).1)
    intro τ hτ i
    have := hst τ hτ i
    simpa [hG] using this
  have hstage2 := eventually_mem_of_monotone_family_vel
    (fun τ => N.massActionVectorField (κ (T₁ + τ)) (Γ₂ τ)) Dm hDmc nS c₂ hlohi₂
    (by
      intro i
      rcases i with p | j
      · exact continuousOn_const
      · simp only [hc₂, Sum.elim_inr]
        refine ContinuousOn.neg ?_
        refine (hbcont j).comp continuous_neg.continuousOn ?_
        intro l hl
        simp only [Set.mem_Ioi]
        linarith [hl.2])
    (by
      intro i
      rcases i with p | j
      · exact monotoneOn_const
      · intro l₁ hl₁ l₂ hl₂ h12
        simp only [hc₂, Sum.elim_inr, neg_le_neg_iff]
        exact hbmono j (show (0:ℝ) < -l₂ by linarith [hl₂.2]) (show (0:ℝ) < -l₁ by linarith [hl₁.2])
          (by linarith))
    Γ₂ hΓ₂d (fun τ hτ i => hvD (T₁ + τ) (by positivity) i) A hAcpt hΓ₂A
    ⟨0, le_rfl, fun τ hτ i => by
      have := hhi₂ τ hτ i
      simpa [hG] using this⟩
    (by
      intro l hl p hpA hpR i hi
      have hε1 : εx ≤ -l := by linarith [hl.2]
      have hε2 : -l < εs := by linarith [hl.1]
      have hppos := hApos p hpA
      have hl' : l = -(-l) := by ring
      have hεpos : 0 < -l := lt_of_lt_of_le hεx0 hε1
      have hv := hvz (-l) hε1 hε2 0 le_rfl (le_min zero_le_one (by
          have := rpow_pos_of_pos hεpos (eexp H 0); positivity)) p hppos
        (fun i' => by rw [add_zero, ← hl']; exact hpR i') i (by rw [add_zero, ← hl']; exact hi)
      have hne : ∃ r, ∑ s, nS i s * N.reactionVector r s ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have h1 := hperp i hcon p hpA.2
        rcases i with q | j
        · have h2 := hlo₁G q
          have h3 := ((hinfC Λ hΛC₀).1 q.1 q.1.isLt).1
          have h4 : G (Sum.inl q) p = Λ + offs β Λ q.1 := by simpa [hc₂] using hi
          linarith
        · have h2 := hzh j
          have h3 : bf (-l) j ≤ bf εs j :=
            hbmono j hεpos hεs0 hε2.le
          have h4 : G (Sum.inr j) p = -bf (-l) j := by simpa [hc₂] using hi
          rw [h1, hGinr] at h4
          linarith
      exact hstrictD i p hpA hv hne)
  obtain ⟨T₂, hT₂0, hT₂⟩ := hstage2 (-εt) ⟨by linarith, by linarith⟩
  -- assemble
  refine ⟨T₁ + T₂, by positivity, fun t ht => ?_⟩
  have hτ : T₂ ≤ t - T₁ := by linarith
  have hmem := hT₂ (t - T₁) hτ
  have hyA := hΓ₂A (t - T₁) (by linarith)
  have e : T₁ + (t - T₁) = t := by ring
  simp only [hΓ₂, e] at hmem hyA
  refine ⟨fun p => ?_, fun j => ?_, hyA.2⟩
  · have := hmem (Sum.inl p)
    simpa [hc₂, hG] using this
  · have := hmem (Sum.inr j)
    have h2 := hGinr j (Γ t)
    simp only [hc₂, Sum.elim_inr, neg_neg] at this
    rw [show (∑ s, nS (Sum.inr j) s * Γ t s) = G (Sum.inr j) (Γ t) from rfl, h2] at this
    linarith


/-- **Two-species endotactic networks are permanent** (Craciun–Nazarov–Pantea 2013), trajectory
form, fixed rates: the special case of constant rate constants. -/
theorem twoSpecies_endotacticStd_genuinePermanent (N : Network S)
    (hS : Fintype.card S = 2) (hend : N.EndotacticStd) (κ : N.RateConstants) :
    N.GenuinePermanentForRates κ := by
  intro xref hxref
  obtain ⟨ρ, hρ, hb⟩ := N.exists_rate_bounds κ
  obtain ⟨K, hK, hKs, hab⟩ := N.twoSpecies_endotacticStd_permanent_varK hS hend hρ xref hxref
  exact ⟨K, hK, hKs, fun x₀ hx₀ Γ hΓ0 hΓd =>
    hab (fun _ => κ) (fun _ r => hb r) x₀ hx₀ Γ hΓ0 hΓd⟩

/-- **Two-species endotactic networks are permanent**, flow form (the library's
`StructurallyPermanent`): a consequence of the trajectory form. -/
theorem twoSpecies_endotacticStd_structurallyPermanent (N : Network S)
    (hS : Fintype.card S = 2) (hend : N.EndotacticStd) : N.StructurallyPermanent := by
  intro κ ϕ γ hflow xref hxref
  obtain ⟨hγ0, hϕγ, hsol⟩ := hflow
  obtain ⟨K, hK, hKs, hab⟩ := N.twoSpecies_endotacticStd_genuinePermanent hS hend κ xref hxref
  refine ⟨K, hK, hKs, fun x₀ hx₀ => ?_⟩
  obtain ⟨T, hT0, hT⟩ := hab x₀ hx₀ (γ x₀) (hγ0 x₀) (hsol x₀)
  refine ⟨Set.Ici ⟨T, hT0⟩, Ici_mem_atTop _, closure_minimal ?_ hK.isClosed⟩
  rintro _ ⟨t, ht, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  have : ϕ t y = γ y t := hϕγ y t
  rw [this]
  exact hT t ht
end Network
end CRNT

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The frontier's `TwoSpeciesEndotacticPermanenceClaim` (Craciun–Nazarov–Pantea) holds. -/
theorem twoSpeciesEndotacticPermanenceClaim (N : Network S) :
    N.TwoSpeciesEndotacticPermanenceClaim :=
  fun hS hend => N.twoSpecies_endotacticStd_structurallyPermanent hS hend

/-- The frontier's `TwoSpeciesWRPermanenceClaim` holds. -/
theorem twoSpeciesWRPermanenceClaim (N : Network S) : N.TwoSpeciesWRPermanenceClaim :=
  N.twoSpeciesWRPermanence_of_endotacticPermanence N.twoSpeciesEndotacticPermanenceClaim

/-- **Two-species weakly reversible networks are permanent.** -/
theorem twoSpecies_weaklyReversible_structurallyPermanent (N : Network S)
    (hS : Fintype.card S = 2) (hwr : N.WeaklyReversible) : N.StructurallyPermanent :=
  N.twoSpeciesWRPermanenceClaim hS hwr

end Network
end CRNT

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Two-species weakly reversible networks are permanent with tempered rates** (the
two-species case of the Extended Permanence Conjecture of Craciun–Nazarov–Pantea for weakly
reversible networks). -/
theorem twoSpecies_weaklyReversible_permanent_varK (N : Network S)
    (hS : Fintype.card S = 2) (hwr : N.WeaklyReversible) {ρ : ℝ} (hρ : 0 < ρ)
    (xref : Concentration S) (hxref : xref.Positive) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → N.RateConstants, (∀ t r, ρ ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ρ) →
      ∀ x₀ ∈ N.positiveCompatibilityClass xref, ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → Γ t ∈ K :=
  N.twoSpecies_endotacticStd_permanent_varK hS hwr.endotacticStd hρ xref hxref

/-- **Two-species weakly reversible networks are permanent**, trajectory form. -/
theorem twoSpecies_weaklyReversible_genuinePermanent (N : Network S)
    (hS : Fintype.card S = 2) (hwr : N.WeaklyReversible) (κ : N.RateConstants) :
    N.GenuinePermanentForRates κ :=
  N.twoSpecies_endotacticStd_genuinePermanent hS hwr.endotacticStd κ

end Network
end CRNT
