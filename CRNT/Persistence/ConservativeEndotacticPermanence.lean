import CRNT.Persistence.TwoSpeciesPermanence

/-!
# Conservative endotactic networks are permanent

For a network that is endotactic in the standard sense and conservative (a strictly positive
conservation law), in any number of species, and for rate constants varying in time inside a
band `[ρ, 1/ρ]`: every positive stoichiometric compatibility class contains one compact set of
positive states that eventually contains every forward solution starting in the class, for all
rate constants in the band (`endotacticStd_conservative_permanent_varK`; fixed rates:
`endotacticStd_conservative_genuinePermanent`).

The classes are bounded by the conservation law, so only the facets near the axes are needed:
the regions of `exists_zsh_family` in the box of the class at the scales `ε ∈ (0, ε₁)` form a
nested family; the field strictly decreases every active facet functional not orthogonal to the
stoichiometric subspace (at the extremal rate vector of the band), the orthogonal ones being
constant and inactive on the class for small `ε`; `eventually_mem_of_monotone_family_vel` gives
eventual entry at a scale depending only on the class.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Finset Real Filter Topology CRNT.Persistence

variable {S : Type} [DecidableEq S] [Fintype S]

set_option maxHeartbeats 8000000 in
/-- **Conservative endotactic networks are permanent, with tempered rates.** -/
theorem endotacticStd_conservative_permanent_varK (N : Network S) [Nonempty S]
    (hend : N.EndotacticStd) (hcons : N.IsConservative) {ρ : ℝ} (hρ : 0 < ρ)
    (xref : Concentration S) (hxref : xref.Positive) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → N.RateConstants, (∀ t r, ρ ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ρ) →
      ∀ x₀ ∈ N.positiveCompatibilityClass xref, ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → Γ t ∈ K := by
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card S = n := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by rw [← hn]; exact Fintype.card_pos
  obtain e : S ≃ Fin n := Fintype.equivFinOfCardEq hn
  -- complex differences, closed under permutations
  obtain ⟨D, hD⟩ : ∃ D : Complex S × Complex S → Fin n → ℝ,
      D = fun p q => ((p.1 (e.symm q) : ℝ) - p.2 (e.symm q)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Finset (Fin n → ℝ), H =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).biUnion
        fun ρ => (N.complexes ×ˢ N.complexes).image fun p => D p ∘ ρ := ⟨_, rfl⟩
  have hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin n), h ∘ ρ ∈ H := by
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
  have htrlog : ∀ (h : Fin n → ℝ) (x : S → ℝ),
      ∑ q, h q * log (x (e.symm q)) = ∑ s, h (e s) * log (x s) := by
    intro h x
    rw [← Equiv.sum_comp e (fun q => h q * log (x (e.symm q)))]
    simp
  -- the facets near the axes
  obtain ⟨ιz, hFz, hNz, a, bf, hbmono, hbcont, hapos, hzf⟩ := exists_zsh_family hn1 H hsym
  have := hFz
  have := hNz
  set nrm : ιz → Fin n → ℝ := fun j => -a j with hnrm
  set nS : ιz → S → ℝ := fun i s => nrm i (e s) with hnS
  have hdotS : ∀ i (x : S → ℝ), fdot (nrm i) (x ∘ e.symm) = ∑ s, nS i s * x s := by
    intro i x
    have : nrm i = nS i ∘ e.symm := by funext q; simp [hnS]
    rw [this, htr]
  have hfdneg : ∀ (j : ιz) (y : Fin n → ℝ), fdot (-a j) y = -fdot (a j) y := by
    intro j y; simp [fdot, sum_neg_distrib]
  -- the slack
  obtain ⟨C, hC0, hC⟩ := exists_ratio_bound
    (fun (i : ιz) (r : N.R) => ∑ s, (-nS i s) * N.reactionVector r s)
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
      ∀ (i : ιz) (x : Concentration S), x.Positive →
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
  set κs : ιz → N.RateConstants := fun i =>
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
  set Dm : ιz → Concentration S → ℝ :=
    fun i x => ∑ s, nS i s * N.massActionVectorField (κs i) x s with hDm
  have hDmc : ∀ i, Continuous (Dm i) := fun i =>
    continuous_finsetSum _ fun s _ => continuous_const.mul
      ((continuous_apply s).comp (N.continuous_massActionVectorField (κs i)))
  -- the region functionals
  set G : ιz → Concentration S → ℝ := fun i x => ∑ s, nS i s * x s with hG
  have hGnrm : ∀ i (x : Concentration S), G i x = fdot (nrm i) (x ∘ e.symm) := fun i x =>
    (hdotS i x).symm
  have hGa : ∀ j (x : Concentration S), G j x = -fdot (a j) (x ∘ e.symm) := by
    intro j x
    rw [hGnrm]
    simp only [hnrm, hfdneg]
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
  -- the class is bounded by the conservation law
  obtain ⟨w, hw⟩ := hcons
  set Bc : ℝ := ∑ s, weightedTotal w xref / w s with hBc
  have hW : 0 ≤ weightedTotal w xref :=
    Finset.sum_nonneg fun s _ => mul_nonneg (hw.2 s).le (hxref s).le
  have hBc0 : 0 ≤ Bc := sum_nonneg fun s _ => div_nonneg hW (hw.2 s).le
  have hbound : ∀ x : Concentration S, x.Nonnegative → N.StoichCompatible xref x →
      ∀ s, x s ≤ Bc := by
    intro x hx hc s
    have h1 := N.coordinate_le_of_strictPSemiflow hw hxref.nonnegative hx hc s
    have h2 : weightedTotal w xref / w s ≤ Bc :=
      Finset.single_le_sum (f := fun s => weightedTotal w xref / w s)
        (fun s _ => div_nonneg hW (hw.2 s).le) (Finset.mem_univ s)
    linarith
  set M : ℝ := Bc + 1 with hM
  obtain ⟨ε₁, hε₁, hzP⟩ := hzf δ M (by linarith)
  -- the class scale
  obtain ⟨μr, hμr, -, hμrle⟩ := exists_pos_le_of_forall_pos (List.finRange n)
    (fun q => xref (e.symm q) / 2) (fun q _ => by have := hxref (e.symm q); positivity)
  have hεs : ∀ᶠ ε in 𝓝[>] (0:ℝ), (0 < ε ∧ ε < ε₁ / 2) ∧
      ∀ m' ∈ range n, ε ^ eexp H m' < μr / 2 := by
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
  have hzsT := hzP εt hεt0 (by linarith)
  -- the absorbing set
  set K : Set (Concentration S) :=
    {x | (∀ j, bf εt j ≤ fdot (a j) (x ∘ e.symm)) ∧ N.StoichCompatible xref x} with hK
  have hfdc : ∀ j, Continuous fun x : Concentration S => fdot (a j) (x ∘ e.symm) := by
    intro j
    unfold fdot
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_apply _)
  have hcompat_closed : IsClosed {x : Concentration S | N.StoichCompatible xref x} := by
    have hc : IsClosed (N.stoichSubspace : Set (S → ℝ)) := Submodule.closed_of_finiteDimensional _
    exact hc.preimage (continuous_id.sub continuous_const)
  have hKclosed : IsClosed K := by
    have h2 : IsClosed {x : Concentration S | ∀ j, bf εt j ≤ fdot (a j) (x ∘ e.symm)} := by
      have : {x : Concentration S | ∀ j, bf εt j ≤ fdot (a j) (x ∘ e.symm)} =
          ⋂ j, {x | bf εt j ≤ fdot (a j) (x ∘ e.symm)} := by ext; simp
      rw [this]
      exact isClosed_iInter fun j => isClosed_le continuous_const (hfdc j)
    exact h2.inter hcompat_closed
  have hKbox : ∀ x ∈ K, ∀ s, εt ^ eexp H 0 ≤ x s ∧ x s ≤ Bc := by
    intro x hx s
    obtain ⟨hxz, hxc⟩ := hx
    have hfl : ∀ s, εt ^ eexp H 0 ≤ x s := fun s => by
      have := hzsT.2.1 (x ∘ e.symm) hxz (e s)
      simpa using this
    have hnn : x.Nonnegative := fun s => le_trans (rpow_pos_of_pos hεt0 _).le (hfl s)
    exact ⟨hfl s, hbound x hnn hxc s⟩
  have hKcpt : IsCompact K := by
    refine IsCompact.of_isClosed_subset (isCompact_univ_pi fun _ =>
      isCompact_Icc (a := εt ^ eexp H 0) (b := Bc)) hKclosed ?_
    intro x hx s _
    exact hKbox x hx s
  have hKclass : K ⊆ N.positiveCompatibilityClass xref := by
    intro x hx
    exact ⟨hx.2, fun s => lt_of_lt_of_le (rpow_pos_of_pos hεt0 _) (hKbox x hx s).1⟩
  refine ⟨K, hKcpt, hKclass, fun κ hκ x₀ hx₀ Γ hΓ0 hΓd => ?_⟩
  obtain ⟨hx₀c, hx₀p⟩ := hx₀
  -- confinement of the solution
  obtain ⟨K₀, hK₀c, hK₀pos, hK₀⟩ :=
    N.endotacticStd_conservative_confined_varK κ hend ⟨w, hw⟩ hρ hκ hx₀p
  set A : Set (Concentration S) := K₀ ∩ {x | N.StoichCompatible xref x} with hA
  have hAcpt : IsCompact A := hK₀c.inter_right hcompat_closed
  have hApos : ∀ x ∈ A, ∀ s, 0 < x s := fun x hx => hK₀pos x hx.1
  have htrajγ : ∀ t : ℝ, 0 ≤ t → Γ t ∈ A := by
    intro t ht
    refine ⟨hK₀ Γ hΓ0 hΓd t ht, ?_⟩
    have : N.StoichCompatible (Γ 0) (Γ t) :=
      N.sub_mem_stoichSubspace_of_solution_varK κ ht fun τ hτ => hΓd τ hτ.1
    rw [hΓ0] at this
    exact hx₀c.trans this
  have hAM : ∀ x ∈ A, ∀ q, (x ∘ e.symm) q ≤ M := fun x hx q => by
    have := hbound x (fun s => (hApos x hx s).le) hx.2 (e.symm q)
    simp only [Function.comp_apply]
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
  -- the start scale
  obtain ⟨μ₁, hμ₁, -, hμ₁le⟩ := exists_pos_le_of_forall_pos (List.finRange n)
    (fun q => x₀ (e.symm q)) (fun q _ => hx₀p _)
  have hεx : ∀ᶠ ε in 𝓝[>] (0:ℝ), (0 < ε ∧ ε < εt) ∧ ∀ m' ∈ range n, ε ^ eexp H m' < μ₁ / 2 := by
    have h1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), 0 < ε ∧ ε < εt := by
      filter_upwards [Ioo_mem_nhdsGT hεt0] with ε hε using hε
    refine h1.and ?_
    rw [Filter.eventually_all_finset]
    exact fun m' _ => eventually_small (eexp_pos H m') (by positivity)
  obtain ⟨εx, ⟨hεx0, hεxt⟩, hεxμ⟩ := hεx.exists
  set c₂ : ιz → ℝ → ℝ := fun j l => -bf (-l) j with hc₂
  -- validity at scale `ε`
  have hvz : ∀ ε, εx ≤ ε → ε < εs → ∀ σ, 0 ≤ σ → σ ≤ ε ^ eexp H 0 / 2 →
      ∀ x : Concentration S, x ∈ A →
      (∀ i, G i x ≤ c₂ i (-ε) + σ) → ∀ i, G i x = c₂ i (-ε) + σ →
      ∀ h ∈ H, 0 < fdot (nrm i) h → δ ≤ ∑ q, h q * log (x (e.symm q)) := by
    intro ε hε1 hε2 σ hσ0 hσ x hxA hall j hact
    have hε0 : 0 < ε := lt_of_lt_of_le hεx0 hε1
    have hzε := hzP ε hε0 (by linarith)
    have hcj : ∀ j', bf ε j' - σ ≤ fdot (a j') (x ∘ e.symm) := by
      intro j'
      have := hall j'
      rw [hGa] at this
      simp only [hc₂, neg_neg] at this
      linarith
    have hactj : fdot (a j) (x ∘ e.symm) = bf ε j - σ := by
      have := hact
      rw [hGa] at this
      simp only [hc₂, neg_neg] at this
      linarith
    intro h hh hpos'
    have hneg : fdot (a j) h < 0 := by
      simp only [hnrm, hfdneg] at hpos'
      linarith
    exact hzε.2.2.2 σ hσ0 hσ (x ∘ e.symm) (fun q => hApos x hxA _) (hAM x hxA) hcj j hactj h hh
      hneg
  have hlohi₂ : -εs < -εx := by linarith
  -- the start region is invariant
  have hhi₂ : ∀ τ : ℝ, 0 ≤ τ → ∀ i, G i (Γ τ) ≤ c₂ i (-εx) := by
    have hR' : 0 < εx ^ eexp H 0 / 2 := by
      have := rpow_pos_of_pos hεx0 (eexp H 0); positivity
    have hst := stays_of_band_vel (fun τ => N.massActionVectorField (κ τ) (Γ τ)) nS
      (fun i => c₂ i (-εx)) hR' Γ hΓd
      (by
        intro j
        have h1 := (hzP εx hεx0 (by linarith)).1 μ₁ hμ₁
          (fun m' hm' => hεxμ m' (mem_range.mpr hm')) (x₀ ∘ e.symm)
          (fun q => hμ₁le q (List.mem_finRange q)) j
        have h2 : G j (Γ 0) = -fdot (a j) (x₀ ∘ e.symm) := by rw [hGa, hΓ0]
        show G j (Γ 0) ≤ c₂ j (-εx)
        rw [h2]
        simp only [hc₂, neg_neg]
        linarith)
      (by
        intro τ hτ σ hσ0 hσ hall i hact
        have hxA := htrajγ τ hτ
        have hv := hvz εx le_rfl (by linarith) σ hσ0 hσ (Γ τ) hxA hall i hact
        exact (hfield (κ τ) (hκ _) i _ (hApos _ hxA) hv).1)
    intro τ hτ i
    have := hst τ hτ i
    simpa [hG] using this
  have hstage := eventually_mem_of_monotone_family_vel
    (fun τ => N.massActionVectorField (κ τ) (Γ τ)) Dm hDmc nS c₂ hlohi₂
    (by
      intro j
      simp only [hc₂]
      refine ContinuousOn.neg ?_
      refine (hbcont j).comp continuous_neg.continuousOn ?_
      intro l hl
      simp only [Set.mem_Ioi]
      linarith [hl.2])
    (by
      intro j l₁ hl₁ l₂ hl₂ h12
      simp only [hc₂, neg_le_neg_iff]
      exact hbmono j (show (0:ℝ) < -l₂ by linarith [hl₂.2]) (show (0:ℝ) < -l₁ by linarith [hl₁.2])
        (by linarith))
    Γ hΓd hvD A hAcpt htrajγ
    ⟨0, le_rfl, fun τ hτ i => by
      have := hhi₂ τ hτ i
      simpa [hG] using this⟩
    (by
      intro l hl p hpA hpR i hi
      have hε1 : εx ≤ -l := by linarith [hl.2]
      have hε2 : -l < εs := by linarith [hl.1]
      have hl' : l = -(-l) := by ring
      have hv := hvz (-l) hε1 hε2 0 le_rfl (by
          have := rpow_pos_of_pos (lt_of_lt_of_le hεx0 hε1) (eexp H 0); positivity) p hpA
        (fun i' => by rw [add_zero, ← hl']; exact hpR i') i (by rw [add_zero, ← hl']; exact hi)
      have hne : ∃ r, ∑ s, nS i s * N.reactionVector r s ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have h1 := hperp i hcon p hpA.2
        have h2 := hzh i
        have hεpos : 0 < -l := lt_of_lt_of_le hεx0 hε1
        have h3 : bf (-l) i ≤ bf εs i := hbmono i hεpos hεs0 hε2.le
        have h4 : G i p = -bf (-l) i := by simpa [hc₂] using hi
        rw [h1, hGa] at h4
        linarith
      exact hstrictD i p hpA hv hne)
  obtain ⟨T, hT0, hT⟩ := hstage (-εt) ⟨by linarith, by linarith⟩
  refine ⟨T, hT0, fun t ht => ⟨fun j => ?_, (htrajγ t (le_trans hT0 ht)).2⟩⟩
  have := hT t ht j
  have h2 := hGa j (Γ t)
  simp only [hc₂, neg_neg] at this
  rw [show (∑ s, nS j s * Γ t s) = G j (Γ t) from rfl, h2] at this
  linarith

/-- **Conservative endotactic networks are permanent** (fixed rates, trajectory form). -/
theorem endotacticStd_conservative_genuinePermanent (N : Network S) [Nonempty S]
    (hend : N.EndotacticStd) (hcons : N.IsConservative) (κ : N.RateConstants) :
    N.GenuinePermanentForRates κ := by
  intro xref hxref
  obtain ⟨ρ, hρ, hb⟩ := N.exists_rate_bounds κ
  obtain ⟨K, hK, hKs, hab⟩ :=
    N.endotacticStd_conservative_permanent_varK hend hcons hρ xref hxref
  exact ⟨K, hK, hKs, fun x₀ hx₀ Γ hΓ0 hΓd =>
    hab (fun _ => κ) (fun _ r => hb r) x₀ hx₀ Γ hΓ0 hΓd⟩

/-- **Conservative weakly reversible networks are permanent, with tempered rates.** -/
theorem weaklyReversible_conservative_permanent_varK (N : Network S) [Nonempty S]
    (hwr : N.WeaklyReversible) (hcons : N.IsConservative) {ρ : ℝ} (hρ : 0 < ρ)
    (xref : Concentration S) (hxref : xref.Positive) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → N.RateConstants, (∀ t r, ρ ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ρ) →
      ∀ x₀ ∈ N.positiveCompatibilityClass xref, ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t → Γ t ∈ K :=
  N.endotacticStd_conservative_permanent_varK hwr.endotacticStd hcons hρ xref hxref

end Network
end CRNT
