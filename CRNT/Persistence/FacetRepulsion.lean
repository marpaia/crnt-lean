import CRNT.Persistence.WeaklyReversibleField
import CRNT.Dynamics.DissipationBound
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Facets are repelling for weakly reversible systems (Anderson–Shiu 2010, Theorem 3.2)

Let `x₀` be positive and `z` a nonnegative point of its compatibility class whose zero set is
exactly `W`.  The face of the class through `z` is a facet precisely when the projection of the
stoichiometric subspace onto the `W`-coordinates has dimension at most one (`hfacet`).  Then for a
weakly reversible mass-action system there is `δ > 0` such that every species of `W` has
nonnegative rate of change at every positive state within `δ` of `z`
(`facet_repelling_of_weaklyReversible`).

Proof, following Anderson–Shiu:
* the projected subspace contains `x₀|_W ≠ 0`, so every reaction vector restricted to `W` is
  `γ_r · x₀|_W` (`exists_facet_coefficient`);
* for a reaction with `γ_r < 0`, weak reversibility gives a path from its target back to its
  source, hence a reaction with `γ > 0` whose source is strictly smaller on every `W`-coordinate
  (`exists_dominating_reaction`);
* the monomial ratio of the two sources is continuous at `z` and vanishes there, so near `z` each
  decreasing reaction is outweighed by its dominating increasing one.

Nothing here is an axiom or a `sorry`.
-/

open Finset Filter Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Under the facet condition, every reaction vector restricted to `W` is a multiple of
`x₀|_W`. -/
theorem exists_facet_coefficient (N : Network S) {W : Finset S} (hW : W.Nonempty)
    {x₀ z : Concentration S} (hx₀ : x₀.Positive) (hzW : ∀ i ∈ W, z i = 0)
    (hzP : z - x₀ ∈ N.stoichSubspace)
    (hfacet : ∃ v : S → ℝ, ∀ r : N.R, ∃ c : ℝ, ∀ i ∈ W, N.reactionVector r i = c * v i) :
    ∀ r : N.R, ∃ γ : ℝ, ∀ i ∈ W, N.reactionVector r i = γ * x₀ i := by
  obtain ⟨v, hv⟩ := hfacet
  -- the vectors whose `W`-part is a multiple of `v` form a submodule containing `S`
  let V : Submodule ℝ (S → ℝ) :=
    { carrier := {s | ∃ c : ℝ, ∀ i ∈ W, s i = c * v i}
      add_mem' := by
        rintro a b ⟨ca, ha⟩ ⟨cb, hb⟩
        exact ⟨ca + cb, fun i hi => by simp [ha i hi, hb i hi]; ring⟩
      zero_mem' := ⟨0, fun i _ => by simp⟩
      smul_mem' := by
        rintro c a ⟨ca, ha⟩
        exact ⟨c * ca, fun i hi => by simp [ha i hi]; ring⟩ }
  have hSV : N.stoichSubspace ≤ V := by
    unfold stoichSubspace
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, rfl⟩
    exact hv r
  obtain ⟨c₀, hc₀⟩ := hSV hzP
  obtain ⟨i₀, hi₀⟩ := hW
  have hc₀ne : c₀ ≠ 0 := by
    intro h
    have := hc₀ i₀ hi₀
    simp [hzW i₀ hi₀, h] at this
    exact (hx₀ i₀).ne' this
  intro r
  obtain ⟨c, hc⟩ := hv r
  refine ⟨-c / c₀, fun i hi => ?_⟩
  have h1 := hc₀ i hi
  simp only [Pi.sub_apply, hzW i hi, zero_sub] at h1
  rw [hc i hi, div_mul_eq_mul_div, eq_div_iff hc₀ne, show x₀ i = -(c₀ * v i) by linarith]
  ring

/-- Along a reaction path, `W`-parts move along `x₀|_W` by the change of `τ c = c i₀ / x₀ i₀`. -/
theorem wpart_of_reaches (N : Network S) {W : Finset S} {x₀ : Concentration S}
    (hx₀ : x₀.Positive) {i₀ : S} (hi₀ : i₀ ∈ W) {γ : N.R → ℝ}
    (hγ : ∀ r, ∀ i ∈ W, N.reactionVector r i = γ r * x₀ i) {c d : Complex S}
    (h : N.Reaches c d) :
    ∀ i ∈ W, ((d i : ℝ) - c i) = ((d i₀ : ℝ) - c i₀) / x₀ i₀ * x₀ i := by
  induction h with
  | refl => intro i _; simp
  | tail _ hbd ih =>
    rename_i b e _
    obtain ⟨q, hqs, hqt⟩ := hbd
    intro i hi
    have hq := hγ q i hi
    have hq₀ := hγ q i₀ hi₀
    rw [reactionVector_apply, hqs, hqt] at hq hq₀
    have hih := ih i hi
    have hx := (hx₀ i₀).ne'
    have e1 : ((e i : ℝ) - c i) = (e i - b i) + (b i - c i) := by ring
    have e2 : ((e i₀ : ℝ) - c i₀) = (e i₀ - b i₀) + (b i₀ - c i₀) := by ring
    rw [e1, e2, hq, hq₀, hih, add_div, add_mul]
    field_simp

/-- A path from outside an upper set to inside has a crossing edge followed by a path to the end. -/
theorem exists_crossing_with_suffix {α : Type*} {r : α → α → Prop} (P : α → Prop) {c d : α}
    (h : Relation.ReflTransGen r c d) (hc : ¬ P c) (hd : P d) :
    ∃ c' d', r c' d' ∧ ¬ P c' ∧ P d' ∧ Relation.ReflTransGen r d' d := by
  induction h with
  | refl => exact absurd hd hc
  | @tail b e hcb hbe ih =>
    by_cases hb : P b
    · obtain ⟨c', d', h1, h2, h3, h4⟩ := ih hb
      exact ⟨c', d', h1, h2, h3, h4.tail hbe⟩
    · exact ⟨_, _, hbe, hb, hd, Relation.ReflTransGen.refl⟩

/-- **Dominating reaction.** For a reaction decreasing the species of `W`, there is a reaction
increasing them whose source is strictly smaller on every coordinate of `W`. -/
theorem exists_dominating_reaction (N : Network S) (hwr : N.WeaklyReversible) {W : Finset S}
    {x₀ : Concentration S} (hx₀ : x₀.Positive) {i₀ : S} (hi₀ : i₀ ∈ W) {γ : N.R → ℝ}
    (hγ : ∀ r, ∀ i ∈ W, N.reactionVector r i = γ r * x₀ i) {r : N.R} (hr : γ r < 0) :
    ∃ q : N.R, 0 < γ q ∧ ∀ i ∈ W,
      (N.reaction q).source i + 1 ≤ (N.reaction r).source i := by
  set τ : Complex S → ℝ := fun c => (c i₀ : ℝ) / x₀ i₀ with hτ
  have hx := hx₀ i₀
  have hτq : ∀ q : N.R, τ (N.reaction q).target - τ (N.reaction q).source = γ q := by
    intro q
    have h := hγ q i₀ hi₀
    rw [reactionVector_apply] at h
    simp only [hτ]
    rw [← sub_div, h]; field_simp
  obtain ⟨c', d', ⟨q, hqs, hqt⟩, hc', hd', hsuf⟩ :=
    exists_crossing_with_suffix (fun c => τ (N.reaction r).source ≤ τ c) (hwr r)
      (show ¬ (τ (N.reaction r).source ≤ τ (N.reaction r).target) from
        not_le.mpr (by linarith [hτq r])) le_rfl
  refine ⟨q, ?_, fun i hi => ?_⟩
  · have h1 := hτq q
    rw [hqs, hqt] at h1
    have h2 : τ c' < τ (N.reaction r).source := not_le.mp hc'
    have h3 : τ (N.reaction r).source ≤ τ d' := hd'
    linarith
  · -- `c'` reaches the source of `r`
    have hreach : N.Reaches c' (N.reaction r).source :=
      Relation.ReflTransGen.head ⟨q, hqs, hqt⟩ hsuf
    have hw := N.wpart_of_reaches hx₀ hi₀ hγ hreach i hi
    have hgap : 0 < ((N.reaction r).source i₀ - c' i₀ : ℝ) / x₀ i₀ := by
      have h2 : τ c' < τ (N.reaction r).source := not_le.mp hc'
      simp only [hτ] at h2
      rw [div_lt_div_iff_of_pos_right hx] at h2
      exact div_pos (by linarith) hx
    have hpos : (0 : ℝ) < (N.reaction r).source i - c' i := by
      rw [hw]; exact mul_pos hgap (hx₀ i)
    rw [hqs]
    have : (c' i : ℝ) < (N.reaction r).source i := by linarith
    exact_mod_cast this

/-- Monomial ratio with integer exponents. -/
noncomputable def monoRatio (a b : Complex S) (x : Concentration S) : ℝ :=
  ∏ s, x s ^ ((a s : ℤ) - (b s : ℤ))

theorem massActionMonomial_eq_monoRatio_mul {a b : Complex S} {x : Concentration S}
    (hx : x.Positive) : a.massActionMonomial x = monoRatio a b x * b.massActionMonomial x := by
  unfold monoRatio Complex.massActionMonomial
  rw [← prod_mul_distrib]
  refine prod_congr rfl fun s _ => ?_
  rw [zpow_sub₀ (hx s).ne', zpow_natCast, zpow_natCast, div_mul_cancel₀ _
    (pow_ne_zero _ (hx s).ne')]

/-- **Anderson–Shiu 2010, Theorem 3.2 (facets are repelling).** -/
theorem facet_repelling_of_weaklyReversible (N : Network S) (κ : N.RateConstants)
    (hwr : N.WeaklyReversible) {W : Finset S} (hW : W.Nonempty) {x₀ z : Concentration S}
    (hx₀ : x₀.Positive) (hzW : ∀ i, z i = 0 ↔ i ∈ W) (hzP : z - x₀ ∈ N.stoichSubspace)
    (hfacet : ∃ v : S → ℝ, ∀ r : N.R, ∃ c : ℝ, ∀ i ∈ W, N.reactionVector r i = c * v i) :
    ∃ δ > 0, ∀ x : Concentration S, x.Positive → dist x z < δ →
      ∀ i ∈ W, 0 ≤ N.massActionVectorField κ x i := by
  classical
  choose γ hγ using N.exists_facet_coefficient hW hx₀ (fun i hi => (hzW i).mpr hi) hzP hfacet
  obtain ⟨i₀, hi₀⟩ := hW
  have hdom := fun r (hr : γ r < 0) => N.exists_dominating_reaction hwr hx₀ hi₀ hγ hr
  let D : N.R → N.R := fun r => if h : γ r < 0 then (hdom r h).choose else r
  have hD : ∀ r, γ r < 0 → 0 < γ (D r) ∧ ∀ i ∈ W,
      (N.reaction (D r)).source i + 1 ≤ (N.reaction r).source i := by
    intro r hr
    have := (hdom r hr).choose_spec
    simp only [D, dif_pos hr]; exact this
  set n : ℝ := (Fintype.card N.R : ℝ) with hn
  let H : N.R → Concentration S → ℝ := fun r =>
    monoRatio (N.reaction r).source (N.reaction (D r)).source
  let ε : N.R → ℝ := fun r => κ.k (D r) * γ (D r) / (n * κ.k r * (-γ r))
  -- continuity of the ratio at `z`, where it vanishes
  have hlim : ∀ r, γ r < 0 → Tendsto (H r) (𝓝 z) (𝓝 0) := by
    intro r hr
    have hexp : ∀ s ∈ W, (0 : ℤ) < ((N.reaction r).source s : ℤ) - (N.reaction (D r)).source s :=
      fun s hs => by have := (hD r hr).2 s hs; omega
    have hz0 : (∏ s, z s ^ (((N.reaction r).source s : ℤ) - (N.reaction (D r)).source s)) = 0 :=
      prod_eq_zero (mem_univ i₀) (by rw [(hzW i₀).mpr hi₀]; exact zero_zpow _ (hexp i₀ hi₀).ne')
    rw [← hz0]
    refine tendsto_finsetProd _ fun s _ => ?_
    have hcont := continuousAt_zpow₀ (z s)
      (((N.reaction r).source s : ℤ) - (N.reaction (D r)).source s) (by
        by_cases hs : s ∈ W
        · exact Or.inr (hexp s hs).le
        · exact Or.inl fun h => hs ((hzW s).mp h))
    exact hcont.tendsto.comp ((continuous_apply s).tendsto z)
  have hev : ∀ᶠ x in 𝓝 z, ∀ r, γ r < 0 → H r x < ε r := by
    refine Filter.eventually_all.mpr fun r => ?_
    by_cases hr : γ r < 0
    · have hεpos : 0 < ε r := by
        have hcard : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨r⟩
        exact div_pos (mul_pos (κ.positive _) (hD r hr).1)
          (mul_pos (mul_pos hcard (κ.positive r)) (by linarith))
      exact ((hlim r hr).eventually (gt_mem_nhds hεpos)).mono fun x hx _ => hx
    · exact Filter.Eventually.of_forall fun x h => absurd h hr
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ, hδ, fun x hx hxz i hi => ?_⟩
  have hsmall := hball hxz
  set T : N.R → ℝ := fun r => κ.k r * (N.reaction r).source.massActionMonomial x * γ r with hT
  have hfield : N.massActionVectorField κ x i = (∑ r, T r) * x₀ i := by
    rw [massActionVectorField_apply, sum_mul]
    refine sum_congr rfl fun r _ => ?_
    rw [hγ r i hi]; simp only [hT, massActionRate]; ring
  rw [hfield]
  refine mul_nonneg ?_ (hx₀ i).le
  have hm : ∀ r, 0 ≤ (N.reaction r).source.massActionMonomial x := fun r =>
    Complex.massActionMonomial_nonneg hx.nonnegative _
  set Pos := ∑ r ∈ univ.filter (fun r => ¬ γ r < 0), T r with hPos
  have hPosnn : 0 ≤ Pos := sum_nonneg fun r hr => by
    have := (mem_filter.mp hr).2; push Not at this
    exact mul_nonneg (mul_nonneg (κ.positive r).le (hm r)) this
  have hTD : ∀ r, γ r < 0 → T (D r) ≤ Pos := by
    intro r hr
    have hmem : D r ∈ univ.filter (fun r => ¬ γ r < 0) :=
      mem_filter.mpr ⟨mem_univ _, not_lt.mpr (hD r hr).1.le⟩
    exact single_le_sum (f := T) (fun q hq => by
      have := (mem_filter.mp hq).2; push Not at this
      exact mul_nonneg (mul_nonneg (κ.positive q).le (hm q)) this) hmem
  have hneg : ∀ r ∈ univ.filter (fun r => γ r < 0), -T r ≤ Pos / n := by
    intro r hr
    have hr' := (mem_filter.mp hr).2
    have hcard : 0 < n := by rw [hn]; exact_mod_cast Fintype.card_pos_iff.mpr ⟨r⟩
    have hHr := hsmall r hr'
    have hratio := massActionMonomial_eq_monoRatio_mul (a := (N.reaction r).source)
      (b := (N.reaction (D r)).source) hx
    have hkr := κ.positive r
    have hmD := hm (D r)
    -- `-T r = k_r (-γ_r) H_r m_D ≤ k_r (-γ_r) ε_r m_D = T (D r) / n`
    have h1 : -T r = κ.k r * (-γ r) * H r x * (N.reaction (D r)).source.massActionMonomial x := by
      simp only [hT, hratio]; ring
    have h2 : κ.k r * (-γ r) * H r x ≤ κ.k r * (-γ r) * ε r :=
      mul_le_mul_of_nonneg_left hHr.le (mul_nonneg hkr.le (by linarith))
    have h3 : κ.k r * (-γ r) * ε r = κ.k (D r) * γ (D r) / n := by
      have hγne : γ r ≠ 0 := hr'.ne
      simp only [ε]; field_simp
    have h4 : -T r ≤ κ.k (D r) * γ (D r) / n * (N.reaction (D r)).source.massActionMonomial x := by
      rw [h1, ← h3]; exact mul_le_mul_of_nonneg_right h2 hmD
    have h5 : κ.k (D r) * γ (D r) / n * (N.reaction (D r)).source.massActionMonomial x =
        T (D r) / n := by simp only [hT]; ring
    rw [h5] at h4
    exact h4.trans (div_le_div_of_nonneg_right (hTD r hr') hcard.le)
  have hsplit := sum_filter_add_sum_filter_not univ (fun r => γ r < 0) T
  have hnegsum : -∑ r ∈ univ.filter (fun r => γ r < 0), T r ≤ Pos := by
    rw [← sum_neg_distrib]
    calc ∑ r ∈ univ.filter (fun r => γ r < 0), -T r
        ≤ ∑ _r ∈ univ.filter (fun r => γ r < 0), Pos / n := sum_le_sum hneg
      _ = (univ.filter (fun r => γ r < 0)).card * (Pos / n) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ n * (Pos / n) := by
          refine mul_le_mul_of_nonneg_right ?_ (div_nonneg hPosnn (by positivity))
          rw [hn]; exact_mod_cast card_le_univ _
      _ ≤ Pos := by
          rcases (Nat.cast_nonneg (Fintype.card N.R) : (0:ℝ) ≤ _).eq_or_lt with h0 | hpos
          · rw [← hn] at h0; rw [← h0]; simp [hPosnn]
          · rw [← hn] at hpos; rw [mul_div_cancel₀ _ hpos.ne']
  linarith

end Network
end CRNT
