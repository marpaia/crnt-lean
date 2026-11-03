import CRNT.Persistence.StronglyEndotacticPermanence
import CRNT.Persistence.UniformFieldBound
import CRNT.Persistence.VariableRateFloor

/-!
# Strongly endotactic networks with tempered (time-dependent) rates

Gopalkrishnan–Miller–Shiu, Theorem 1.1, is stated for *tempered* systems: each rate constant may
vary in time inside a compact positive interval (their mass-action differential inclusions).
This module proves the variable-rate forms, with rates `κ : ℝ → RateConstants` satisfying
`ε ≤ κ_r(t) ≤ ε⁻¹`:

* `genuineOrbit_pos_varK`: forward positivity;
* `TierDescending.forward_bounded_on_varK`: one bound for all tempered solutions starting in a
  compact subset of a positive class;
* `persistent_step_varK`, `StronglyEndotacticStd.persistent_uniform_varK`: uniform persistence;
* `exists_entry_logBox_varK`: every tempered orbit enters a fixed compact set of the class;
* `StronglyEndotacticStd.permanent_varK`: for each positive class one compact set `K` such that
  every tempered solution from a positive state of the class is in `K` from some time on.
-/

open Filter Set
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Forward positivity for time-dependent rates bounded above.** -/
theorem genuineOrbit_pos_varK (N : Network S) (κ : ℝ → N.RateConstants) {K : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t r, (κ t).k r ≤ K)
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) :
    ∀ t, 0 ≤ t → (Γ t).Positive := by
  intro T hT
  show ∀ s, 0 < Γ T s
  by_contra hcon
  simp only [not_forall, not_lt] at hcon
  obtain ⟨s₀, hs₀⟩ := hcon
  -- Continuity of the orbit on the compact interval `[0, T]`.
  have hcontOn : ContinuousOn Γ (Set.Icc 0 T) :=
    fun t ht => (hΓd t ht.1).continuousAt.continuousWithinAt
  have hcs : ∀ s, ContinuousOn (fun t => Γ t s) (Set.Icc 0 T) :=
    fun s => (continuous_apply s).comp_continuousOn hcontOn
  -- A uniform box bound on `[0, T]` from compactness.
  obtain ⟨Bb, hBb⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
  have hBbound : ∀ t ∈ Set.Icc (0:ℝ) T, ∀ s, Γ t s ≤ Bb := by
    intro t ht s
    calc Γ t s ≤ |Γ t s| := le_abs_self _
      _ = ‖Γ t s‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖Γ t‖ := norm_le_pi_norm (Γ t) s
      _ ≤ Bb := hBb t ht
  -- The field's linear lower bound on that box.
  obtain ⟨L, _hLnn, hbound⟩ := N.exists_field_lower_bound_uniform hK0 Bb
  -- First crossing of zero, restricted to `[0, T]`.
  set A : Set ℝ := {t | (0 ≤ t ∧ t ≤ T) ∧ ∃ s, Γ t s ≤ 0} with hA
  have hAne : A.Nonempty := ⟨T, ⟨hT, le_refl T⟩, s₀, hs₀⟩
  have hAcl : IsClosed A := by
    have heq : A = ⋃ s : S, (Set.Icc 0 T ∩ (fun t => Γ t s) ⁻¹' Set.Iic 0) := by
      ext t
      simp only [hA, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage,
        Set.mem_Iic, Set.mem_setOf_eq]
      constructor
      · rintro ⟨⟨h0, hT'⟩, s, hs⟩; exact ⟨s, ⟨h0, hT'⟩, hs⟩
      · rintro ⟨s, ⟨h0, hT'⟩, hs⟩; exact ⟨⟨h0, hT'⟩, s, hs⟩
    rw [heq]
    exact isClosed_iUnion_of_finite fun s =>
      (hcs s).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hAbdd : BddBelow A := ⟨0, fun t ht => ht.1.1⟩
  set t₁ := sInf A with ht₁def
  have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
  have ht₁0 : 0 ≤ t₁ := ht₁A.1.1
  have ht₁leT : t₁ ≤ T := ht₁A.1.2
  obtain ⟨s₁, hs₁⟩ := ht₁A.2
  have hbefore : ∀ t, 0 ≤ t → t ≤ T → t < t₁ → (Γ t).Positive := by
    intro t ht0 htT htlt s
    by_contra hle
    rw [not_lt] at hle
    exact absurd (csInf_le hAbdd ⟨⟨ht0, htT⟩, s, hle⟩) (not_le.mpr htlt)
  rcases eq_or_lt_of_le ht₁0 with ht₁eq | ht₁pos
  · rw [← ht₁eq] at hs₁
    exact absurd (hΓ0 s₁) (not_lt.mpr hs₁)
  · -- The exponential lower bound on `[0, t₁)`, then passed to the limit at `t₁`.
    have key : ∀ t ∈ Set.Ico 0 t₁, Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁ := by
      intro t ht
      refine ge_mul_exp_of_forward_deriv_ge ht.1
        (fun τ hτ => (hasDerivAt_pi.mp (hΓd τ hτ.1)) s₁) ?_
      intro τ hτ
      have hτlt : τ < t₁ := lt_of_le_of_lt hτ.2 ht.2
      have hτT : τ ≤ T := le_of_lt (lt_of_lt_of_le hτlt ht₁leT)
      have hpos := hbefore τ hτ.1 hτT hτlt
      exact hbound (κ τ) (hK τ) (Γ τ) hpos.nonnegative (hBbound τ ⟨hτ.1, hτT⟩) s₁
    have hclosed :
        IsClosed (Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁}) := by
      have hcd : ContinuousOn
          (fun τ => Γ τ s₁ - Γ 0 s₁ * Real.exp (-(L * τ))) (Set.Icc 0 T) :=
        (hcs s₁).sub ((continuous_const.mul
          (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))).continuousOn)
      have heq2 : Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁}
          = Set.Icc 0 T ∩ (fun τ => Γ τ s₁ - Γ 0 s₁ * Real.exp (-(L * τ))) ⁻¹' Set.Ici 0 := by
        ext t
        simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_Ici, sub_nonneg]
      rw [heq2]
      exact hcd.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hsub : Set.Ico 0 t₁ ⊆
        Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁} := by
      intro τ hτ
      exact ⟨⟨hτ.1, le_of_lt (lt_of_lt_of_le hτ.2 ht₁leT)⟩, key τ hτ⟩
    have ht₁mem : t₁ ∈ Set.Icc 0 T ∩ {t | Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁} :=
      hclosed.closure_subset_iff.mpr hsub
        (by rw [closure_Ico (ne_of_lt ht₁pos)]; exact ⟨ht₁0, le_refl t₁⟩)
    exact absurd (lt_of_lt_of_le (mul_pos (hΓ0 s₁) (Real.exp_pos _)) ht₁mem.2) (not_lt.mpr hs₁)

/-- Rates in the band `[ε, ε⁻¹]` at all times. -/
def Tempered (N : Network S) (ε : ℝ) (κ : ℝ → N.RateConstants) : Prop :=
  ∀ t, N.RateVectorInBand ε (κ t).k

/-- A compact set of positive states lies in a log box. -/
theorem exists_logBox_of_compact {K : Set (Concentration S)} (hKc : IsCompact K)
    (hKpos : ∀ x ∈ K, x.Positive) : ∃ R : ℝ, 0 ≤ R ∧ K ⊆ logBox (S := S) R := by
  classical
  rcases K.eq_empty_or_nonempty with hK | hK
  · exact ⟨0, le_rfl, by simp [hK]⟩
  have hcoord : ∀ s : S, ∃ a b : ℝ, 0 < a ∧ ∀ x ∈ K, a ≤ x s ∧ x s ≤ b := by
    intro s
    obtain ⟨x₁, hx₁, hmin⟩ := hKc.exists_isMinOn hK (continuous_apply s).continuousOn
    obtain ⟨x₂, hx₂, hmax⟩ := hKc.exists_isMaxOn hK (continuous_apply s).continuousOn
    exact ⟨x₁ s, x₂ s, hKpos x₁ hx₁ s, fun x hx => ⟨hmin hx, hmax hx⟩⟩
  choose a b ha hab using hcoord
  set R : ℝ := ∑ s, (|Real.log (a s)| + |Real.log (b s)|)
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun s _ => by positivity
  have hle : ∀ s, |Real.log (a s)| + |Real.log (b s)| ≤ R := fun s =>
    Finset.single_le_sum (f := fun s => |Real.log (a s)| + |Real.log (b s)|)
      (fun s _ => by positivity) (Finset.mem_univ s)
  refine ⟨R, hR0, fun x hx s => ⟨?_, ?_⟩⟩
  · have h1 : Real.exp (-R) ≤ a s := by
      rw [← Real.exp_log (ha s)]
      apply Real.exp_le_exp.mpr
      have := neg_abs_le (Real.log (a s))
      linarith [hle s, abs_nonneg (Real.log (b s))]
    exact h1.trans (hab s x hx).1
  · have hbpos : 0 < b s := (ha s).trans_le ((hab s x hx).1.trans (hab s x hx).2)
    have h1 : b s ≤ Real.exp R := by
      rw [← Real.exp_log hbpos]
      apply Real.exp_le_exp.mpr
      have := le_abs_self (Real.log (b s))
      linarith [hle s, abs_nonneg (Real.log (a s))]
    exact (hab s x hx).2.trans h1

/-- **Uniform boundedness for tempered rates from a compact set of initial states.** -/
theorem TierDescending.forward_bounded_on_varK {N : Network S} (htd : N.TierDescending)
    (ε : ℝ) (xref : Concentration S) {Υ : Set (Concentration S)}
    (hΥc : IsCompact Υ) (hΥ : Υ ⊆ N.positiveCompatibilityClass xref) :
    ∃ M : ℝ, ∀ κ : ℝ → N.RateConstants, N.Tempered ε κ → ∀ γ : ℝ → Concentration S, γ 0 ∈ Υ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M := by
  classical
  obtain ⟨K, hKc, hKsub, hKneg⟩ := htd.exists_compact_class_region_negative_outside_uniform xref ε
  have href : Concentration.Positive (tierReference S : Concentration S) := fun _ => zero_lt_one
  have hVc : Continuous (fun x : Concentration S => tierEntropy x) := by
    unfold tierEntropy; exact continuous_const.add (relEntropy_continuous href)
  obtain ⟨c, hc⟩ := hKc.bddAbove_image hVc.continuousOn
  obtain ⟨cΥ, hcΥ⟩ := hΥc.bddAbove_image hVc.continuousOn
  set c' : ℝ := max c cΥ + 1 with hc'
  refine ⟨max (Real.exp 2 * 1) (c' - 1), fun κ hκ γ hγΥ hsol => ?_⟩
  have hγ0 : (γ 0).Positive := (hΥ hγΥ).2
  have hKpos : ∀ t r, (κ t).k r ≤ ε⁻¹ := fun t r => ((hκ t).2 r).2
  have hε : 0 < ε := (hκ 0).1
  have hpos := N.genuineOrbit_pos_varK κ (inv_pos.mpr hε).le hKpos hγ0 hsol
  have hcomp : ∀ t, 0 ≤ t → N.StoichCompatible xref (γ t) := fun t ht =>
    (hΥ hγΥ).1.trans (N.sub_mem_stoichSubspace_of_solution_varK κ ht fun τ hτ => hsol τ hτ.1)
  have hV : ∀ t, 0 ≤ t → tierEntropy (γ t) ≤ c' := by
    intro t ht
    have hd : ∀ τ, 0 ≤ τ → HasDerivAt (fun τ => tierEntropy (γ τ))
        (N.tierDissipation (κ τ) (γ τ)) τ := fun τ hτ =>
      N.tierEntropy_hasDerivAt (κ τ) (hpos τ hτ) fun s => (hasDerivAt_pi.mp (hsol τ hτ)) s
    refine image_le_of_deriv_right_lt_deriv_boundary' (f := fun τ => tierEntropy (γ τ))
      (f' := fun τ => N.tierDissipation (κ τ) (γ τ)) (a := 0) (b := t)
      (fun τ hτ => (hd τ hτ.1).continuousAt.continuousWithinAt)
      (fun τ hτ => (hd τ hτ.1).hasDerivWithinAt)
      (B := fun _ => c') (B' := fun _ => 0)
      (by have := hcΥ ⟨γ 0, hγΥ, rfl⟩; simp only [hc']; linarith [le_max_right c cΥ])
      continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
      (fun τ hτ heq => ?_) (Set.right_mem_Icc.2 ht)
    have hnotK : γ τ ∉ K := by
      intro hK
      have h0 : tierEntropy (γ τ) ≤ c := hc ⟨γ τ, hK, rfl⟩
      have := heq ▸ h0
      simp only [hc'] at this
      linarith [le_max_left c cΥ]
    rw [← tierDissipationWith_rateConstants]
    exact hKneg _ _ (hκ τ) ⟨hcomp τ hτ.1, hpos τ hτ.1⟩ hnotK
  intro t ht s
  have h1 : relEntropy (tierReference S) (γ t) ≤ c' - 1 := by
    have := hV t ht; unfold tierEntropy at this; linarith
  exact relEntropy_coord_le href (hpos t ht).nonnegative h1 s

/-- Bounds on the omitted coordinates and tempered rates put the projected rates in a band. -/
theorem exists_band_projRates_varK (N : Network S) (P : Finset S) {ε m M : ℝ}
    (hε : 0 < ε) (hm : 0 < m) (hM : 0 < M) :
    ∃ δ : ℝ, ∀ κ : N.RateConstants, N.RateVectorInBand ε κ.k → ∀ x : Concentration S,
      (∀ s ∉ P, m ≤ x s ∧ x s ≤ M) →
      (N.speciesProjection P).RateVectorInBand δ (N.projRates P κ x) := by
  classical
  let lo : N.R → ℝ := fun r => ε * ∏ s ∈ Pᶜ, m ^ (N.reaction r).source s
  let hi : N.R → ℝ := fun r => ε⁻¹ * ∏ s ∈ Pᶜ, M ^ (N.reaction r).source s
  have hlo : ∀ r, 0 < lo r := fun r => mul_pos hε (Finset.prod_pos fun s _ => pow_pos hm _)
  have hhi : ∀ r, 0 < hi r := fun r =>
    mul_pos (inv_pos.mpr hε) (Finset.prod_pos fun s _ => pow_pos hM _)
  obtain ⟨δ, hδ, hδlo, hδhi⟩ : ∃ δ : ℝ, 0 < δ ∧ (∀ r, δ ≤ lo r) ∧ ∀ r, hi r ≤ δ⁻¹ := by
    by_cases hR : Nonempty N.R
    · obtain ⟨r₁, -, h₁⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := N.R)) lo
      obtain ⟨r₂, -, h₂⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := N.R)) hi
      refine ⟨min (lo r₁) (hi r₂)⁻¹, lt_min (hlo r₁) (inv_pos.mpr (hhi r₂)), fun r => ?_, fun r => ?_⟩
      · exact (min_le_left _ _).trans (h₁ ▸ Finset.inf'_le lo (Finset.mem_univ r))
      · have h1 : hi r ≤ hi r₂ := h₂ ▸ Finset.le_sup' hi (Finset.mem_univ r)
        have h2 : (min (lo r₁) (hi r₂)⁻¹)⁻¹ ≥ hi r₂ := by
          rw [ge_iff_le, le_inv_comm₀ (hhi r₂) (lt_min (hlo r₁) (inv_pos.mpr (hhi r₂)))]
          exact min_le_right _ _
        linarith
    · exact ⟨1, one_pos, fun r => absurd ⟨r⟩ hR, fun r => absurd ⟨r⟩ hR⟩
  refine ⟨δ, fun κ hκ x hx => ⟨hδ, fun r => ⟨?_, ?_⟩⟩⟩
  · refine (hδlo r).trans ?_
    change lo r ≤ κ.k r * omittedMonomial P x (N.reaction r).source
    unfold omittedMonomial
    exact mul_le_mul (hκ.2 r).1 (Finset.prod_le_prod₀ (fun s _ => pow_nonneg hm.le _)
      (fun s hs => pow_le_pow_left₀ hm.le (hx s (Finset.mem_compl.mp hs)).1 _))
      (Finset.prod_nonneg fun s _ => pow_nonneg hm.le _) (κ.positive r).le
  · refine le_trans ?_ (hδhi r)
    change κ.k r * omittedMonomial P x (N.reaction r).source ≤ hi r
    unfold omittedMonomial
    exact mul_le_mul (hκ.2 r).2 (Finset.prod_le_prod₀
      (fun s hs => pow_nonneg (hm.le.trans (hx s (Finset.mem_compl.mp hs)).1) _)
      (fun s hs => pow_le_pow_left₀ (hm.le.trans (hx s (Finset.mem_compl.mp hs)).1)
        (hx s (Finset.mem_compl.mp hs)).2 _))
      (Finset.prod_nonneg fun s hs =>
        pow_nonneg (hm.le.trans (hx s (Finset.mem_compl.mp hs)).1) _) (inv_pos.mpr hε).le

/-! ## Uniform persistence for tempered rates -/

/-- `Q(P)` for a family of tempered solutions. -/
def KeepsSomeAboveV (N : Network S) (G : (ℝ → N.RateConstants) → (ℝ → Concentration S) → Prop)
    (P : Finset S) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → ∃ s ∈ P, m ≤ γ t s

/-- The induction step for tempered rates. -/
theorem persistent_step_varK {N : Network S} (hse : N.StronglyEndotacticStd) {ε : ℝ} (hε : 0 < ε)
    (G : (ℝ → N.RateConstants) → (ℝ → Concentration S) → Prop) (xref : Concentration S)
    (hbandG : ∀ κ γ, G κ γ → N.Tempered ε κ)
    (hsolG : ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t)
    (hclass : ∀ κ γ, G κ γ → γ 0 - xref ∈ N.stoichSubspace)
    {g : ℝ} (hg : 0 < g) (hg0le : ∀ κ γ, G κ γ → ∀ s, g ≤ γ 0 s)
    {M : ℝ} (hM1 : 1 ≤ M) (hMG : ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    {P : Finset S} (hP : P.Nonempty)
    (IH : ∀ s, s ∉ P → N.KeepsSomeAboveV G (insert s P)) : N.KeepsSomeAboveV G P := by
  classical
  -- the floor `m'` for the omitted coordinates
  choose! mfun hmpos hmQ using IH
  obtain ⟨m', hm'pos, hm'le⟩ : ∃ m' : ℝ, 0 < m' ∧ ∀ s, s ∉ P → m' ≤ mfun s := by
    by_cases hc : Pᶜ.Nonempty
    · refine ⟨Pᶜ.inf' hc mfun, ?_, fun s hs => Finset.inf'_le _ (Finset.mem_compl.mpr hs)⟩
      obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf' hc mfun
      rw [heq]; exact hmpos s (Finset.mem_compl.mp hs)
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, Finset.mem_compl.mpr hs⟩ hc⟩
  have fact1 : ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → (∀ s ∈ P, γ t s < m') → ∀ s, s ∉ P → m' ≤ γ t s := by
    intro κ γ hγ t ht hsmall s hs
    obtain ⟨s', hs', hle⟩ := hmQ s hs κ γ hγ t ht
    rcases Finset.mem_insert.mp hs' with rfl | hs'P
    · exact (hm'le s' hs).trans hle
    · exact absurd (lt_of_lt_of_le (hsmall s' hs'P) (hm'le s hs)) (not_lt.mpr hle)
  -- the projected network and its compact region
  set NP := N.speciesProjection P
  have htdP : NP.TierDescending :=
    (NP.stronglyEndotacticStd_iff_tierDescending).mp (StronglyEndotacticStd.speciesProjection hse P)
  obtain ⟨δ, hδ⟩ := N.exists_band_projRates_varK P hε hm'pos (zero_lt_one.trans_le hM1)
  set xrefP := projectConcentration P xref
  obtain ⟨K, hKc, hKsub, hKneg⟩ :=
    htdP.exists_compact_class_region_negative_outside_uniform xrefP δ
  -- a positive lower bound on the coordinates over `K`
  have hcoord : ∀ s : {s // s ∈ P}, ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, c ≤ x s := by
    intro s
    rcases K.eq_empty_or_nonempty with hK | hK
    · exact ⟨1, one_pos, by simp [hK]⟩
    · obtain ⟨x₀, hx₀, hmin⟩ := hKc.exists_isMinOn hK (continuous_apply s).continuousOn
      exact ⟨x₀ s, (hKsub hx₀).2 s, fun x hx => hmin hx⟩
  choose cfun hcfun hcfunK using hcoord
  set s₁ : {s // s ∈ P} := ⟨hP.choose, hP.choose_spec⟩
  have hune : (Finset.univ : Finset {s // s ∈ P}).Nonempty := ⟨s₁, Finset.mem_univ _⟩
  obtain ⟨c, hcpos, hcK⟩ : ∃ c : ℝ, 0 < c ∧ ∀ x ∈ K, ∀ s, c ≤ x s := by
    refine ⟨Finset.univ.inf' hune cfun, ?_, fun x hx s =>
      (Finset.inf'_le _ (Finset.mem_univ s)).trans (hcfunK s x hx)⟩
    obtain ⟨s, -, h⟩ := Finset.exists_mem_eq_inf' hune cfun
    rw [h]; exact hcfun s
  -- the radii `ρ' ≤ ρ`
  set ρ := min (min m' c) (min (1 / 2) g) with hρdef
  have hρpos : 0 < ρ := lt_min (lt_min hm'pos hcpos) (lt_min (by norm_num) hg)
  have hρm' : ρ ≤ m' := (min_le_left _ _).trans (min_le_left _ _)
  have hρc : ρ ≤ c := (min_le_left _ _).trans (min_le_right _ _)
  have hρ1 : ρ ≤ 1 := (min_le_right _ _).trans ((min_le_left _ _).trans (by norm_num))
  have hρg : ∀ κ γ, G κ γ → ∀ s, ρ ≤ γ 0 s := fun κ γ hγ s =>
    ((min_le_right _ _).trans (min_le_right _ _)).trans (hg0le κ γ hγ s)
  set n : ℝ := (P.card : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr hP.card_pos
  have hcard : (Finset.univ : Finset {s // s ∈ P}).card = P.card := by simp
  obtain ⟨ρ', hρ'pos, hρ'le, hρ'u⟩ := exists_small_entU hρpos
    (c := (n - 1 + entU ρ) / n) (by
      rw [div_lt_one hn]; linarith [entU_lt_one hρpos hρ1])
  have hkey : n + entU ρ < 1 + n * entU ρ' := by
    have := (div_lt_iff₀ hn).mp hρ'u
    linarith
  refine ⟨ρ', hρ'pos, fun κ γ hγ t₁ ht₁ => ?_⟩
  by_contra hnot
  push Not at hnot
  have hsol := hsolG κ γ hγ
  have hband := hbandG κ γ hγ
  have hpos : ∀ t, 0 ≤ t → (γ t).Positive :=
    N.genuineOrbit_pos_varK κ (inv_pos.mpr hε).le (fun t r => ((hband t).2 r).2)
      (fun s => hg.trans_le (hg0le κ γ hγ s)) hsol
  have hM := hMG κ γ hγ
  -- continuity of `γ`
  have hcont : ∀ t, 0 ≤ t → ContinuousAt γ t := fun t ht => (hsol t ht).continuousAt
  -- the last time before `t₁` at which some `P`-coordinate is at least `ρ`
  set A : Set ℝ := Icc 0 t₁ ∩ {t | ∃ s ∈ P, ρ ≤ γ t s} with hAdef
  have hAeq : A = ⋃ s ∈ P, Icc 0 t₁ ∩ (fun t => γ t s) ⁻¹' Ici ρ := by
    ext t; simp only [hAdef, mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_preimage, mem_Ici,
      exists_prop]
    constructor
    · rintro ⟨h1, s, hs, h2⟩; exact ⟨s, hs, h1, h2⟩
    · rintro ⟨s, hs, h1, h2⟩; exact ⟨h1, s, hs, h2⟩
  have hAc : IsClosed A := by
    rw [hAeq]
    refine isClosed_biUnion_finset fun s _ => ?_
    have hcs : ContinuousOn (fun t => γ t s) (Icc 0 t₁) := fun t ht =>
      ((continuous_apply s).continuousAt.comp (hcont t ht.1)).continuousWithinAt
    exact hcs.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, ht₁⟩, hP.choose, hP.choose_spec, hρg κ γ hγ _⟩
  have hAbdd : BddAbove A := ⟨t₁, fun t ht => ht.1.2⟩
  set t₀ := sSup A
  have ht₀A : t₀ ∈ A := hAc.csSup_mem ⟨0, hA0⟩ hAbdd
  have ht₀0 : 0 ≤ t₀ := ht₀A.1.1
  have ht₀lt : t₀ < t₁ := by
    refine lt_of_le_of_ne ht₀A.1.2 fun h => ?_
    obtain ⟨s, hs, hle⟩ := ht₀A.2
    rw [h] at hle
    exact absurd ((hnot s hs).trans_le hρ'le) (not_lt.mpr hle)
  have hsmall : ∀ t, t₀ < t → t ≤ t₁ → ∀ s ∈ P, γ t s < ρ := by
    intro t ht0 ht1 s hs
    by_contra hge
    push Not at hge
    have htA : t ∈ A := ⟨⟨ht₀0.trans ht0.le, ht1⟩, s, hs, hge⟩
    exact absurd (le_csSup hAbdd htA) (not_le.mpr ht0)
  have ht₀le : ∀ s ∈ P, γ t₀ s ≤ ρ := by
    intro s hs
    have hlim : Tendsto (fun t => γ t s) (𝓝[>] t₀) (𝓝 (γ t₀ s)) :=
      (((continuous_apply s).continuousAt.comp (hcont t₀ ht₀0)).tendsto).mono_left
        nhdsWithin_le_nhds
    refine le_of_tendsto hlim ?_
    filter_upwards [Ioo_mem_nhdsGT ht₀lt] with t ht
    exact (hsmall t ht.1 ht.2.le s hs).le
  obtain ⟨s₀, hs₀, hs₀ge⟩ := ht₀A.2
  -- the projected entropy is antitone on `[t₀, t₁]`
  set V : ℝ → ℝ := fun t => tierEntropy (projectConcentration P (γ t))
  set D : ℝ → ℝ := fun t =>
    NP.tierDissipationWith (N.projRates P (κ t) (γ t)) (projectConcentration P (γ t))
  have hD : ∀ t ∈ Ioo t₀ t₁, HasDerivAt V (D t) t ∧ D t < 0 := by
    intro t ht
    have ht0 : 0 ≤ t := ht₀0.trans ht.1.le
    refine ⟨N.projected_tierEntropy_hasDerivAt P (κ t) (hpos t ht0) (hsol t ht0), ?_⟩
    have hsm := hsmall t ht.1 ht.2.le
    have hbandP := hδ (κ t) (hband t) (γ t) fun s hs =>
      ⟨fact1 κ γ hγ t ht0 (fun s' hs' => (hsm s' hs').trans_le hρm') s hs, hM t ht0 s⟩
    have hclassP : projectConcentration P (γ t) ∈ NP.positiveCompatibilityClass xrefP := by
      refine ⟨?_, fun s => hpos t ht0 s.1⟩
      have h1 := N.sub_mem_stoichSubspace_of_solution_varK κ ht0 fun τ hτ => hsol τ hτ.1
      have h2 : γ t - xref ∈ N.stoichSubspace := by
        have := Submodule.add_mem _ h1 (hclass κ γ hγ)
        simpa [sub_add_sub_cancel] using this
      exact N.projectConcentration_sub_mem P h2
    have hnotK : projectConcentration P (γ t) ∉ K := by
      intro hK
      have h1 := hcK _ hK s₁
      have h2 := hsm s₁.1 s₁.2
      simp only [projectConcentration_apply] at h1
      linarith
    exact hKneg _ _ hbandP hclassP hnotK
  have hVcont : ContinuousOn V (Icc t₀ t₁) := by
    have hEc : Continuous (fun x : Concentration {s // s ∈ P} => tierEntropy x) := by
      unfold tierEntropy
      exact continuous_const.add (relEntropy_continuous fun _ => zero_lt_one)
    have hpc : Continuous (projectConcentration P) := continuous_pi fun s => continuous_apply s.1
    intro t ht
    exact (hEc.continuousAt.comp (hpc.continuousAt.comp (hcont t (ht₀0.trans ht.1)))).continuousWithinAt
  have hanti : AntitoneOn V (Icc t₀ t₁) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc t₀ t₁) hVcont
      (fun t ht => by rw [interior_Icc] at ht ⊢; exact (hD t ht).1.hasDerivWithinAt)
      (fun t ht => by rw [interior_Icc] at ht; exact (hD t ht).2.le)
  have hV : V t₁ ≤ V t₀ := hanti ⟨le_rfl, ht₀lt.le⟩ ⟨ht₀lt.le, le_rfl⟩ ht₀lt.le
  -- upper bound at `t₀`
  have hVt₀ : V t₀ ≤ n + entU ρ := by
    show tierEntropy (projectConcentration P (γ t₀)) ≤ n + entU ρ
    rw [tierEntropy_eq_entU]
    set s₀' : {s // s ∈ P} := ⟨s₀, hs₀⟩
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s₀')]
    have hval : projectConcentration P (γ t₀) s₀' = ρ := le_antisymm (ht₀le s₀ hs₀) hs₀ge
    rw [hval]
    have hrest : ∑ x ∈ Finset.univ.erase s₀', entU (projectConcentration P (γ t₀) x) ≤
        ((Finset.univ.erase s₀').card : ℝ) * 1 := by
      rw [← nsmul_eq_mul]
      exact Finset.sum_le_card_nsmul _ _ _ fun x _ => entU_le_one (hpos t₀ ht₀0 x.1).le
        ((ht₀le x.1 x.2).trans hρ1)
    have hc : ((Finset.univ.erase s₀').card : ℝ) = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ _), hcard, Nat.cast_sub hP.card_pos]
      simp [n]
    rw [hc, mul_one] at hrest
    linarith
  -- lower bound at `t₁`
  have hVt₁ : 1 + n * entU ρ' ≤ V t₁ := by
    show 1 + n * entU ρ' ≤ tierEntropy (projectConcentration P (γ t₁))
    rw [tierEntropy_eq_entU]
    have hsum : (Finset.univ : Finset {s // s ∈ P}).card • entU ρ' ≤
        ∑ x, entU (projectConcentration P (γ t₁) x) := by
      refine Finset.card_nsmul_le_sum _ _ _ fun x _ => ?_
      exact entU_antitoneOn ⟨(hpos t₁ ht₁ x.1).le, (hnot x.1 x.2).le.trans (hρ'le.trans hρ1)⟩
        ⟨hρ'pos.le, hρ'le.trans hρ1⟩ (hnot x.1 x.2).le
    rw [nsmul_eq_mul, hcard] at hsum
    linarith
  linarith

/-- **Uniform persistence for tempered rates.** -/
theorem StronglyEndotacticStd.persistent_uniform_varK {N : Network S}
    (hse : N.StronglyEndotacticStd) {ε : ℝ} (hε : 0 < ε)
    (G : (ℝ → N.RateConstants) → (ℝ → Concentration S) → Prop) (xref : Concentration S)
    (hbandG : ∀ κ γ, G κ γ → N.Tempered ε κ)
    (hsolG : ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t)
    (hclass : ∀ κ γ, G κ γ → γ 0 - xref ∈ N.stoichSubspace)
    {g : ℝ} (hg : 0 < g) (hg0le : ∀ κ γ, G κ γ → ∀ s, g ≤ γ 0 s)
    {M : ℝ} (hMG : ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M) :
    ∃ m : ℝ, 0 < m ∧ ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → ∀ s, m ≤ γ t s := by
  classical
  have hM' : ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → ∀ s, γ t s ≤ max M 1 := fun κ γ hγ t ht s =>
    (hMG κ γ hγ t ht s).trans (le_max_left _ _)
  have hkey : ∀ k : ℕ, ∀ P : Finset S, Pᶜ.card = k → P.Nonempty → N.KeepsSomeAboveV G P := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro P hk hP
      refine persistent_step_varK hse hε G xref hbandG hsolG hclass hg hg0le (le_max_right _ _)
        hM' hP fun s hs => ?_
      have hlt : (insert s P)ᶜ.card < k := by
        rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.mpr hs), ← hk]
        exact Nat.sub_lt (Finset.card_pos.mpr ⟨s, Finset.mem_compl.mpr hs⟩) one_pos
      exact ih _ hlt (insert s P) rfl (Finset.insert_nonempty s P)
  have hsingle : ∀ s : S, ∃ m : ℝ, 0 < m ∧ ∀ κ γ, G κ γ → ∀ t, 0 ≤ t → m ≤ γ t s := by
    intro s
    obtain ⟨m, hm, h⟩ := hkey _ {s} rfl (Finset.singleton_nonempty s)
    refine ⟨m, hm, fun κ γ hγ t ht => ?_⟩
    obtain ⟨s', hs', hle⟩ := h κ γ hγ t ht
    rw [Finset.mem_singleton.mp hs'] at hle
    exact hle
  choose mfun hmpos hmle using hsingle
  by_cases hS : Nonempty S
  · obtain ⟨s₀, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) mfun
    refine ⟨Finset.univ.inf' Finset.univ_nonempty mfun, by rw [h]; exact hmpos s₀,
      fun κ γ hγ t ht s => (Finset.inf'_le _ (Finset.mem_univ s)).trans (hmle s κ γ hγ t ht)⟩
  · exact ⟨1, one_pos, fun _ _ _ t _ s => absurd ⟨s⟩ hS⟩


/-! ## Entry and permanence for tempered rates -/

/-- The largest dissipation over the rate band, reaction by reaction. -/
noncomputable def bandMaxDissipation (N : Network S) (ε : ℝ) (x : Concentration S) : ℝ :=
  ∑ r, (ε⁻¹ * max (N.tierTerm r x) 0 + ε * min (N.tierTerm r x) 0)

theorem tierDissipationWith_le_bandMax (N : Network S) {ε : ℝ} {k : N.R → ℝ}
    (hk : N.RateVectorInBand ε k) (x : Concentration S) :
    N.tierDissipationWith k x ≤ N.bandMaxDissipation ε x := by
  rw [tierDissipationWith_eq]
  refine Finset.sum_le_sum fun r _ => ?_
  obtain ⟨h1, h2⟩ := hk.2 r
  rcases le_total 0 (N.tierTerm r x) with h | h
  · rw [max_eq_left h, min_eq_right h, mul_zero, add_zero]
    exact mul_le_mul_of_nonneg_right h2 h
  · rw [max_eq_right h, min_eq_left h, mul_zero, zero_add]
    exact mul_le_mul_of_nonpos_right h1 h

theorem bandMax_eq (N : Network S) {ε : ℝ} (hε : 0 < ε) (hne : ∀ _ : N.R, ε ≤ ε⁻¹)
    (x : Concentration S) :
    ∃ k : N.R → ℝ, N.RateVectorInBand ε k ∧ N.tierDissipationWith k x = N.bandMaxDissipation ε x := by
  classical
  refine ⟨fun r => if 0 ≤ N.tierTerm r x then ε⁻¹ else ε, ⟨hε, fun r => ?_⟩, ?_⟩
  · show ε ≤ (if 0 ≤ N.tierTerm r x then ε⁻¹ else ε) ∧ (if 0 ≤ N.tierTerm r x then ε⁻¹ else ε) ≤ ε⁻¹
    split_ifs
    · exact ⟨hne r, le_rfl⟩
    · exact ⟨le_rfl, hne r⟩
  · rw [tierDissipationWith_eq, bandMaxDissipation]
    refine Finset.sum_congr rfl fun r _ => ?_
    split_ifs with h
    · rw [max_eq_left h, min_eq_right h]; ring
    · push Not at h
      rw [max_eq_right h.le, min_eq_left h.le]; ring

theorem continuousOn_bandMax (N : Network S) (ε : ℝ) :
    ContinuousOn (N.bandMaxDissipation ε) {x | x.Positive} := by
  have hmon : ∀ y : Complex S, Continuous fun x : Concentration S => tierMonomial x y := by
    intro y; unfold tierMonomial; fun_prop
  have hmpos : ∀ y : Complex S, ∀ x : Concentration S, x.Positive → 0 < tierMonomial x y :=
    fun y x hx => Finset.prod_pos fun s _ => pow_pos (hx s) _
  have hterm : ∀ r, ContinuousOn (N.tierTerm r) {x | x.Positive} := by
    intro r
    unfold tierTerm
    refine (hmon _).continuousOn.mul (ContinuousOn.log ((hmon _).continuousOn.div
      (hmon _).continuousOn fun x hx => (hmpos _ x hx).ne') fun x hx => ?_)
    exact (div_pos (hmpos _ x hx) (hmpos _ x hx)).ne'
  unfold bandMaxDissipation
  refine continuousOn_finsetSum _ fun r _ => ?_
  have h1 : ContinuousOn (fun x => max (N.tierTerm r x) 0) {x | x.Positive} :=
    (hterm r).sup continuousOn_const
  have h2 : ContinuousOn (fun x => min (N.tierTerm r x) 0) {x | x.Positive} :=
    (hterm r).inf continuousOn_const
  exact (continuousOn_const.mul h1).add (continuousOn_const.mul h2)

/-- **Every tempered orbit enters the box.** -/
theorem exists_entry_logBox_varK {N : Network S} {ε : ℝ} (hε : 0 < ε) (xref : Concentration S)
    {R : ℝ} (hR : ∀ (k : N.R → ℝ) (x : Concentration S), N.RateVectorInBand ε k →
      x ∈ N.positiveCompatibilityClass xref → x ∉ logBox (S := S) R → N.tierDissipationWith k x < 0)
    {κ : ℝ → N.RateConstants} (hκ : N.Tempered ε κ)
    {γ : ℝ → Concentration S} (hγ0 : N.StoichCompatible xref (γ 0))
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t)
    {m M : ℝ} (hm : 0 < m) (hbounds : ∀ t, 0 ≤ t → ∀ s, m ≤ γ t s ∧ γ t s ≤ M) :
    ∃ t, 0 ≤ t ∧ γ t ∈ logBox (S := S) (R + 1) := by
  classical
  set O : Set (Concentration S) :=
    {x | ∀ s, Real.exp (-(R + 1)) < x s ∧ x s < Real.exp (R + 1)} with hOdef
  have hOopen : IsOpen O := by
    have : O = ⋂ s : S, (fun x : Concentration S => x s) ⁻¹' Ioo (Real.exp (-(R + 1)))
        (Real.exp (R + 1)) := by
      ext x; simp [hOdef]
    rw [this]
    exact isOpen_iInter_of_finite fun s => (continuous_apply s).isOpen_preimage _ isOpen_Ioo
  have hboxO : ∀ x, x ∈ logBox (S := S) R → x ∈ O := by
    intro x hx s
    have h := hx s
    exact ⟨(Real.exp_lt_exp.mpr (by linarith)).trans_le h.1,
      h.2.trans_lt (Real.exp_lt_exp.mpr (by linarith))⟩
  have hOlog : ∀ x, x ∈ O → x ∈ logBox (S := S) (R + 1) := fun x hx s =>
    ⟨(hx s).1.le, (hx s).2.le⟩
  set Λ : Set (Concentration S) := N.classInteriorBox xref m M ∩ Oᶜ
  have hΛc : IsCompact Λ := (N.isCompact_classInteriorBox xref m M).inter_right hOopen.isClosed_compl
  have hΛpos : ∀ x ∈ Λ, x.Positive := fun x hx s => hm.trans_le (hx.1.2 s).1
  have hne : ∀ _ : N.R, ε ≤ ε⁻¹ := fun r => ((hκ 0).2 r).1.trans ((hκ 0).2 r).2
  have hΛneg : ∀ x ∈ Λ, N.bandMaxDissipation ε x < 0 := fun x hx => by
    obtain ⟨k, hk, heq⟩ := N.bandMax_eq hε hne x
    rw [← heq]
    exact hR k x hk ⟨hx.1.1, hΛpos x hx⟩ fun hb => hx.2 (hboxO x hb)
  have hcls : ∀ t, 0 ≤ t → N.StoichCompatible xref (γ t) := fun t ht =>
    hγ0.trans (N.sub_mem_stoichSubspace_of_solution_varK κ ht fun τ hτ => hsol τ hτ.1)
  by_contra hno
  push Not at hno
  have hinΛ : ∀ t, 0 ≤ t → γ t ∈ Λ := fun t ht =>
    ⟨⟨hcls t ht, fun s => hbounds t ht s⟩, fun hO => hno t ht (hOlog _ hO)⟩
  -- a uniform negative bound on `Λ`
  obtain ⟨x₁, hx₁, hmax⟩ := hΛc.exists_isMaxOn ⟨γ 0, hinΛ 0 le_rfl⟩
    ((N.continuousOn_bandMax ε).mono fun x hx => hΛpos x hx)
  set η := -N.bandMaxDissipation ε x₁
  have hη : 0 < η := by have := hΛneg x₁ hx₁; simp only [η]; linarith
  have hDle : ∀ t, 0 ≤ t → N.tierDissipation (κ t) (γ t) ≤ -η := fun t ht => by
    have h1 := hmax (hinΛ t ht)
    have h2 := N.tierDissipationWith_le_bandMax (hκ t) (γ t)
    rw [tierDissipationWith_rateConstants] at h2
    simp only [η, neg_neg]
    exact h2.trans h1
  have hpos : ∀ t, 0 ≤ t → (γ t).Positive := fun t ht => hΛpos _ (hinΛ t ht)
  -- `V(γ t) + η t` is antitone
  set W : ℝ → ℝ := fun t => tierEntropy (γ t) + η * t
  have hd : ∀ t, 0 ≤ t → HasDerivAt W (N.tierDissipation (κ t) (γ t) + η * 1) t := fun t ht =>
    (N.tierEntropy_hasDerivAt (κ t) (hpos t ht) fun s => (hasDerivAt_pi.mp (hsol t ht)) s).add
      ((hasDerivAt_id t).const_mul η)
  have hanti : AntitoneOn W (Ici 0) :=
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      (fun t ht => (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht => by rw [interior_Ici] at ht ⊢; exact (hd t (le_of_lt ht)).hasDerivWithinAt)
      (fun t ht => by
        rw [interior_Ici] at ht
        have := hDle t (le_of_lt ht)
        linarith)
  set T := tierEntropy (γ 0) / η + 1
  have hV0 : 1 ≤ tierEntropy (γ 0) := by
    unfold tierEntropy
    linarith [relEntropy_nonneg (fun s => (hpos 0 le_rfl s).le) (fun _ => zero_lt_one)
      (xstar := tierReference S)]
  have hT : 0 ≤ T := by positivity
  have hWT := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hT) hT
  have hVT : 1 ≤ tierEntropy (γ T) := by
    unfold tierEntropy
    linarith [relEntropy_nonneg (fun s => (hpos T hT s).le) (fun _ => zero_lt_one)
      (xstar := tierReference S)]
  simp only [W, mul_zero, add_zero] at hWT
  have hηT : η * T = tierEntropy (γ 0) + η := by
    simp only [T]; field_simp
  linarith


/-- **Permanence of strongly endotactic networks with tempered rates** (Gopalkrishnan–Miller–Shiu
2014, Theorem 1.1). For rates varying in time inside `[ε, ε⁻¹]`, each positive stoichiometric class
contains one compact set `K` such that every forward solution from a positive state of the class is
in `K` from some time on; `K` depends only on the class and `ε`. -/
theorem StronglyEndotacticStd.permanent_varK {N : Network S} (hse : N.StronglyEndotacticStd)
    {ε : ℝ} (hε : 0 < ε) (xref : Concentration S) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → N.RateConstants, N.Tempered ε κ →
      ∀ γ : ℝ → Concentration S, γ 0 ∈ N.positiveCompatibilityClass xref →
        (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) →
        ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → γ t ∈ K := by
  classical
  have htd : N.TierDescending := (N.stronglyEndotacticStd_iff_tierDescending).mp hse
  obtain ⟨K₀, hK₀c, hK₀sub, hK₀neg⟩ := htd.exists_compact_class_region_negative_outside_uniform xref ε
  obtain ⟨R, -, hR⟩ := exists_logBox_of_compact hK₀c fun x hx => (hK₀sub hx).2
  have hRneg : ∀ (k : N.R → ℝ) (x : Concentration S), N.RateVectorInBand ε k →
      x ∈ N.positiveCompatibilityClass xref → x ∉ logBox (S := S) R →
      N.tierDissipationWith k x < 0 := fun k x hk hx hxR =>
    hK₀neg k x hk hx fun hxK => hxR (hR hxK)
  set Υ : Set (Concentration S) := N.compatibilityClass xref ∩ logBox (S := S) (R + 1)
  have hΥc : IsCompact Υ :=
    (isCompact_logBox (S := S) (R + 1)).inter_left (N.isClosed_compatibilityClass xref)
  have hΥpos : Υ ⊆ N.positiveCompatibilityClass xref := fun x hx => ⟨hx.1, logBox_positive hx.2⟩
  obtain ⟨M, hM⟩ := htd.forward_bounded_on_varK ε xref hΥc hΥpos
  set G : (ℝ → N.RateConstants) → (ℝ → Concentration S) → Prop := fun κ δ =>
    N.Tempered ε κ ∧ δ 0 ∈ Υ ∧ ∀ t, 0 ≤ t → HasDerivAt δ (N.massActionVectorField (κ t) (δ t)) t
  obtain ⟨m, hm, hmle⟩ := StronglyEndotacticStd.persistent_uniform_varK hse hε G xref
    (fun κ δ hδ => hδ.1) (fun κ δ hδ => hδ.2.2) (fun κ δ hδ => hδ.2.1.1)
    (g := Real.exp (-(R + 1))) (Real.exp_pos _) (fun κ δ hδ s => (hδ.2.1.2 s).1)
    (M := M) (fun κ δ hδ => hM κ hδ.1 δ hδ.2.1 hδ.2.2)
  refine ⟨N.classInteriorBox xref m M, N.isCompact_classInteriorBox xref m M,
    N.classInteriorBox_subset_positiveCompatibilityClass xref hm, fun κ hκ γ hγ0 hsol => ?_⟩
  -- bounds along this orbit
  obtain ⟨g, hg, hgle⟩ : ∃ g : ℝ, 0 < g ∧ ∀ s, g ≤ γ 0 s := by
    by_cases hS : Nonempty S
    · obtain ⟨s₀, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) (γ 0)
      exact ⟨Finset.univ.inf' Finset.univ_nonempty (γ 0), by rw [h]; exact hγ0.2 s₀,
        fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    · exact ⟨1, one_pos, fun s => absurd ⟨s⟩ hS⟩
  obtain ⟨M₀, hM₀⟩ := htd.forward_bounded_on_varK ε xref (Υ := {γ 0}) isCompact_singleton
    (by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hγ0)
  obtain ⟨m₀, hm₀, hm₀le⟩ := StronglyEndotacticStd.persistent_uniform_varK hse hε
    (fun κ' δ => κ' = κ ∧ δ = γ) xref (fun κ' δ h => h.1 ▸ hκ)
    (fun κ' δ h => by rw [h.1, h.2]; exact hsol) (fun κ' δ h => by rw [h.2]; exact hγ0.1)
    hg (fun κ' δ h => by rw [h.2]; exact hgle) (M := M₀)
    (fun κ' δ h => by rw [h.2]; exact hM₀ κ hκ γ rfl hsol)
  obtain ⟨t₀, ht₀, hbox⟩ := exists_entry_logBox_varK hε xref hRneg hκ hγ0.1 hsol hm₀
    (M := M₀) fun t ht s => ⟨hm₀le κ γ ⟨rfl, rfl⟩ t ht s, hM₀ κ hκ γ rfl hsol t ht s⟩
  have hcls : ∀ t, 0 ≤ t → N.StoichCompatible xref (γ t) := fun t ht =>
    hγ0.1.trans (N.sub_mem_stoichSubspace_of_solution_varK κ ht fun τ hτ => hsol τ hτ.1)
  -- the shifted orbit starts in `Υ`
  set κs : ℝ → N.RateConstants := fun t => κ (t₀ + t)
  set δ : ℝ → Concentration S := fun t => γ (t₀ + t)
  have hδ : G κs δ := by
    refine ⟨fun t => hκ (t₀ + t), ⟨by simpa [δ] using (mem_compatibilityClass.mpr (hcls t₀ ht₀)),
      by simpa [δ] using hbox⟩, fun t ht => ?_⟩
    have h := hsol (t₀ + t) (by linarith)
    have hshift : HasDerivAt (fun τ : ℝ => t₀ + τ) 1 t := (hasDerivAt_id t).const_add t₀
    have := h.scomp t hshift
    simpa [δ, κs, Function.comp_def] using this
  refine ⟨t₀, ht₀, fun t ht => ⟨hcls t (ht₀.trans ht), fun s => ?_⟩⟩
  have heq : γ t = δ (t - t₀) := by simp [δ]
  rw [heq]
  exact ⟨hmle κs δ hδ (t - t₀) (by linarith) s, hM κs hδ.1 δ hδ.2.1 hδ.2.2 (t - t₀) (by linarith) s⟩

/-- **Persistence of strongly endotactic networks with tempered rates.** -/
theorem StronglyEndotacticStd.persistent_varK {N : Network S} (hse : N.StronglyEndotacticStd)
    {ε : ℝ} (hε : 0 < ε) {κ : ℝ → N.RateConstants} (hκ : N.Tempered ε κ)
    {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → ∀ s, m ≤ γ t s := by
  classical
  have htd : N.TierDescending := (N.stronglyEndotacticStd_iff_tierDescending).mp hse
  obtain ⟨g, hg, hgle⟩ : ∃ g : ℝ, 0 < g ∧ ∀ s, g ≤ γ 0 s := by
    by_cases hS : Nonempty S
    · obtain ⟨s₀, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) (γ 0)
      exact ⟨Finset.univ.inf' Finset.univ_nonempty (γ 0), by rw [h]; exact hγ0 s₀,
        fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    · exact ⟨1, one_pos, fun s => absurd ⟨s⟩ hS⟩
  have hγcls : γ 0 ∈ N.positiveCompatibilityClass (γ 0) := ⟨StoichCompatible.refl _ _, hγ0⟩
  obtain ⟨M₀, hM₀⟩ := htd.forward_bounded_on_varK ε (γ 0) (Υ := {γ 0}) isCompact_singleton
    (by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hγcls)
  obtain ⟨m, hm, hmle⟩ := StronglyEndotacticStd.persistent_uniform_varK hse hε
    (fun κ' δ => κ' = κ ∧ δ = γ) (γ 0) (fun κ' δ h => h.1 ▸ hκ)
    (fun κ' δ h => by rw [h.1, h.2]; exact hsol)
    (fun κ' δ h => by rw [h.2, sub_self]; exact Submodule.zero_mem _)
    hg (fun κ' δ h => by rw [h.2]; exact hgle) (M := M₀)
    (fun κ' δ h => by rw [h.2]; exact hM₀ κ hκ γ rfl hsol)
  exact ⟨m, hm, hmle κ γ ⟨rfl, rfl⟩⟩

end Network
end CRNT
