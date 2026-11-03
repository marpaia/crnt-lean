import CRNT.Dynamics.TierUniformNegativity
import CRNT.Dynamics.TierFixedRateRegion
import CRNT.Kinetics.SpeciesProjectionMassAction
import CRNT.Theorems.DeficiencyZero.AsymptoticStability
import CRNT.Dynamics.SingleLinkageStructure
import CRNT.Dynamics.GenuineConfinement

/-!
# Persistence of strongly endotactic mass-action systems

`StronglyEndotacticStd.persistent`: for a strongly endotactic network and any positive rate
constants, every positive forward solution stays a positive distance away from the boundary of
the orthant (Gopalkrishnan–Miller–Shiu 2014; the tier route of Anderson–Cappelletti–Kim–Nguyen
2020, §5).

The argument is an induction on the set `P` of species that might become small, from large `P` to
small. `Q(P)`: some coordinate in `P` stays above a positive constant. Assuming `Q(P')` for every
`P' ⊋ P`, whenever all `P`-coordinates are below `m'` the other coordinates are at least `m'`. The
`P`-coordinates then follow the projected network `speciesProjection N P` (strongly endotactic) with
rates `κ_r ∏_{s ∉ P} x_s^{y_{r,s}}` in a fixed band, so by the variable-rate compact region
(`exists_compact_class_region_negative_outside_uniform`) the projected tier entropy decreases while
all `P`-coordinates are below `ρ`. The entropy `1 + ∑_{s ∈ P} u(x_s)`, `u(x) = x log x − x + 1`, is
largest at the origin; an orbit segment inside the cube `[0, ρ)^P` starts on its boundary, where the
entropy is at most `|P| + u(ρ)`, so it never reaches the smaller cube `[0, ρ')^P`, where the entropy
exceeds `1 + |P| u(ρ') > |P| + u(ρ)`.
-/

open Filter Set
open scoped BigOperators Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The effective rates of the projected network at the state `x`. -/
noncomputable def projRates (N : Network S) (P : Finset S) (κ : N.RateConstants)
    (x : Concentration S) : N.R → ℝ :=
  fun r => κ.k r * omittedMonomial P x (N.reaction r).source

/-- The projected tier entropy decreases at the rate given by the projected dissipation. -/
theorem projected_tierEntropy_hasDerivAt (N : Network S) (P : Finset S) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} {t : ℝ} (hpos : (γ t).Positive)
    (hsol : HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    HasDerivAt (fun τ => tierEntropy (projectConcentration P (γ τ)))
      ((N.speciesProjection P).tierDissipationWith (N.projRates P κ (γ t))
        (projectConcentration P (γ t))) t := by
  set NP := N.speciesProjection P
  have hk : ∀ r, 0 < N.projRates P κ (γ t) r := fun r =>
    mul_pos (κ.positive r) (Finset.prod_pos fun s _ => pow_pos (hpos s) _)
  let κV : NP.VariableRateConstants := ⟨fun _ r => N.projRates P κ (γ t) r, fun _ r => hk r⟩
  have hposP : (projectConcentration P (γ t)).Positive := fun s => hpos s.1
  have hfield : ∀ s : {s // s ∈ P}, NP.variableMassActionVectorField κV t
      (projectConcentration P (γ t)) s = N.massActionVectorField κ (γ t) s.1 := by
    intro s
    rw [variableMassActionVectorField_apply, massActionVectorField_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    change N.R at r
    simp only [variableMassActionRate, massActionRate]
    rw [speciesProjection_reactionVector_apply,
      ← massActionMonomial_project_mul_omitted P (γ t) (N.reaction r).source]
    show κ.k r * omittedMonomial P (γ t) (N.reaction r).source *
        (projectComplex P (N.reaction r).source).massActionMonomial (projectConcentration P (γ t)) *
          N.reactionVector r s.1 =
      κ.k r * ((projectComplex P (N.reaction r).source).massActionMonomial
        (projectConcentration P (γ t)) * omittedMonomial P (γ t) (N.reaction r).source) *
          N.reactionVector r s.1
    ring
  have hsolP : ∀ s : {s // s ∈ P}, HasDerivAt (fun τ => projectConcentration P (γ τ) s)
      (NP.variableMassActionVectorField κV t (projectConcentration P (γ t)) s) t := by
    intro s
    rw [hfield s]
    exact (hasDerivAt_pi.mp hsol) s.1
  exact NP.tierEntropy_hasDerivAt_variable κV (γ := fun τ => projectConcentration P (γ τ))
    hposP hsolP

/-- Bounds on the omitted coordinates put the projected rates in a band. -/
theorem exists_band_projRates (N : Network S) (P : Finset S) (κ : N.RateConstants) {m M : ℝ}
    (hm : 0 < m) (hM : 0 < M) :
    ∃ δ : ℝ, ∀ x : Concentration S, (∀ s ∉ P, m ≤ x s ∧ x s ≤ M) →
      (N.speciesProjection P).RateVectorInBand δ (N.projRates P κ x) := by
  classical
  -- lower and upper endpoints for each reaction
  let lo : N.R → ℝ := fun r => κ.k r * ∏ s ∈ Pᶜ, m ^ (N.reaction r).source s
  let hi : N.R → ℝ := fun r => κ.k r * ∏ s ∈ Pᶜ, M ^ (N.reaction r).source s
  have hlo : ∀ r, 0 < lo r := fun r => mul_pos (κ.positive r) (Finset.prod_pos fun s _ => pow_pos hm _)
  have hhi : ∀ r, 0 < hi r := fun r => mul_pos (κ.positive r) (Finset.prod_pos fun s _ => pow_pos hM _)
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
  refine ⟨δ, fun x hx => ⟨hδ, fun r => ⟨?_, ?_⟩⟩⟩
  · refine (hδlo r).trans ?_
    change lo r ≤ κ.k r * omittedMonomial P x (N.reaction r).source
    unfold omittedMonomial
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀ (fun s _ => pow_nonneg hm.le _)
      (fun s hs => pow_le_pow_left₀ hm.le (hx s (Finset.mem_compl.mp hs)).1 _)) (κ.positive r).le
  · refine le_trans ?_ (hδhi r)
    change κ.k r * omittedMonomial P x (N.reaction r).source ≤ hi r
    unfold omittedMonomial
    refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod₀
      (fun s hs => pow_nonneg (hm.le.trans (hx s (Finset.mem_compl.mp hs)).1) _)
      (fun s hs => pow_le_pow_left₀ (hm.le.trans (hx s (Finset.mem_compl.mp hs)).1)
        (hx s (Finset.mem_compl.mp hs)).2 _)) (κ.positive r).le

/-- Projections of states in one stoichiometric class lie in one class of the projection. -/
theorem projectConcentration_sub_mem (N : Network S) (P : Finset S) {x x' : Concentration S}
    (h : x - x' ∈ N.stoichSubspace) :
    projectConcentration P x - projectConcentration P x' ∈ (N.speciesProjection P).stoichSubspace := by
  let π : (S → ℝ) →ₗ[ℝ] ({s // s ∈ P} → ℝ) :=
    { toFun := fun v s => v s.1, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hmap : N.stoichSubspace.map π ≤ (N.speciesProjection P).stoichSubspace := by
    unfold stoichSubspace
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨v, ⟨r, rfl⟩, rfl⟩
    apply Submodule.subset_span
    refine ⟨r, ?_⟩
    funext s
    simp [π, speciesProjection_reactionVector_apply]
  have := hmap (Submodule.mem_map_of_mem (f := π) h)
  convert this using 1
  funext s
  simp [π, projectConcentration]

/-! ## The entropy profile `u(x) = x log x − x + 1` -/

/-- One coordinate of the tier entropy. -/
noncomputable def entU (x : ℝ) : ℝ := x * Real.log x - x + 1

theorem tierEntropy_eq_entU {T : Type} [Fintype T] (x : T → ℝ) :
    tierEntropy x = 1 + ∑ s, entU (x s) := by
  simp [tierEntropy, relEntropy, tierReference, entU]

theorem entU_le_one {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : entU x ≤ 1 := by
  have := Real.mul_log_nonpos h0 h1
  unfold entU; linarith

theorem entU_lt_one {x : ℝ} (h0 : 0 < x) (h1 : x ≤ 1) : entU x < 1 := by
  have := Real.mul_log_nonpos h0.le h1
  unfold entU; linarith

theorem continuous_entU : Continuous entU := by
  unfold entU
  exact (Real.continuous_mul_log.sub continuous_id).add continuous_const

theorem entU_antitoneOn : AntitoneOn entU (Icc 0 1) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) continuous_entU.continuousOn
    (f' := Real.log) (fun x hx => ?_) (fun x hx => ?_)
  · rw [interior_Icc] at hx
    have h := ((Real.hasDerivAt_mul_log hx.1.ne').sub (hasDerivAt_id x)).add_const 1
    have h' : HasDerivAt entU (Real.log x) x := by
      have he : entU = fun x => x * Real.log x - id x + 1 := by funext y; simp [entU]
      rw [he]
      convert h using 1
      ring
    exact h'.hasDerivWithinAt
  · rw [interior_Icc] at hx
    exact (Real.log_neg hx.1 hx.2).le

theorem entU_zero : entU 0 = 1 := by simp [entU]

/-- Small arguments make `u` close to `1`. -/
theorem exists_small_entU {ρ : ℝ} (hρ : 0 < ρ) {c : ℝ} (hc : c < 1) :
    ∃ ρ', 0 < ρ' ∧ ρ' ≤ ρ ∧ c < entU ρ' := by
  have hlim : Tendsto entU (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have := continuous_entU.continuousAt (x := 0)
    rw [ContinuousAt, entU_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ x in 𝓝[>] (0 : ℝ), c < entU x := hlim.eventually (lt_mem_nhds hc)
  have hev2 : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioc 0 ρ := Ioc_mem_nhdsGT hρ
  obtain ⟨x, hx1, hx2⟩ := (hev.and hev2).exists
  exact ⟨x, hx2.1, hx2.2, hx1⟩

/-! ## The induction step -/

/-- `Q(P)` for a family `G` of solutions: some coordinate in `P` stays above one positive
constant along every member. -/
def KeepsSomeAbove (G : (ℝ → Concentration S) → Prop) (P : Finset S) : Prop :=
  ∃ m : ℝ, 0 < m ∧ ∀ γ, G γ → ∀ t, 0 ≤ t → ∃ s ∈ P, m ≤ γ t s

/-- The induction step, uniformly over a family of solutions in one stoichiometric class whose
initial coordinates are at least `g` and whose values stay below `M`. -/
theorem persistent_step {N : Network S} (hse : N.StronglyEndotacticStd) (κ : N.RateConstants)
    (G : (ℝ → Concentration S) → Prop) (xref : Concentration S)
    (hsolG : ∀ γ, G γ → ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hclass : ∀ γ, G γ → γ 0 - xref ∈ N.stoichSubspace)
    {g : ℝ} (hg : 0 < g) (hg0le : ∀ γ, G γ → ∀ s, g ≤ γ 0 s)
    {M : ℝ} (hM1 : 1 ≤ M) (hMG : ∀ γ, G γ → ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M)
    {P : Finset S} (hP : P.Nonempty)
    (IH : ∀ s, s ∉ P → KeepsSomeAbove G (insert s P)) : KeepsSomeAbove G P := by
  classical
  -- the floor `m'` for the omitted coordinates
  choose! mfun hmpos hmQ using IH
  obtain ⟨m', hm'pos, hm'le⟩ : ∃ m' : ℝ, 0 < m' ∧ ∀ s, s ∉ P → m' ≤ mfun s := by
    by_cases hc : Pᶜ.Nonempty
    · refine ⟨Pᶜ.inf' hc mfun, ?_, fun s hs => Finset.inf'_le _ (Finset.mem_compl.mpr hs)⟩
      obtain ⟨s, hs, heq⟩ := Finset.exists_mem_eq_inf' hc mfun
      rw [heq]; exact hmpos s (Finset.mem_compl.mp hs)
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, Finset.mem_compl.mpr hs⟩ hc⟩
  have fact1 : ∀ γ, G γ → ∀ t, 0 ≤ t → (∀ s ∈ P, γ t s < m') → ∀ s, s ∉ P → m' ≤ γ t s := by
    intro γ hγ t ht hsmall s hs
    obtain ⟨s', hs', hle⟩ := hmQ s hs γ hγ t ht
    rcases Finset.mem_insert.mp hs' with rfl | hs'P
    · exact (hm'le s' hs).trans hle
    · exact absurd (lt_of_lt_of_le (hsmall s' hs'P) (hm'le s hs)) (not_lt.mpr hle)
  -- the projected network and its compact region
  set NP := N.speciesProjection P
  have htdP : NP.TierDescending :=
    (NP.stronglyEndotacticStd_iff_tierDescending).mp (StronglyEndotacticStd.speciesProjection hse P)
  obtain ⟨δ, hδ⟩ := N.exists_band_projRates P κ hm'pos (zero_lt_one.trans_le hM1)
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
  have hρg : ∀ γ, G γ → ∀ s, ρ ≤ γ 0 s := fun γ hγ s =>
    ((min_le_right _ _).trans (min_le_right _ _)).trans (hg0le γ hγ s)
  set n : ℝ := (P.card : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr hP.card_pos
  have hcard : (Finset.univ : Finset {s // s ∈ P}).card = P.card := by simp
  obtain ⟨ρ', hρ'pos, hρ'le, hρ'u⟩ := exists_small_entU hρpos
    (c := (n - 1 + entU ρ) / n) (by
      rw [div_lt_one hn]; linarith [entU_lt_one hρpos hρ1])
  have hkey : n + entU ρ < 1 + n * entU ρ' := by
    have := (div_lt_iff₀ hn).mp hρ'u
    linarith
  refine ⟨ρ', hρ'pos, fun γ hγ t₁ ht₁ => ?_⟩
  by_contra hnot
  push Not at hnot
  have hsol := hsolG γ hγ
  have hpos : ∀ t, 0 ≤ t → (γ t).Positive :=
    N.genuineOrbit_pos κ (fun s => hg.trans_le (hg0le γ hγ s)) hsol
  have hM := hMG γ hγ
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
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_rfl, ht₁⟩, hP.choose, hP.choose_spec, hρg γ hγ _⟩
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
    NP.tierDissipationWith (N.projRates P κ (γ t)) (projectConcentration P (γ t))
  have hD : ∀ t ∈ Ioo t₀ t₁, HasDerivAt V (D t) t ∧ D t < 0 := by
    intro t ht
    have ht0 : 0 ≤ t := ht₀0.trans ht.1.le
    refine ⟨N.projected_tierEntropy_hasDerivAt P κ (hpos t ht0) (hsol t ht0), ?_⟩
    have hsm := hsmall t ht.1 ht.2.le
    have hband := hδ (γ t) fun s hs =>
      ⟨fact1 γ hγ t ht0 (fun s' hs' => (hsm s' hs').trans_le hρm') s hs, hM t ht0 s⟩
    have hclassP : projectConcentration P (γ t) ∈ NP.positiveCompatibilityClass xrefP := by
      refine ⟨?_, fun s => hpos t ht0 s.1⟩
      have h1 := N.sub_mem_stoichSubspace_of_solution κ ht0 fun τ hτ => hsol τ hτ.1
      have h2 : γ t - xref ∈ N.stoichSubspace := by
        have := Submodule.add_mem _ h1 (hclass γ hγ)
        simpa [sub_add_sub_cancel] using this
      exact N.projectConcentration_sub_mem P h2
    have hnotK : projectConcentration P (γ t) ∉ K := by
      intro hK
      have h1 := hcK _ hK s₁
      have h2 := hsm s₁.1 s₁.2
      simp only [projectConcentration_apply] at h1
      linarith
    exact hKneg _ _ hband hclassP hnotK
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

/-- **Uniform persistence.** For a strongly endotactic network, positive rate constants, and a
family of forward solutions in one stoichiometric class whose initial coordinates are at least
`g > 0` and whose values stay below `M`, one positive constant bounds every coordinate of every
member from below. -/
theorem StronglyEndotacticStd.persistent_uniform {N : Network S} (hse : N.StronglyEndotacticStd)
    (κ : N.RateConstants) (G : (ℝ → Concentration S) → Prop) (xref : Concentration S)
    (hsolG : ∀ γ, G γ → ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    (hclass : ∀ γ, G γ → γ 0 - xref ∈ N.stoichSubspace)
    {g : ℝ} (hg : 0 < g) (hg0le : ∀ γ, G γ → ∀ s, g ≤ γ 0 s)
    {M : ℝ} (hMG : ∀ γ, G γ → ∀ t, 0 ≤ t → ∀ s, γ t s ≤ M) :
    ∃ m : ℝ, 0 < m ∧ ∀ γ, G γ → ∀ t, 0 ≤ t → ∀ s, m ≤ γ t s := by
  classical
  have hM' : ∀ γ, G γ → ∀ t, 0 ≤ t → ∀ s, γ t s ≤ max M 1 := fun γ hγ t ht s =>
    (hMG γ hγ t ht s).trans (le_max_left _ _)
  have hkey : ∀ k : ℕ, ∀ P : Finset S, Pᶜ.card = k → P.Nonempty → KeepsSomeAbove G P := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro P hk hP
      refine persistent_step hse κ G xref hsolG hclass hg hg0le (le_max_right _ _) hM' hP
        fun s hs => ?_
      have hlt : (insert s P)ᶜ.card < k := by
        rw [Finset.compl_insert, Finset.card_erase_of_mem (Finset.mem_compl.mpr hs), ← hk]
        exact Nat.sub_lt (Finset.card_pos.mpr ⟨s, Finset.mem_compl.mpr hs⟩) one_pos
      exact ih _ hlt (insert s P) rfl (Finset.insert_nonempty s P)
  have hsingle : ∀ s : S, ∃ m : ℝ, 0 < m ∧ ∀ γ, G γ → ∀ t, 0 ≤ t → m ≤ γ t s := by
    intro s
    obtain ⟨m, hm, h⟩ := hkey _ {s} rfl (Finset.singleton_nonempty s)
    refine ⟨m, hm, fun γ hγ t ht => ?_⟩
    obtain ⟨s', hs', hle⟩ := h γ hγ t ht
    rw [Finset.mem_singleton.mp hs'] at hle
    exact hle
  choose mfun hmpos hmle using hsingle
  by_cases hS : Nonempty S
  · obtain ⟨s₀, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) mfun
    refine ⟨Finset.univ.inf' Finset.univ_nonempty mfun, by rw [h]; exact hmpos s₀,
      fun γ hγ t ht s => (Finset.inf'_le _ (Finset.mem_univ s)).trans (hmle s γ hγ t ht)⟩
  · exact ⟨1, one_pos, fun _ _ t _ s => absurd ⟨s⟩ hS⟩

/-- **Persistence of strongly endotactic mass-action systems** (Gopalkrishnan–Miller–Shiu 2014,
Theorem 8.5; Anderson–Cappelletti–Kim–Nguyen 2020, Theorem 5.4). Every forward solution from a
positive initial state of a strongly endotactic network with positive rate constants is bounded
below by a positive constant in every coordinate. -/
theorem StronglyEndotacticStd.persistent {N : Network S} (hse : N.StronglyEndotacticStd)
    (κ : N.RateConstants) {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → ∀ s, m ≤ γ t s := by
  classical
  obtain ⟨M, hM⟩ := StronglyEndotacticStd.forward_bounded hse κ hγ0 hsol
  obtain ⟨g, hg, hgle⟩ : ∃ g : ℝ, 0 < g ∧ ∀ s, g ≤ γ 0 s := by
    by_cases hS : Nonempty S
    · obtain ⟨s₀, -, h⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := S)) (γ 0)
      exact ⟨Finset.univ.inf' Finset.univ_nonempty (γ 0), by rw [h]; exact hγ0 s₀,
        fun s => Finset.inf'_le _ (Finset.mem_univ s)⟩
    · exact ⟨1, one_pos, fun s => absurd ⟨s⟩ hS⟩
  obtain ⟨m, hm, h⟩ := StronglyEndotacticStd.persistent_uniform hse κ (fun δ => δ = γ) (γ 0)
    (fun δ hδ => hδ ▸ hsol) (fun δ hδ => by rw [hδ, sub_self]; exact Submodule.zero_mem _)
    hg (fun δ hδ => hδ ▸ hgle) (M := M) (fun δ hδ => hδ ▸ hM)
  exact ⟨m, hm, h γ rfl⟩

/-- **Weakly reversible networks with one linkage class are persistent** (Anderson 2011): they are
strongly endotactic (Gopalkrishnan–Miller–Shiu, Corollary 3.20). -/
theorem WeaklyReversible.persistent_of_singleLinkageClass {N : Network S}
    (hwr : N.WeaklyReversible) (hslc : N.SingleLinkageClass) (κ : N.RateConstants)
    {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) :
    ∃ m : ℝ, 0 < m ∧ ∀ t, 0 ≤ t → ∀ s, m ≤ γ t s :=
  StronglyEndotacticStd.persistent (hwr.stronglyEndotacticStd_of_singleLinkageClass hslc) κ hγ0 hsol

end Network
end CRNT
