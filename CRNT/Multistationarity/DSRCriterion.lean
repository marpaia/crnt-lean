import CRNT.Multistationarity.BCFullyOpen
import CRNT.Multistationarity.ConcordanceConverse

/-!
# The DSR-graph criterion (Banaji–Craciun 2009)

The DSR graph of Banaji and Craciun refines the species–reaction graph by orienting it: an edge
from a species to a reaction is present only when the species affects the rate, i.e. is a reactant
of (some direction of) the reaction; edges from reactions to the species they change are always
present.  A cycle of the DSR graph is a cycle of the true-SR graph traversed so that every
species-to-reaction step enters a reaction in which the species is a reactant
(`TrueSRCycle.Oriented`).

**DSR condition (`DSRCriterion`).**  Every even oriented cycle is an s-cycle, and no two even
oriented cycles have an S-to-R intersection.  It only constrains oriented cycles, so it is implied
by the true-SR criterion (`TrueSRStrongCriterion.dsrCriterion`).

**Theorem (`concordant_fullyOpen_of_dsrCriterion`).**  Under reactant/product separation, with
flows that are single-species in- and outflows, the DSR condition makes the fully open extension
concordant; hence every weakly monotonic kinetics on it (rates depending only on reactant
concentrations) is injective (`injective_fullyOpen_of_dsrCriterion`), so the fully open system has at
most one positive steady state.

Proof: the Banaji–Craciun determinant argument of `BCFullyOpen`, run for a discordance witness
instead of a strong-discordance witness.  A discordance witness has its sign matches on reactant
species only, so the weights `w r t` of the product `A · (w ∘ Aᵀ)` vanish unless `t` is a reactant of
`r`.  In the column expansion, only column choices `f` with every `f t = r` a reactant channel of
`t` carry a nonzero weight, and for those the cycles of the normalized minor are oriented; the
DSR condition then gives a nonnegative coefficient exactly as the true-SR condition does.

Nothing here is an axiom or a `sorry`.
-/

open Finset Matrix Equiv

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A true-SR cycle is **oriented** (a cycle of the DSR graph) when every species enters the next
reaction of the cycle through a complex that is the source of some channel of that reaction. -/
def TrueSRCycle.Oriented {N : Network S} {n : ℕ} (C : N.TrueSRCycle n) : Prop :=
  ∀ i, ∃ r : N.R, N.trueReaction r = C.reaction i ∧ (C.leftEdge i).endpoint = (N.reaction r).source

/-- **The DSR condition** (Banaji–Craciun condition `(*)` on the DSR graph). -/
def DSRCriterion (N : Network S) : Prop :=
  (∀ {n : ℕ} (C : N.TrueSRCycle n), C.Oriented → C.Even → C.SCycle) ∧
  (∀ {m n : ℕ} (C : N.TrueSRCycle m) (D : N.TrueSRCycle n), C.Oriented → D.Oriented →
    C.Even → D.Even → ¬ Nonempty (C.SToRIntersection D))

/-- The true-SR criterion implies the DSR condition. -/
theorem TrueSRStrongCriterion.dsrCriterion {N : Network S} (h : N.TrueSRStrongCriterion) :
    N.DSRCriterion :=
  ⟨fun C _ he => h.1 C he, fun C D _ _ hC hD => h.2 C D hC hD⟩

/-- The cycle of a permutation is oriented when every channel has its species as a reactant. -/
theorem CycleChannels.toCycle_oriented {N : Network S} {c : Perm S} {ch : S → N.R}
    (h : N.CycleChannels c ch) {x₀ : S} (hx₀ : x₀ ∈ c.support)
    (hsrc : ∀ y ∈ c.support, (N.reaction (ch y)).source y ≠ 0) :
    (h.toCycle x₀ hx₀).Oriented := by
  intro j
  refine ⟨ch (h.sp x₀ j), rfl, ?_⟩
  show N.bcEndpoint (ch (h.sp x₀ j)) (h.sp x₀ j) = _
  unfold bcEndpoint
  rw [if_pos (hsrc _ (h.sp_mem hx₀ j))]

/-- Column expansion with nonnegativity only on the column choices of nonzero weight. -/
theorem DetCycle.det_mul_pos_of_coeff_nonneg_on {K : Type*} [Fintype K] [DecidableEq K]
    (A : Matrix S K ℝ) (w : K → S → ℝ) (hw : ∀ k t, 0 ≤ w k t)
    (hcoef : ∀ f : S → K, (∏ t, w (f t) t) ≠ 0 → 0 ≤ (∏ t, A t (f t)) * (A.submatrix id f).det)
    (f₀ : S → K)
    (hf₀ : 0 < (∏ t, w (f₀ t) t) * ((∏ t, A t (f₀ t)) * (A.submatrix id f₀).det)) :
    0 < (A * Matrix.of (fun k t => w k t * A t k)).det := by
  rw [DetCycle.det_mul_eq_sum_columns]
  have hterm : ∀ f : S → K, (∏ t, (Matrix.of (fun k t => w k t * A t k)) (f t) t) *
      (A.submatrix id f).det =
      (∏ t, w (f t) t) * ((∏ t, A t (f t)) * (A.submatrix id f).det) := by
    intro f
    simp only [Matrix.of_apply, Finset.prod_mul_distrib]
    ring
  simp_rw [hterm]
  have hnn : ∀ f ∈ (Finset.univ : Finset (S → K)),
      0 ≤ (∏ t, w (f t) t) * ((∏ t, A t (f t)) * (A.submatrix id f).det) := by
    intro f _
    by_cases h0 : (∏ t, w (f t) t) = 0
    · rw [h0, zero_mul]
    · exact mul_nonneg (Finset.prod_nonneg fun t _ => hw _ _) (hcoef f h0)
  exact lt_of_lt_of_le hf₀
    (Finset.single_le_sum (f := fun f : S → K =>
      (∏ t, w (f t) t) * ((∏ t, A t (f t)) * (A.submatrix id f).det)) hnn
      (Finset.mem_univ f₀))

section Minor

variable (N : Network S) (f : S → N.R ⊕ S) [Nonempty N.R]

/-- **The normalized minor has nonnegative determinant under the DSR condition**, for column
choices whose channels have their species as reactants. -/
theorem det_bcH_nonneg_dsr (hsep : N.ReactantProductSeparated) (hflow : N.FlowsAreSingletons)
    (hDSR : N.DSRCriterion) (hz : ∀ t, N.bcG f t t ≠ 0)
    (hcol : ∀ a b, a ≠ b → ∀ r q, f a = Sum.inl r → f b = Sum.inl q →
      ¬ N.SameTrueReaction r q)
    (hreact : ∀ t r, f t = Sum.inl r → (N.reaction r).source t ≠ 0) :
    0 ≤ (N.bcH f).det := by
  classical
  have hsrc : ∀ {c : Perm S}, (∀ y ∈ c.support, f y = Sum.inl (N.bcCh f y)) →
      ∀ y ∈ c.support, (N.reaction (N.bcCh f y)).source y ≠ 0 :=
    fun hinl y hy => hreact y _ (hinl y hy)
  apply DetCycle.det_nonneg_of_negCycles _ (N.bcH_diag f hz)
  · intro c hc hneg
    obtain ⟨hch, hinl, hweq⟩ :=
      N.cycleChannels_of_weight_ne f hflow hz hcol hc (ne_of_lt hneg)
    obtain ⟨x₀, hx₀⟩ : ∃ x, x ∈ c.support := hc.nonempty_support
    rw [hweq] at hneg ⊢
    have heven := hch.even_of_weight_neg hsep hx₀ hneg
    exact hch.weight_eq_neg_one_of_sCycle hsep hx₀ heven
      (hDSR.1 _ (hch.toCycle_oriented hx₀ (hsrc hinl)) heven)
  · intro c d hc hd hcneg hdneg hne
    by_contra hdisj
    obtain ⟨x, hxc, hxd⟩ : ∃ x, c x ≠ x ∧ d x ≠ x := by
      unfold Perm.Disjoint at hdisj
      push Not at hdisj
      exact hdisj
    obtain ⟨hcc, hcinl, hcw⟩ :=
      N.cycleChannels_of_weight_ne f hflow hz hcol hc (ne_of_lt hcneg)
    obtain ⟨hdc, hdinl, hdw⟩ :=
      N.cycleChannels_of_weight_ne f hflow hz hcol hd (ne_of_lt hdneg)
    have hxc' : x ∈ c.support := Perm.mem_support.mpr hxc
    have hxd' : x ∈ d.support := Perm.mem_support.mpr hxd
    have P : N.CyclePair c d (N.bcCh f) := by
      refine ⟨hcc, hdc, ?_, hne⟩
      intro y hy y' hy' hcls
      by_contra hyy
      exact hcol y y' hyy _ _ (hcinl y hy) (hdinl y' hy') (Quotient.exact hcls)
    rw [hcw] at hcneg
    rw [hdw] at hdneg
    have hCe := hcc.even_of_weight_neg hsep hxc' hcneg
    have hDe := hdc.even_of_weight_neg hsep hxd' hdneg
    exact hDSR.2 _ _ (hcc.toCycle_oriented hxc' (hsrc hcinl))
      (hdc.toCycle_oriented hxd' (hsrc hdinl)) hCe hDe
      ⟨P.sToRIntersection hxc' hxd' ⟨x, hxc', hxd'⟩⟩

end Minor

/-- **The coefficients of reactant column choices are nonnegative under the DSR condition.** -/
theorem bc_coeff_nonneg_dsr (N : Network S) (hsep : N.ReactantProductSeparated)
    (hflow : N.FlowsAreSingletons) (hDSR : N.DSRCriterion) (f : S → N.R ⊕ S)
    (hreact : ∀ t r, f t = Sum.inl r → (N.reaction r).source t ≠ 0) :
    0 ≤ (∏ t, N.bcMatrix t (f t)) * (N.bcMatrix.submatrix id f).det := by
  classical
  change 0 ≤ (∏ t, N.bcG f t t) * (N.bcG f).det
  by_cases hz : ∃ t, N.bcG f t t = 0
  · obtain ⟨t, ht⟩ := hz
    rw [Finset.prod_eq_zero (f := fun u => N.bcG f u u) (Finset.mem_univ t) ht, zero_mul]
  push Not at hz
  by_cases hcolex : ∃ a b, a ≠ b ∧ ∃ r q, f a = Sum.inl r ∧ f b = Sum.inl q ∧
      N.SameTrueReaction r q
  · obtain ⟨a, b, hab, r, q, ha, hb, hrq⟩ := hcolex
    rw [N.det_bcG_eq_zero_of_sameClass f hab ha hb hrq, mul_zero]
  push Not at hcolex
  have hcol : ∀ a b, a ≠ b → ∀ r q, f a = Sum.inl r → f b = Sum.inl q →
      ¬ N.SameTrueReaction r q := fun a b hab r q ha hb => hcolex a b hab r q ha hb
  rcases isEmpty_or_nonempty N.R with hR | hR
  · have hf : ∀ t, f t = Sum.inr t := by
      intro t
      cases h : f t with
      | inl r => exact (hR.false r).elim
      | inr u =>
        have h1 := hz t
        rw [bcG_apply, h, bcMatrix_inr] at h1
        split_ifs at h1 with hu
        · rw [hu]
        · exact absurd rfl h1
    have hG : N.bcG f = 1 := by
      ext s t
      simp [bcG_apply, hf, Matrix.one_apply]
    rw [hG, Matrix.det_one, mul_one]
    exact Finset.prod_nonneg fun t _ => by simp
  · have hdet : (N.bcG f).det = (N.bcH f).det * ∏ t, N.bcG f t t := by
      conv_lhs => rw [N.bcG_eq_mul f hz]
      rw [Matrix.det_mul, Matrix.det_diagonal]
    rw [hdet]
    have hH := N.det_bcH_nonneg_dsr f hsep hflow hDSR hz hcol hreact
    have : (∏ t, N.bcG f t t) * ((N.bcH f).det * ∏ t, N.bcG f t t) =
        ((∏ t, N.bcG f t t) ^ 2) * (N.bcH f).det := by ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) hH

/-! ## From a discordance witness of the fully open network to a singular product -/

section Witness

variable {N : Network S} {α : N.fullyOpen.R → ℝ} {σ : S → ℝ}

theorem outflow_sign_c (W : N.fullyOpen.ConcordanceWitness α σ) (s : S) :
    (α (Sum.inr (Sum.inr s)) ≠ 0 → SignType.sign (σ s) = SignType.sign (α (Sum.inr (Sum.inr s))))
      ∧ (α (Sum.inr (Sum.inr s)) = 0 → σ s = 0) := by
  have hsrc : ∀ t, (N.fullyOpen.reaction (Sum.inr (Sum.inr s))).source t ≠ 0 → t = s := by
    intro t ht
    simp only [fullyOpen_reaction_outflow, outflowReaction, singletonComplex_apply] at ht
    by_contra h
    simp [Pi.single_apply, h] at ht
  have hss : (N.fullyOpen.reaction (Sum.inr (Sum.inr s))).source s ≠ 0 := by
    simp [outflowReaction, singletonComplex_apply]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨t, ht, hsg⟩ := W.sign_match _ h
    have := hsrc t ht
    subst this
    exact hsg
  · rcases W.sign_balance _ h with h0 | ⟨t, t', ht, ht', hlt, hgt⟩
    · exact h0 s hss
    · have h1 := hsrc t ht
      have h2 := hsrc t' ht'
      subst h1; subst h2
      exact absurd (lt_trans hlt hgt) (lt_irrefl _)

theorem inflow_zero_c (W : N.fullyOpen.ConcordanceWitness α σ) (s : S) :
    α (Sum.inr (Sum.inl s)) = 0 := by
  by_contra h
  obtain ⟨t, ht, -⟩ := W.sign_match _ h
  simp [inflowReaction, Complex.zero_apply] at ht

theorem netOut_spec_c (W : N.fullyOpen.ConcordanceWitness α σ) (s : S) :
    (σ s = 0 → netOut α s = 0) ∧ (σ s ≠ 0 → 0 < netOut α s / σ s) := by
  obtain ⟨ho1, ho2⟩ := outflow_sign_c W s
  have hin := inflow_zero_c W s
  unfold netOut
  rw [hin, sub_zero]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hne
    have := ho1 hne
    rw [h, sign_zero] at this
    exact hne (sign_eq_zero_iff.mp this.symm)
  · have hne : α (Sum.inr (Sum.inr s)) ≠ 0 := fun h0 => h (ho2 h0)
    have hsg := ho1 hne
    rcases lt_or_gt_of_ne h with hs | hs
    · rw [sign_neg hs] at hsg
      have : α (Sum.inr (Sum.inr s)) < 0 := sign_eq_neg_one_iff.mp hsg.symm
      exact div_pos_of_neg_of_neg this hs
    · rw [sign_pos hs] at hsg
      have : 0 < α (Sum.inr (Sum.inr s)) := sign_eq_one_iff.mp hsg.symm
      exact div_pos this hs

/-- The diagonal produced by the flows. -/
noncomputable def flowDiagC (α : N.fullyOpen.R → ℝ) (σ : S → ℝ) (s : S) : ℝ :=
  if σ s = 0 then 1 else netOut α s / σ s

theorem flowDiagC_pos (W : N.fullyOpen.ConcordanceWitness α σ) (s : S) :
    0 < flowDiagC α σ s := by
  unfold flowDiagC
  split_ifs with h
  · exact one_pos
  · exact (netOut_spec_c W s).2 h

theorem flowDiagC_mul (W : N.fullyOpen.ConcordanceWitness α σ) (s : S) :
    flowDiagC α σ s * σ s = netOut α s := by
  unfold flowDiagC
  split_ifs with h
  · rw [h, mul_zero, (netOut_spec_c W s).1 h]
  · field_simp

theorem exists_reactant_of_rate_ne (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) (r : N.R) (h : α (Sum.inl r) ≠ 0) :
    ∃ s, (N.reaction r).source s ≠ 0 ∧
      0 < α (Sum.inl r) / (N.fullyOpen.reactionDirectionSign (Sum.inl r) s * σ s) := by
  obtain ⟨s, hs, hsg⟩ := W.sign_match _ h
  simp only [fullyOpen_reaction_inl] at hs
  refine ⟨s, hs, ?_⟩
  have htarget : (N.reaction r).target s = 0 := hsep r s hs
  have hdir : 0 < N.fullyOpen.reactionDirectionSign (Sum.inl r) s := by
    rw [dir_inl, reactionVector_apply, htarget]
    have : (0 : ℝ) < (N.reaction r).source s := by exact_mod_cast Nat.pos_of_ne_zero hs
    simpa using this
  have hσ : σ s ≠ 0 := by
    intro h0
    rw [h0, sign_zero] at hsg
    exact h (sign_eq_zero_iff.mp hsg.symm)
  rcases lt_or_gt_of_ne h with hneg | hpos
  · rw [sign_neg hneg] at hsg
    have : σ s < 0 := sign_eq_neg_one_iff.mp hsg
    exact div_pos_of_neg_of_neg hneg (mul_neg_of_pos_of_neg hdir this)
  · rw [sign_pos hpos] at hsg
    have : 0 < σ s := sign_eq_one_iff.mp hsg
    exact div_pos hpos (mul_pos hdir this)

open Classical in
/-- The weights on internal channels, carried by a reactant species. -/
noncomputable def chanWeightC (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) (r : N.R) (t : S) : ℝ :=
  if h : α (Sum.inl r) ≠ 0 then
    (if t = Classical.choose (exists_reactant_of_rate_ne hsep W r h) then
      α (Sum.inl r) / (N.fullyOpen.reactionDirectionSign (Sum.inl r) t * σ t) else 0)
  else 0

theorem chanWeightC_nonneg (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) (r : N.R) (t : S) :
    0 ≤ chanWeightC hsep W r t := by
  unfold chanWeightC
  split_ifs with h ht
  · subst ht
    exact (Classical.choose_spec (exists_reactant_of_rate_ne hsep W r h)).2.le
  · exact le_refl 0
  · exact le_refl 0

theorem chanWeightC_reactant (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) (r : N.R) (t : S)
    (hne : chanWeightC hsep W r t ≠ 0) : (N.reaction r).source t ≠ 0 := by
  unfold chanWeightC at hne
  split_ifs at hne with h ht
  · subst ht
    exact (Classical.choose_spec (exists_reactant_of_rate_ne hsep W r h)).1
  · exact absurd rfl hne
  · exact absurd rfl hne

theorem sum_chanWeightC (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) (r : N.R) :
    ∑ t, chanWeightC hsep W r t * N.reactionVector r t * σ t = -α (Sum.inl r) := by
  classical
  by_cases h : α (Sum.inl r) ≠ 0
  · set s₀ := Classical.choose (exists_reactant_of_rate_ne hsep W r h) with hs₀
    have hspec := (Classical.choose_spec (exists_reactant_of_rate_ne hsep W r h)).2
    rw [← hs₀] at hspec
    have hden : N.fullyOpen.reactionDirectionSign (Sum.inl r) s₀ * σ s₀ ≠ 0 := by
      intro h0; rw [h0, div_zero] at hspec; exact lt_irrefl 0 hspec
    rw [Finset.sum_eq_single s₀]
    · unfold chanWeightC
      rw [dif_pos h, if_pos hs₀]
      rw [dir_inl] at hden ⊢
      have hν : N.reactionVector r s₀ ≠ 0 := fun h0 => hden (by rw [h0]; ring)
      have hσ : σ s₀ ≠ 0 := fun h0 => hden (by rw [h0]; ring)
      field_simp
    · intro t _ ht
      unfold chanWeightC
      rw [dif_pos h, if_neg (by rw [← hs₀]; exact ht)]
      ring
    · intro h'; exact absurd (Finset.mem_univ s₀) h'
  · push Not at h
    rw [h, neg_zero]
    apply Finset.sum_eq_zero
    intro t _
    unfold chanWeightC
    rw [dif_neg (by push Not; exact h)]
    ring

/-- All weights. -/
noncomputable def bcWeightC (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) : N.R ⊕ S → S → ℝ :=
  Sum.elim (chanWeightC hsep W) (fun t' _ => flowDiagC α σ t')

theorem bcWeightC_nonneg (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) (k : N.R ⊕ S) (t : S) :
    0 ≤ bcWeightC hsep W k t := by
  cases k with
  | inl r => exact chanWeightC_nonneg hsep W r t
  | inr t' => exact (flowDiagC_pos W t').le

theorem kernel_at_c (W : N.fullyOpen.ConcordanceWitness α σ) (s : S) :
    ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s = netOut α s := by
  have h := inKerL_apply W.mem_kerL s
  change ∑ r : N.R ⊕ S ⊕ S, α r * N.fullyOpen.reactionVector r s = 0 at h
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type] at h
  have h1 : ∑ t : S, α (Sum.inr (Sum.inl t)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inl t)) s = α (Sum.inr (Sum.inl s)) := by
    simp only [reactionVector_inflow, Pi.single_apply]
    simp
  have h2 : ∑ t : S, α (Sum.inr (Sum.inr t)) *
      N.fullyOpen.reactionVector (Sum.inr (Sum.inr t)) s = -α (Sum.inr (Sum.inr s)) := by
    simp only [reactionVector_outflow, Pi.neg_apply, Pi.single_apply]
    simp
  rw [h1, h2] at h
  have h3 : ∑ r : N.R, α (Sum.inl r) * N.fullyOpen.reactionVector (Sum.inl r) s =
      ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s := rfl
  rw [h3] at h
  unfold netOut
  linarith

/-- **A discordance witness makes the product singular.** -/
theorem det_bcProduct_eq_zero_of_concordanceWitness (hsep : N.ReactantProductSeparated)
    (W : N.fullyOpen.ConcordanceWitness α σ) :
    (N.bcMatrix * Matrix.of (fun k t => bcWeightC hsep W k t * N.bcMatrix t k)).det = 0 := by
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨σ, W.sigma_ne, ?_⟩
  rw [← Matrix.mulVec_mulVec]
  have hinner : (Matrix.of (fun k t => bcWeightC hsep W k t * N.bcMatrix t k)).mulVec σ =
      Sum.elim (fun r => -α (Sum.inl r)) (fun t' => netOut α t') := by
    funext k
    cases k with
    | inl r =>
      show ∑ t, bcWeightC hsep W (Sum.inl r) t * N.bcMatrix t (Sum.inl r) * σ t = -α (Sum.inl r)
      rw [← sum_chanWeightC hsep W r]
      rfl
    | inr t' =>
      show ∑ t, bcWeightC hsep W (Sum.inr t') t * N.bcMatrix t (Sum.inr t') * σ t = netOut α t'
      simp only [bcWeightC, Sum.elim_inr, bcMatrix_inr]
      rw [Finset.sum_eq_single t']
      · rw [if_pos rfl, mul_one, flowDiagC_mul W]
      · intro t _ ht; rw [if_neg ht]; ring
      · intro h'; exact absurd (Finset.mem_univ t') h'
  rw [hinner]
  funext s
  show ∑ k : N.R ⊕ S, N.bcMatrix s k *
      Sum.elim (fun r => -α (Sum.inl r)) (fun t' => netOut α t') k = 0
  rw [Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, bcMatrix_inl, bcMatrix_inr]
  rw [Finset.sum_eq_single (f := fun t' => (if s = t' then (1 : ℝ) else 0) * netOut α t') s]
  · rw [if_pos rfl, one_mul, ← kernel_at_c W s]
    simp only [mul_neg, Finset.sum_neg_distrib]
    rw [show (∑ r : N.R, N.reactionVector r s * α (Sum.inl r)) =
        ∑ r : N.R, α (Sum.inl r) * N.reactionVector r s from
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)]
    ring
  · intro t _ ht; rw [if_neg (Ne.symm ht)]; ring
  · intro h'; exact absurd (Finset.mem_univ s) h'

end Witness

/-- **Positivity of the product for reactant-supported weights** under the DSR condition. -/
theorem det_bcProduct_pos_dsr (N : Network S) (hsep : N.ReactantProductSeparated)
    (hflow : N.FlowsAreSingletons) (hDSR : N.DSRCriterion)
    (w : N.R ⊕ S → S → ℝ) (hw : ∀ k t, 0 ≤ w k t) (hd : ∀ t, 0 < w (Sum.inr t) t)
    (hwr : ∀ r t, w (Sum.inl r) t ≠ 0 → (N.reaction r).source t ≠ 0) :
    0 < (N.bcMatrix * Matrix.of (fun k t => w k t * N.bcMatrix t k)).det := by
  apply DetCycle.det_mul_pos_of_coeff_nonneg_on _ w hw _ (fun t => Sum.inr t)
  · have hid : N.bcMatrix.submatrix id (fun t => Sum.inr t) = 1 := by
      ext s t
      simp [Matrix.one_apply]
    rw [hid, Matrix.det_one]
    simp only [bcMatrix_inr, if_true, Finset.prod_const_one, mul_one]
    exact Finset.prod_pos fun t _ => hd t
  · intro f hf
    refine N.bc_coeff_nonneg_dsr hsep hflow hDSR f fun t r hfr => ?_
    have h1 : w (f t) t ≠ 0 := (Finset.prod_ne_zero_iff.mp hf) t (Finset.mem_univ t)
    rw [hfr] at h1
    exact hwr r t h1

/-- **The DSR condition makes the fully open extension concordant** (Banaji–Craciun DSR
theorem, concordance form). -/
theorem concordant_fullyOpen_of_dsrCriterion (N : Network S)
    (hsep : N.ReactantProductSeparated) (hflow : N.FlowsAreSingletons)
    (hDSR : N.DSRCriterion) : N.fullyOpen.Concordant := by
  rintro ⟨α, σ, W⟩
  have hzero := det_bcProduct_eq_zero_of_concordanceWitness hsep W
  have hpos := N.det_bcProduct_pos_dsr hsep hflow hDSR (bcWeightC hsep W)
    (bcWeightC_nonneg hsep W) (fun t => flowDiagC_pos W t)
    (fun r t h => chanWeightC_reactant hsep W r t h)
  rw [hzero] at hpos
  exact lt_irrefl 0 hpos

/-- **DSR theorem, injectivity form.** Under the DSR condition every weakly monotonic kinetics
on the fully open extension is injective. -/
theorem injective_fullyOpen_of_dsrCriterion (N : Network S)
    (hsep : N.ReactantProductSeparated) (hflow : N.FlowsAreSingletons)
    (hDSR : N.DSRCriterion) {K : Kinetics N.fullyOpen} (hK : K.WeaklyMonotonic) :
    K.Injective :=
  (N.fullyOpen.concordant_iff_all_weaklyMonotonic_injective.mp
    (N.concordant_fullyOpen_of_dsrCriterion hsep hflow hDSR)) K hK

end Network
end CRNT
