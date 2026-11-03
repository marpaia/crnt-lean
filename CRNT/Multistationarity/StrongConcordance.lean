import CRNT.Multistationarity.WeakNormality
import CRNT.Multistationarity.FullyOpenConcordanceSpectral
import CRNT.LinearAlgebra.SignVector

/-!
# Strong concordance and two-way weakly monotonic kinetics

Strong concordance is the structural condition paired with kinetics in which both reactant
activation and product inhibition may influence a reaction rate.  For a reaction
`y → y'`, write `y-y' = -ν`.  A positive rate displacement must be witnessed by a species
whose concentration displacement has the same sign as `y-y'`; a negative rate displacement
uses the opposite sign.  Zero rate displacement permits either no reactant change or
opposing signed influences.

This is the Shinar--Feinberg strong-concordance definition.  Strong concordance implies
ordinary concordance and gives injectivity for every two-way weakly monotonic kinetics.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- No species occurs on both sides of one reaction. This removes ambiguity between
reactant activation and product inhibition. -/
def ReactantProductSeparated (N : Network S) : Prop :=
  ∀ r : N.R, ∀ s : S,
    (N.reaction r).source s ≠ 0 → (N.reaction r).target s = 0

/-- Signed reactant-minus-product coefficient. -/
def reactionDirectionSign (N : Network S) (r : N.R) (s : S) : ℝ :=
  ((N.reaction r).source s : ℝ) - ((N.reaction r).target s : ℝ)

/-- A species displacement `σ` promotes reaction `r` in the two-way sense: either a
reactant increases or a product decreases. -/
def Promotes (N : Network S) (r : N.R) (σ : S → ℝ) (s : S) : Prop :=
  SignType.sign (σ s) = SignType.sign (N.reactionDirectionSign r s) ∧
    N.reactionDirectionSign r s ≠ 0

/-- A species displacement opposes reaction `r`: reactant decreases or product increases. -/
def Opposes (N : Network S) (r : N.R) (σ : S → ℝ) (s : S) : Prop :=
  SignType.sign (σ s) = -SignType.sign (N.reactionDirectionSign r s) ∧
    N.reactionDirectionSign r s ≠ 0

/-- Forbidden sign configuration for strong concordance. -/
structure StrongConcordanceWitness (N : Network S)
    (α : N.R → ℝ) (σ : S → ℝ) : Prop where
  mem_kerL : N.InKerL α
  mem_stoich : σ ∈ N.stoichSubspace
  sigma_ne : σ ≠ 0
  positive_reaction : ∀ r : N.R, 0 < α r →
    ∃ s : S, N.Promotes r σ s
  negative_reaction : ∀ r : N.R, α r < 0 →
    ∃ s : S, N.Opposes r σ s
  zero_reaction : ∀ r : N.R, α r = 0 →
    (∀ s : S, (N.reaction r).source s ≠ 0 → σ s = 0) ∨
    (∃ s t : S, N.Promotes r σ s ∧ N.Opposes r σ t)

/-- Strong concordance. -/
def StronglyConcordant (N : Network S) : Prop :=
  ¬ ∃ (α : N.R → ℝ) (σ : S → ℝ), N.StrongConcordanceWitness α σ

/-- Strong discordance. -/
def StronglyDiscordant (N : Network S) : Prop := ¬ N.StronglyConcordant

/-- Strong discordance is existence of the explicit witness. -/
theorem stronglyDiscordant_iff_exists_witness (N : Network S) :
    N.StronglyDiscordant ↔
      ∃ (α : N.R → ℝ) (σ : S → ℝ), N.StrongConcordanceWitness α σ := by
  simp [StronglyDiscordant, StronglyConcordant]

/-- On source/product-separated networks, strong concordance implies ordinary concordance.
The separation hypothesis is essential for the present two-way definition: a product-side
influence can otherwise witness a strong sign condition without being a reactant sign witness. -/
theorem StronglyConcordant.concordant (h : N.StronglyConcordant)
    (hsep : N.ReactantProductSeparated) : N.Concordant := by
  intro hex
  rcases hex with ⟨α, σ, W⟩
  apply h
  refine ⟨α, σ, ?_⟩
  refine ⟨W.mem_kerL, W.mem_stoich, W.sigma_ne, ?_, ?_, ?_⟩
  · intro r ha
    obtain ⟨s, hs, hsign⟩ := W.sign_match r ha.ne'
    refine ⟨s, ?_, ?_⟩
    · have hdir : 0 < N.reactionDirectionSign r s := by
        rw [reactionDirectionSign, hsep r s hs]
        simp
        exact_mod_cast Nat.pos_of_ne_zero hs
      rw [hsign, _root_.sign_pos ha, _root_.sign_pos hdir]
    · rw [reactionDirectionSign, hsep r s hs]
      simp
      exact_mod_cast hs
  · intro r ha
    obtain ⟨s, hs, hsign⟩ := W.sign_match r ha.ne
    refine ⟨s, ?_, ?_⟩
    · have hdir : 0 < N.reactionDirectionSign r s := by
        rw [reactionDirectionSign, hsep r s hs]
        simp
        exact_mod_cast Nat.pos_of_ne_zero hs
      rw [hsign, _root_.sign_neg ha, _root_.sign_pos hdir]
    · rw [reactionDirectionSign, hsep r s hs]
      simp
      exact_mod_cast hs
  · intro r ha
    rcases W.sign_balance r ha with hall | ⟨s, t, hs, ht, hsneg, htpos⟩
    · exact Or.inl hall
    · right
      refine ⟨t, s, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · have hdir : 0 < N.reactionDirectionSign r t := by
            rw [reactionDirectionSign, hsep r t ht]
            simp
            exact_mod_cast Nat.pos_of_ne_zero ht
          rw [_root_.sign_pos htpos, _root_.sign_pos hdir]
        · rw [reactionDirectionSign, hsep r t ht]
          simp
          exact_mod_cast ht
      · refine ⟨?_, ?_⟩
        · have hdir : 0 < N.reactionDirectionSign r s := by
            rw [reactionDirectionSign, hsep r s hs]
            simp
            exact_mod_cast Nat.pos_of_ne_zero hs
          rw [_root_.sign_neg hsneg, _root_.sign_pos hdir]
        · rw [reactionDirectionSign, hsep r s hs]
          simp
          exact_mod_cast hs


namespace Kinetics

/-- Two-way weak monotonicity: increasing a rate requires a promoting reactant/product
change; unchanged rate either sees no reactant change or opposing influences. -/
def TwoWayWeaklyMonotonic (K : Kinetics N) : Prop :=
  ∀ (cs css : Concentration S), cs.Nonnegative → css.Nonnegative →
    ∀ r : N.R,
      (∀ s : S, (N.reaction r).source s ≠ 0 → cs s ≠ 0) →
      (∀ s : S, (N.reaction r).source s ≠ 0 → css s ≠ 0) →
      (K.rate r cs < K.rate r css →
        ∃ s : S, N.Promotes r (css - cs) s) ∧
      (K.rate r cs = K.rate r css →
        (∀ s : S, (N.reaction r).source s ≠ 0 → cs s = css s) ∨
        (∃ s t : S,
          N.Promotes r (css - cs) s ∧ N.Opposes r (css - cs) t))

/-- Ordinary weak monotonicity is a special case of two-way weak monotonicity when source
and target supports are disjoint. -/
theorem twoWayWeaklyMonotonic_of_weaklyMonotonic
    {K : Kinetics N} (hsep : N.ReactantProductSeparated)
    (hwm : K.WeaklyMonotonic) : K.TwoWayWeaklyMonotonic := by
  intro cs css hcs hcss r hcsg hcssg
  have H := hwm cs css hcs hcss r hcsg hcssg
  constructor
  · intro hrate
    obtain ⟨s, hs, hlt⟩ := H.1 hrate
    refine ⟨s, ?_, ?_⟩
    · have hsigma : 0 < (css - cs) s := by simp; linarith
      have hdir : 0 < N.reactionDirectionSign r s := by
        rw [reactionDirectionSign, hsep r s hs]
        simp
        exact_mod_cast Nat.pos_of_ne_zero hs
      rw [_root_.sign_pos hsigma, _root_.sign_pos hdir]
    · rw [reactionDirectionSign, hsep r s hs]
      simp
      exact_mod_cast hs
  · intro heq
    rcases H.2 heq with hall | ⟨s, t, hs, ht, hinc, hdec⟩
    · exact Or.inl hall
    · right
      refine ⟨s, t, ?_, ?_⟩
      · refine ⟨?_, ?_⟩
        · have hsigma : 0 < (css - cs) s := by simp; linarith
          have hdir : 0 < N.reactionDirectionSign r s := by
            rw [reactionDirectionSign, hsep r s hs]
            simp
            exact_mod_cast Nat.pos_of_ne_zero hs
          rw [_root_.sign_pos hsigma, _root_.sign_pos hdir]
        · rw [reactionDirectionSign, hsep r s hs]
          simp
          exact_mod_cast hs
      · refine ⟨?_, ?_⟩
        · have hsigma : (css - cs) t < 0 := by simp; linarith
          have hdir : 0 < N.reactionDirectionSign r t := by
            rw [reactionDirectionSign, hsep r t ht]
            simp
            exact_mod_cast Nat.pos_of_ne_zero ht
          rw [_root_.sign_neg hsigma, _root_.sign_pos hdir]
        · rw [reactionDirectionSign, hsep r t ht]
          simp
          exact_mod_cast ht

/-- Mass action is two-way weakly monotonic on source/product-separated networks. -/
theorem massActionKinetics_twoWayWeaklyMonotonic
    (N : Network S) (hsep : N.ReactantProductSeparated) (κ : N.RateConstants) :
    (N.massActionKinetics κ).TwoWayWeaklyMonotonic :=
  twoWayWeaklyMonotonic_of_weaklyMonotonic hsep
    (N.massActionKinetics_weaklyMonotonic κ)

/-- Equal vector-field values of a two-way weakly monotonic kinetics generate a strong
concordance witness. -/
theorem strongConcordanceWitness_of_eq_vectorField
    {K : Kinetics N} (htw : K.TwoWayWeaklyMonotonic)
    {cs css : Concentration S} (hcs : cs.Positive) (hcss : css.Positive)
    (hmem : css - cs ∈ N.stoichSubspace) (hne : cs ≠ css)
    (hfield : K.vectorField cs = K.vectorField css) :
    N.StrongConcordanceWitness
      (fun r => K.rate r css - K.rate r cs) (css - cs) := by
  set α : N.R → ℝ := fun r => K.rate r css - K.rate r cs with hα
  set σ : Concentration S := css - cs with hσ
  have hcsg : ∀ r : N.R, ∀ s : S, (N.reaction r).source s ≠ 0 → cs s ≠ 0 :=
    fun _ s _ => (hcs s).ne'
  have hcssg : ∀ r : N.R, ∀ s : S, (N.reaction r).source s ≠ 0 → css s ≠ 0 :=
    fun _ s _ => (hcss s).ne'
  have hker : N.InKerL α := by
    refine N.inKerL_of_apply fun s => ?_
    have hxy : K.vectorField cs s = K.vectorField css s := by rw [hfield]
    have hsum : ∑ r : N.R, (K.rate r css - K.rate r cs) * N.reactionVector r s
        = (∑ r : N.R, K.rate r css * N.reactionVector r s) -
          ∑ r : N.R, K.rate r cs * N.reactionVector r s := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    simp only [hα]
    rw [hsum, ← K.vectorField_apply css s, ← K.vectorField_apply cs s, ← hxy, sub_self]
  refine ⟨hker, hmem, ?_, ?_, ?_, ?_⟩
  · simpa [hσ, sub_ne_zero] using Ne.symm hne
  · intro r hr
    have hrate : K.rate r cs < K.rate r css := by simp only [hα] at hr; linarith
    exact (htw cs css hcs.nonnegative hcss.nonnegative r (hcsg r) (hcssg r)).1 hrate
  · intro r hr
    have hrate : K.rate r css < K.rate r cs := by simp only [hα] at hr; linarith
    obtain ⟨s, hsEq, hsne⟩ :=
      (htw css cs hcss.nonnegative hcs.nonnegative r (hcssg r) (hcsg r)).1 hrate
    refine ⟨s, ?_, hsne⟩
    simp only [hσ]
    rw [show (css - cs) s = -((cs - css) s) by simp, Left.sign_neg, hsEq]
  · intro r hr
    have hrate : K.rate r cs = K.rate r css := by simp only [hα] at hr; linarith
    rcases (htw cs css hcs.nonnegative hcss.nonnegative r (hcsg r) (hcssg r)).2 hrate with
      hall | hopp
    · left
      intro s hs
      have h := hall s hs
      simp only [hσ, Pi.sub_apply, h, sub_self]
    · right
      simpa only [hσ] using hopp

end Kinetics

/-- **Strong concordance injectivity theorem.** -/
theorem StronglyConcordant.injective_of_twoWayWeaklyMonotonic
    (hN : N.StronglyConcordant) {K : Kinetics N}
    (htw : K.TwoWayWeaklyMonotonic) : K.Injective := by
  intro x₀ x hx y hy hfield
  by_contra hxy
  have hmem : y - x ∈ N.stoichSubspace := by
    have hxS := hx.1
    have hyS := hy.1
    -- `ext s; ring` does not close a Pi-type subtraction; use the group identity.
    rw [← sub_sub_sub_cancel_right y x x₀]
    exact N.stoichSubspace.sub_mem hyS hxS
  exact hN ⟨_, _, K.strongConcordanceWitness_of_eq_vectorField htw
    hx.2 hy.2 hmem hxy hfield⟩

/-- Strong concordance therefore excludes multiple compatible positive steady states for
all two-way weakly monotonic kinetics. -/
theorem StronglyConcordant.subsingleton_steadyState
    (hN : N.StronglyConcordant) {K : Kinetics N}
    (htw : K.TwoWayWeaklyMonotonic)
    {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀)
    (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hssx : N.IsKineticSteadyState K x)
    (hssy : N.IsKineticSteadyState K y) : x = y :=
  (hN.injective_of_twoWayWeaklyMonotonic htw).subsingleton_steadyState hx hy hssx hssy

/-- Strong concordance descends from the fully open extension of a weakly normal network,
under the reactant/product separation hypothesis used in the strong-concordance theory. -/
theorem stronglyConcordant_of_fullyOpen_of_weaklyNormal
    (N : Network S) (hsep : N.ReactantProductSeparated) (hwn : N.WeaklyNormal)
    (hopen : N.fullyOpen.StronglyConcordant) : N.StronglyConcordant := by
  rintro ⟨α, σ, hW⟩
  rcases hwn with ⟨WN⟩
  let P := WN.influences
  let T := N.weakNormalityOperatorOnStoich P
  let σ0 : N.stoichSubspace := ⟨σ, hW.mem_stoich⟩
  obtain ⟨ε, hε, χ, hres, hsignσ⟩ :=
    descent_exists_resolvent_preserving_sign N T WN.nonsingular σ0 hW.sigma_ne
  let σ' : S → ℝ := (σ0 + ε • χ).1
  let β : N.R → ℝ := fun r => ∑ s : S, (P.influence r).vec s * χ.1 s
  have hTval : N.weakNormalityOperator P χ.1 = σ' := by
    have hv := congrArg Subtype.val hres
    change ((N.weakNormalityOperatorOnStoich P) χ : S → ℝ) = _ at hv
    rw [N.weakNormalityOperatorOnStoich_coe P χ] at hv
    simpa [T, σ'] using hv
  have hβsum : ∑ r : N.R, β r • N.reactionVector r = σ' := by
    simpa [weakNormalityOperator, β] using hTval
  obtain ⟨δ, hδ, hsignα⟩ := descent_exists_pos_preserving_nonzero_sign α β
  let α' : N.fullyOpen.R → ℝ := fun q =>
    match q with
    | Sum.inl r => α r + δ * β r
    | Sum.inr (Sum.inl _) => 0
    | Sum.inr (Sum.inr s) => δ * σ' s
  have hσ'ne : σ' ≠ 0 := by
    obtain ⟨s, hs⟩ : ∃ s : S, σ s ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hW.sigma_ne
      funext s
      exact hn s
    intro hz
    have hzS : σ' s = 0 := congrFun hz s
    have hp := hsignσ s hs
    have hp0 : SignType.sign (σ' s) = 0 := by rw [hzS, sign_zero]
    have hs0 : SignType.sign (σ s) ≠ 0 := sign_ne_zero.mpr hs
    exact hs0 (hp.symm.trans hp0)
  have hker : N.fullyOpen.InKerL α' := by
    apply N.fullyOpen.inKerL_of_apply
    intro s
    change (∑ q : N.R ⊕ (S ⊕ S), α' q * N.fullyOpen.reactionVector q s) = 0
    rw [Fintype.sum_sum_type]
    rw [Fintype.sum_sum_type]
    have horigα : ∑ r : N.R, α r * N.reactionVector r s = 0 := N.inKerL_apply hW.mem_kerL s
    have hβs : ∑ r : N.R, β r * N.reactionVector r s = σ' s := by
      have hv := congrArg (fun f : S → ℝ => f s) hβsum
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hv
    have horig : (∑ r : N.R, α' (Sum.inl r) * N.fullyOpen.reactionVector (Sum.inl r) s)
        = δ * σ' s := by
      calc
        _ = ∑ r : N.R, (α r + δ * β r) * N.reactionVector r s := by
          apply Finset.sum_congr rfl
          intro r _
          rw [show N.fullyOpen.reactionVector (Sum.inl r) s = N.reactionVector r s by rfl]
        _ = (∑ r : N.R, α r * N.reactionVector r s) +
            δ * (∑ r : N.R, β r * N.reactionVector r s) := by
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro r _
          ring
        _ = δ * σ' s := by rw [horigα, hβs, zero_add]
    rw [horig]
    have hin : (∑ t : S, α' (Sum.inr (Sum.inl t)) *
        N.fullyOpen.reactionVector (Sum.inr (Sum.inl t)) s) = 0 := by simp [α']
    rw [hin, zero_add]
    have hout : (∑ t : S, α' (Sum.inr (Sum.inr t)) *
        N.fullyOpen.reactionVector (Sum.inr (Sum.inr t)) s) = -(δ * σ' s) := by
      rw [Finset.sum_eq_single s]
      · rw [N.reactionVector_outflow s]
        simp [α']
      · intro t _ hts
        rw [N.reactionVector_outflow t]
        simp [α', Pi.single_eq_of_ne (Ne.symm hts)]
      · simp
    rw [hout]
    ring
  apply hopen
  refine ⟨α', σ', ?_⟩
  refine ⟨hker, ?_, hσ'ne, ?_, ?_, ?_⟩
  · rw [N.stoichSubspace_fullyOpen_eq_top]
    exact Submodule.mem_top
  · intro q hqpos
    rcases q with r | q
    · change ∃ s : S, N.Promotes r σ' s
      by_cases hα0 : α r = 0
      · have hβpos : 0 < β r := by
          simp [α', hα0] at hqpos
          rcases mul_pos_iff.mp hqpos with h | h
          · exact h.2
          · linarith
        rcases hW.zero_reaction r hα0 with hzero | hopp
        · have hex : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ 0 < χ.1 s := by
            by_contra hn
            push_neg at hn
            have hsum : β r ≤ 0 := by
              dsimp [β]
              apply Finset.sum_nonpos
              intro s _
              by_cases hs : (N.reaction r).source s = 0
              · have hp0 : (P.influence r).vec s = 0 := by
                  have hpnn := (P.influence r).nonneg s
                  have hnpos : ¬ 0 < (P.influence r).vec s := by
                    intro hp
                    exact ((P.influence r).pos_iff_source s).mp hp hs
                  linarith
                simp [hp0]
              · exact mul_nonpos_of_nonneg_of_nonpos ((P.influence r).nonneg s) (hn s hs)
            linarith
          obtain ⟨s, hs, hχs⟩ := hex
          refine ⟨s, ?_⟩
          refine ⟨?_, ?_⟩
          · have hσ0 := hzero s hs
            have hσ'eq : σ' s = ε * χ.1 s := by simp [σ', σ0, hσ0]
            have hσ'pos : 0 < σ' s := by rw [hσ'eq]; exact mul_pos hε hχs
            have hdirpos : 0 < N.reactionDirectionSign r s := by
              rw [reactionDirectionSign, hsep r s hs]
              simp
              exact_mod_cast Nat.pos_of_ne_zero hs
            rw [_root_.sign_pos hσ'pos, _root_.sign_pos hdirpos]
          · have hdirpos : 0 < N.reactionDirectionSign r s := by
              rw [reactionDirectionSign, hsep r s hs]
              simp
              exact_mod_cast Nat.pos_of_ne_zero hs
            exact ne_of_gt hdirpos
        · obtain ⟨sp, so, hprom, hoppose⟩ := hopp
          refine ⟨sp, ?_⟩
          refine ⟨?_, hprom.2⟩
          have hσne : σ sp ≠ 0 := by
            apply sign_ne_zero.mp
            rw [hprom.1]
            exact sign_ne_zero.mpr hprom.2
          have hsigne : SignType.sign (σ' sp) = SignType.sign (σ sp) := by
            simpa [σ', σ0] using hsignσ sp hσne
          exact hsigne.trans hprom.1
      · have hsign : SignType.sign (α' (Sum.inl r)) = SignType.sign (α r) := by
          simpa [α'] using hsignα r hα0
        have hαpos : 0 < α r := by
          apply sign_eq_one_iff.mp
          rw [← hsign, _root_.sign_pos hqpos]
        obtain ⟨s, hp⟩ := hW.positive_reaction r hαpos
        refine ⟨s, ?_⟩
        refine ⟨?_, hp.2⟩
        have hσne : σ s ≠ 0 := by
          apply sign_ne_zero.mp
          rw [hp.1]
          exact sign_ne_zero.mpr hp.2
        have hsigne : SignType.sign (σ' s) = SignType.sign (σ s) := by
          simpa [σ', σ0] using hsignσ s hσne
        exact hsigne.trans hp.1
    · rcases q with s | s
      · simp [α'] at hqpos
      · have hspos : 0 < σ' s := by
          have hh := hqpos
          simp only [α'] at hh
          rcases mul_pos_iff.mp hh with h | h
          · exact h.2
          · linarith
        refine ⟨s, ?_⟩
        refine ⟨?_, ?_⟩
        · simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
            singletonComplex_apply, hspos]
        · simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
            singletonComplex_apply]
  · intro q hqneg
    rcases q with r | q
    · change ∃ s : S, N.Opposes r σ' s
      by_cases hα0 : α r = 0
      · have hβneg : β r < 0 := by
          simp [α', hα0] at hqneg
          rcases mul_neg_iff.mp hqneg with h | h
          · exact h.2
          · linarith
        rcases hW.zero_reaction r hα0 with hzero | hopp
        · have hex : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ χ.1 s < 0 := by
            by_contra hn
            push_neg at hn
            have hsum : 0 ≤ β r := by
              dsimp [β]
              apply Finset.sum_nonneg
              intro s _
              by_cases hs : (N.reaction r).source s = 0
              · have hp0 : (P.influence r).vec s = 0 := by
                  have hpnn := (P.influence r).nonneg s
                  have hnpos : ¬ 0 < (P.influence r).vec s := by
                    intro hp
                    exact ((P.influence r).pos_iff_source s).mp hp hs
                  linarith
                simp [hp0]
              · exact mul_nonneg ((P.influence r).nonneg s) (hn s hs)
            linarith
          obtain ⟨s, hs, hχs⟩ := hex
          refine ⟨s, ?_⟩
          refine ⟨?_, ?_⟩
          · have hσ0 := hzero s hs
            have hσ'eq : σ' s = ε * χ.1 s := by simp [σ', σ0, hσ0]
            have hσ'neg : σ' s < 0 := by rw [hσ'eq]; exact mul_neg_of_pos_of_neg hε hχs
            have hdirpos : 0 < N.reactionDirectionSign r s := by
              rw [reactionDirectionSign, hsep r s hs]
              simp
              exact_mod_cast Nat.pos_of_ne_zero hs
            rw [_root_.sign_neg hσ'neg, _root_.sign_pos hdirpos]
          · have hdirpos : 0 < N.reactionDirectionSign r s := by
              rw [reactionDirectionSign, hsep r s hs]
              simp
              exact_mod_cast Nat.pos_of_ne_zero hs
            exact ne_of_gt hdirpos
        · obtain ⟨sp, so, hprom, hoppose⟩ := hopp
          refine ⟨so, ?_⟩
          refine ⟨?_, hoppose.2⟩
          have hσne : σ so ≠ 0 := by
            apply sign_ne_zero.mp
            rw [hoppose.1]
            intro hz
            exact (sign_ne_zero.mpr hoppose.2) (SignType.neg_eq_zero_iff.mp hz)
          have hsigne : SignType.sign (σ' so) = SignType.sign (σ so) := by
            simpa [σ', σ0] using hsignσ so hσne
          exact hsigne.trans hoppose.1
      · have hsign : SignType.sign (α' (Sum.inl r)) = SignType.sign (α r) := by
          simpa [α'] using hsignα r hα0
        have hαneg : α r < 0 := by
          apply sign_eq_neg_one_iff.mp
          rw [← hsign, _root_.sign_neg hqneg]
        obtain ⟨s, hp⟩ := hW.negative_reaction r hαneg
        refine ⟨s, ?_⟩
        refine ⟨?_, hp.2⟩
        have hσne : σ s ≠ 0 := by
          apply sign_ne_zero.mp
          rw [hp.1]
          intro hz
          exact (sign_ne_zero.mpr hp.2) (SignType.neg_eq_zero_iff.mp hz)
        have hsigne : SignType.sign (σ' s) = SignType.sign (σ s) := by
          simpa [σ', σ0] using hsignσ s hσne
        exact hsigne.trans hp.1
    · rcases q with s | s
      · simp [α'] at hqneg
      · have hsneg : σ' s < 0 := by
          have := hqneg
          simp only [α'] at this
          rcases mul_neg_iff.mp this with h | h
          · exact h.2
          · linarith
        refine ⟨s, ?_⟩
        refine ⟨?_, ?_⟩
        · simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
            singletonComplex_apply, hsneg]
        · simp [reactionDirectionSign, fullyOpen_reaction_outflow, outflowReaction,
            singletonComplex_apply]
  · intro q hq0
    rcases q with r | q
    · change
        (∀ s : S, (N.reaction r).source s ≠ 0 → σ' s = 0) ∨
          (∃ s t : S, N.Promotes r σ' s ∧ N.Opposes r σ' t)
      by_cases hα0 : α r = 0
      · have hβ0 : β r = 0 := by
          have : δ * β r = 0 := by simpa [α', hα0] using hq0
          exact (mul_eq_zero.mp this).resolve_left hδ.ne'
        rcases hW.zero_reaction r hα0 with hzero | hopp
        · by_cases hall : ∀ s : S, (N.reaction r).source s ≠ 0 → χ.1 s = 0
          · left
            intro s hs
            have hσ0 := hzero s hs
            have hχ0 := hall s hs
            simp [σ', σ0, hσ0, hχ0]
          · right
            push Not at hall
            obtain ⟨s0, hs0, hχ0ne⟩ := hall
            rcases lt_or_gt_of_ne hχ0ne with hχ0neg | hχ0pos
            · have hexpos : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ 0 < χ.1 s := by
                by_contra hn
                push_neg at hn
                have hnonpos : ∀ s ∈ (Finset.univ : Finset S),
                    (P.influence r).vec s * χ.1 s ≤ 0 := by
                  intro s _
                  by_cases hs : (N.reaction r).source s = 0
                  · have hp0 : (P.influence r).vec s = 0 := by
                      have hpnn := (P.influence r).nonneg s
                      have hnpos : ¬ 0 < (P.influence r).vec s := by
                        intro hp
                        exact ((P.influence r).pos_iff_source s).mp hp hs
                      linarith
                    simp [hp0]
                  · exact mul_nonpos_of_nonneg_of_nonpos ((P.influence r).nonneg s) (hn s hs)
                have hp0pos : 0 < (P.influence r).vec s0 := ((P.influence r).pos_iff_source s0).2 hs0
                have hstrict : (P.influence r).vec s0 * χ.1 s0 < 0 := mul_neg_of_pos_of_neg hp0pos hχ0neg
                have hsumneg : β r < 0 := by
                  dsimp [β]
                  apply Finset.sum_neg' hnonpos
                  exact ⟨s0, Finset.mem_univ s0, hstrict⟩
                linarith
              obtain ⟨sp, hsp, hχp⟩ := hexpos
              refine ⟨sp, s0, ?_, ?_⟩
              · refine ⟨?_, ?_⟩
                · have hσp0 := hzero sp hsp
                  have hσ'eq : σ' sp = ε * χ.1 sp := by simp [σ', σ0, hσp0]
                  have hσ'pos : 0 < σ' sp := by rw [hσ'eq]; exact mul_pos hε hχp
                  have hdirpos : 0 < N.reactionDirectionSign r sp := by
                    rw [reactionDirectionSign, hsep r sp hsp]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hsp
                  rw [_root_.sign_pos hσ'pos, _root_.sign_pos hdirpos]
                · have hdirpos : 0 < N.reactionDirectionSign r sp := by
                    rw [reactionDirectionSign, hsep r sp hsp]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hsp
                  exact ne_of_gt hdirpos
              · refine ⟨?_, ?_⟩
                · have hσ00 := hzero s0 hs0
                  have hσ'eq : σ' s0 = ε * χ.1 s0 := by simp [σ', σ0, hσ00]
                  have hσ'neg : σ' s0 < 0 := by rw [hσ'eq]; exact mul_neg_of_pos_of_neg hε hχ0neg
                  have hdirpos : 0 < N.reactionDirectionSign r s0 := by
                    rw [reactionDirectionSign, hsep r s0 hs0]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hs0
                  rw [_root_.sign_neg hσ'neg, _root_.sign_pos hdirpos]
                · have hdirpos : 0 < N.reactionDirectionSign r s0 := by
                    rw [reactionDirectionSign, hsep r s0 hs0]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hs0
                  exact ne_of_gt hdirpos
            · have hexneg : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ χ.1 s < 0 := by
                by_contra hn
                push_neg at hn
                have hnonneg : ∀ s ∈ (Finset.univ : Finset S),
                    0 ≤ (P.influence r).vec s * χ.1 s := by
                  intro s _
                  by_cases hs : (N.reaction r).source s = 0
                  · have hp0 : (P.influence r).vec s = 0 := by
                      have hpnn := (P.influence r).nonneg s
                      have hnpos : ¬ 0 < (P.influence r).vec s := by
                        intro hp
                        exact ((P.influence r).pos_iff_source s).mp hp hs
                      linarith
                    simp [hp0]
                  · exact mul_nonneg ((P.influence r).nonneg s) (hn s hs)
                have hp0pos : 0 < (P.influence r).vec s0 := ((P.influence r).pos_iff_source s0).2 hs0
                have hstrict : 0 < (P.influence r).vec s0 * χ.1 s0 := mul_pos hp0pos hχ0pos
                have hsumpos : 0 < β r := by
                  dsimp [β]
                  apply Finset.sum_pos' hnonneg
                  exact ⟨s0, Finset.mem_univ s0, hstrict⟩
                linarith
              obtain ⟨sn, hsn, hχn⟩ := hexneg
              refine ⟨s0, sn, ?_, ?_⟩
              · refine ⟨?_, ?_⟩
                · have hσ00 := hzero s0 hs0
                  have hσ'eq : σ' s0 = ε * χ.1 s0 := by simp [σ', σ0, hσ00]
                  have hσ'pos : 0 < σ' s0 := by rw [hσ'eq]; exact mul_pos hε hχ0pos
                  have hdirpos : 0 < N.reactionDirectionSign r s0 := by
                    rw [reactionDirectionSign, hsep r s0 hs0]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hs0
                  rw [_root_.sign_pos hσ'pos, _root_.sign_pos hdirpos]
                · have hdirpos : 0 < N.reactionDirectionSign r s0 := by
                    rw [reactionDirectionSign, hsep r s0 hs0]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hs0
                  exact ne_of_gt hdirpos
              · refine ⟨?_, ?_⟩
                · have hσn0 := hzero sn hsn
                  have hσ'eq : σ' sn = ε * χ.1 sn := by simp [σ', σ0, hσn0]
                  have hσ'neg : σ' sn < 0 := by rw [hσ'eq]; exact mul_neg_of_pos_of_neg hε hχn
                  have hdirpos : 0 < N.reactionDirectionSign r sn := by
                    rw [reactionDirectionSign, hsep r sn hsn]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hsn
                  rw [_root_.sign_neg hσ'neg, _root_.sign_pos hdirpos]
                · have hdirpos : 0 < N.reactionDirectionSign r sn := by
                    rw [reactionDirectionSign, hsep r sn hsn]
                    simp
                    exact_mod_cast Nat.pos_of_ne_zero hsn
                  exact ne_of_gt hdirpos
        · right
          obtain ⟨sp, so, hprom, hoppose⟩ := hopp
          refine ⟨sp, so, ?_, ?_⟩
          · refine ⟨?_, hprom.2⟩
            have hσne : σ sp ≠ 0 := by
              apply sign_ne_zero.mp
              rw [hprom.1]
              exact sign_ne_zero.mpr hprom.2
            have hsigne : SignType.sign (σ' sp) = SignType.sign (σ sp) := by
              simpa [σ', σ0] using hsignσ sp hσne
            exact hsigne.trans hprom.1
          · refine ⟨?_, hoppose.2⟩
            have hσne : σ so ≠ 0 := by
              apply sign_ne_zero.mp
              rw [hoppose.1]
              intro hz
              exact (sign_ne_zero.mpr hoppose.2) (SignType.neg_eq_zero_iff.mp hz)
            have hsigne : SignType.sign (σ' so) = SignType.sign (σ so) := by
              simpa [σ', σ0] using hsignσ so hσne
            exact hsigne.trans hoppose.1
      · have hsign := hsignα r hα0
        have hα'ne : α r + δ * β r ≠ 0 := by
          intro hz
          rw [hz, sign_zero] at hsign
          exact (sign_ne_zero.mpr hα0) hsign.symm
        exact (hα'ne (by simpa [α'] using hq0)).elim
    · rcases q with s | s
      · left
        intro u hu
        simp [fullyOpen_reaction_inflow, inflowReaction] at hu
      · left
        have hs0 : σ' s = 0 := by
          have : δ * σ' s = 0 := by simpa [α'] using hq0
          exact (mul_eq_zero.mp this).resolve_left hδ.ne'
        intro u hu
        simp [fullyOpen_reaction_outflow, outflowReaction, singletonComplex_apply] at hu
        subst u
        exact hs0


/-- In particular the descent theorem holds for weakly reversible, source/product-separated networks. -/
theorem stronglyConcordant_of_fullyOpen_of_weaklyReversible
    (N : Network S) (hsep : N.ReactantProductSeparated) (hwr : N.WeaklyReversible)
    (hopen : N.fullyOpen.StronglyConcordant) : N.StronglyConcordant :=
  N.stronglyConcordant_of_fullyOpen_of_weaklyNormal hsep
    (N.weaklyNormal_of_weaklyReversible hwr) hopen

end Network
end CRNT
