import CRNT.Multistationarity.Injectivity
import CRNT.LinearAlgebra.SignVector

/-!
# Concordance and kinetics-independent monostationarity

Following Shinar and Feinberg, "Concordant Chemical Reaction Networks"
(Mathematical Biosciences, arXiv:1109.2923), a reaction network is **concordant** when a
purely structural sign-counting configuration on its reaction vectors is forbidden. The
force of concordance is that a concordant network is injective — hence monostationary —
when taken with *any* weakly monotonic kinetics, with no further assumption on the rate law.

The development is abstract sign counting. For `α : N.R → ℝ` and `σ : S → ℝ`:

* `InKerL N α` is `∑ r, α r • reactionVector r = 0`, membership of `α` in the kernel of
  the map carrying a reaction-rate displacement to its species displacement.
* `ConcordanceWitness N α σ` is the forbidden configuration: `α ∈ ker L`,
  `σ ∈ stoichSubspace`, `σ ≠ 0`, and the two sign-implication clauses (i)/(ii) on the
  source supports of the reactions.
* `Concordant N` asserts no such witness exists.
* `WeaklyMonotonic K`: on nonnegative compositions whose source supports
  are present, a reaction's rate change has the sign behaviour matched by the corresponding
  composition change on the source support.

The payoff is `Concordant.injective_of_weaklyMonotonic`: a weakly monotonic kinetics on a
concordant network is injective in the Craciun–Feinberg sense, hence has at most one
positive steady state per stoichiometric compatibility class
(`Concordant.subsingleton_steadyState`), kinetics-independently. Mass action is weakly
monotonic, so the mass-action specialization follows. The converse direction — that a
discordant network admits a noninjective weakly monotonic kinetics — is not developed here.

Depends on:
`CRNT.Multistationarity.Injectivity`, `CRNT.LinearAlgebra.SignVector`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-- **Membership in the kernel of `L`.** A reaction-rate displacement `α : N.R → ℝ` lies in
the kernel of the stoichiometric map when its induced species displacement vanishes:
`∑ r, α r • reactionVector r = 0`. -/
def InKerL (N : Network S) (α : N.R → ℝ) : Prop :=
  ∑ r : N.R, α r • N.reactionVector r = 0

theorem inKerL_apply {α : N.R → ℝ} (h : N.InKerL α) (s : S) :
    ∑ r : N.R, α r * N.reactionVector r s = 0 := by
  have := congrArg (fun f : S → ℝ => f s) h
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this

theorem inKerL_of_apply {α : N.R → ℝ}
    (h : ∀ s : S, ∑ r : N.R, α r * N.reactionVector r s = 0) : N.InKerL α := by
  funext s
  simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h s

/-- **The forbidden configuration.** A `ConcordanceWitness` for `N` is a pair
`(α, σ)` with `α ∈ ker L`, `σ` a nonzero stoichiometric vector, and:

* (i) for each reaction `r` with `α r ≠ 0`, some species in the source support of `r` has
  `SignType.sign (σ s) = SignType.sign (α r)`;
* (ii) for each reaction `r` with `α r = 0`, either `σ` vanishes on the source support of
  `r`, or that support contains two species with strictly opposite signs of `σ`. -/
structure ConcordanceWitness (N : Network S) (α : N.R → ℝ) (σ : S → ℝ) : Prop where
  /-- `α` lies in the kernel of the stoichiometric map. -/
  mem_kerL : N.InKerL α
  /-- `σ` lies in the stoichiometric subspace. -/
  mem_stoich : σ ∈ N.stoichSubspace
  /-- `σ` is nonzero. -/
  sigma_ne : σ ≠ 0
  /-- Clause (i): a reaction with nonzero `α` matches a same-sign species on its source
  support. -/
  sign_match : ∀ r : N.R, α r ≠ 0 →
    ∃ s : S, (N.reaction r).source s ≠ 0 ∧ SignType.sign (σ s) = SignType.sign (α r)
  /-- Clause (ii): a reaction with zero `α` either has `σ` vanishing on its source support,
  or that support carries opposite strict signs of `σ`. -/
  sign_balance : ∀ r : N.R, α r = 0 →
    (∀ s : S, (N.reaction r).source s ≠ 0 → σ s = 0) ∨
    (∃ s s' : S, (N.reaction r).source s ≠ 0 ∧ (N.reaction r).source s' ≠ 0 ∧
      σ s < 0 ∧ 0 < σ s')

/-- **Concordance.** A network is concordant when no `ConcordanceWitness` exists. -/
def Concordant (N : Network S) : Prop :=
  ¬ ∃ (α : N.R → ℝ) (σ : S → ℝ), N.ConcordanceWitness α σ

namespace Kinetics

/-- **Weakly monotonic kinetics.** For every pair of nonnegative
compositions `c*`, `c**` and every reaction `r` whose source support is present in both
compositions, the change in the rate of `r` has its sign reflected by the change of the
compositions on the source support:

* (i) if the rate strictly increases, some source species strictly increases;
* (ii) if the rate is unchanged, either the compositions agree on the source support, or the
  source support contains a strictly increasing and a strictly decreasing species.

The nonnegativity and support guards are Feinberg's; on a positive composition the
implications hold for every reaction. -/
def WeaklyMonotonic (K : Kinetics N) : Prop :=
  ∀ (cs css : Concentration S), cs.Nonnegative → css.Nonnegative →
    ∀ r : N.R, (∀ s : S, (N.reaction r).source s ≠ 0 → cs s ≠ 0) →
      (∀ s : S, (N.reaction r).source s ≠ 0 → css s ≠ 0) →
      (K.rate r cs < K.rate r css →
        ∃ s : S, (N.reaction r).source s ≠ 0 ∧ cs s < css s) ∧
      (K.rate r cs = K.rate r css →
        (∀ s : S, (N.reaction r).source s ≠ 0 → cs s = css s) ∨
        (∃ s s' : S, (N.reaction r).source s ≠ 0 ∧ (N.reaction r).source s' ≠ 0 ∧
          cs s < css s ∧ css s' < cs s'))

/-- **The forbidden configuration from two compositions.** Two positive
compositions `cs`, `css` whose difference lies in the stoichiometric subspace, at which a
weakly monotonic kinetics takes equal field values, give a `ConcordanceWitness` with rate
displacement `α r = K.rate r css − K.rate r cs` and species displacement `σ = css − cs`,
provided `cs ≠ css`. This is the structural content behind injectivity of a concordant
network. -/
theorem concordanceWitness_of_eq_vectorField {K : Kinetics N} (hwm : K.WeaklyMonotonic)
    {cs css : Concentration S} (hcs : cs.Positive) (hcss : css.Positive)
    (hmem : css - cs ∈ N.stoichSubspace) (hne : cs ≠ css)
    (hfield : K.vectorField cs = K.vectorField css) :
    N.ConcordanceWitness (fun r => K.rate r css - K.rate r cs) (css - cs) := by
  set α : N.R → ℝ := fun r => K.rate r css - K.rate r cs with hα
  set σ : Concentration S := css - cs with hσ
  -- The support guards are vacuous: positive compositions never vanish.
  have hcsg : ∀ r : N.R, ∀ s : S, (N.reaction r).source s ≠ 0 → cs s ≠ 0 :=
    fun r s _ => (hcs s).ne'
  have hcssg : ∀ r : N.R, ∀ s : S, (N.reaction r).source s ≠ 0 → css s ≠ 0 :=
    fun r s _ => (hcss s).ne'
  -- The induced species displacement vanishes, i.e. `α ∈ ker L`.
  have hker : N.InKerL α := by
    refine N.inKerL_of_apply fun s => ?_
    have hx : K.vectorField cs s = K.vectorField css s := by rw [hfield]
    have : ∑ r : N.R, (K.rate r css - K.rate r cs) * N.reactionVector r s
        = (∑ r : N.R, K.rate r css * N.reactionVector r s)
          - ∑ r : N.R, K.rate r cs * N.reactionVector r s := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    simp only [hα]
    rw [this]
    have e1 : ∑ r : N.R, K.rate r css * N.reactionVector r s = K.vectorField css s :=
      (K.vectorField_apply css s).symm
    have e2 : ∑ r : N.R, K.rate r cs * N.reactionVector r s = K.vectorField cs s :=
      (K.vectorField_apply cs s).symm
    rw [e1, e2, ← hx, sub_self]
  refine ⟨hker, hmem, ?_, ?_, ?_⟩
  · -- `σ ≠ 0` since `cs ≠ css`.
    simp only [hσ]
    intro h
    exact hne (sub_eq_zero.mp h).symm
  · -- Clause (i).
    intro r hαr
    have hwmr := hwm cs css hcs.nonnegative hcss.nonnegative r (hcsg r) (hcssg r)
    rcases lt_or_gt_of_ne hαr with hlt | hgt
    · -- `α r < 0`, i.e. `K css < K cs`; the rate strictly decreases, apply (i) swapped.
      have hrate : K.rate r css < K.rate r cs := by simp only [hα] at hlt; linarith
      have hwmr' := hwm css cs hcss.nonnegative hcs.nonnegative r (hcssg r) (hcsg r)
      obtain ⟨s, hs, hsgt⟩ := hwmr'.1 hrate
      refine ⟨s, hs, ?_⟩
      have hσs : σ s < 0 := by simp only [hσ, Pi.sub_apply]; linarith
      have hαneg : α r < 0 := hlt
      rw [_root_.sign_neg hσs, _root_.sign_neg hαneg]
    · -- `α r > 0`, i.e. `K cs < K css`; the rate strictly increases, apply (i).
      have hrate : K.rate r cs < K.rate r css := by simp only [hα] at hgt; linarith
      obtain ⟨s, hs, hsgt⟩ := hwmr.1 hrate
      refine ⟨s, hs, ?_⟩
      have hσs : 0 < σ s := by simp only [hσ, Pi.sub_apply]; linarith
      have hαpos : 0 < α r := hgt
      rw [_root_.sign_pos hσs, _root_.sign_pos hαpos]
  · -- Clause (ii).
    intro r hαr
    have hwmr := hwm cs css hcs.nonnegative hcss.nonnegative r (hcsg r) (hcssg r)
    have hrate : K.rate r cs = K.rate r css := by
      simp only [hα] at hαr; linarith
    rcases hwmr.2 hrate with heq | ⟨s, s', hs, hs', hgt, hlt⟩
    · left
      intro s hs
      have := heq s hs
      simp only [hσ, Pi.sub_apply]; linarith
    · right
      refine ⟨s', s, hs', hs, ?_, ?_⟩
      · simp only [hσ, Pi.sub_apply]; linarith
      · simp only [hσ, Pi.sub_apply]; linarith

end Kinetics

/-- **Mass action is weakly monotonic.** This is the sanity check on the statement of
`WeaklyMonotonic`: the chain to injectivity is only useful if mass action satisfies the
hypothesis. -/
theorem massActionKinetics_weaklyMonotonic (N : Network S) (κ : RateConstants N) :
    (N.massActionKinetics κ).WeaklyMonotonic := by
  intro cs css hcsnn hcssnn r hcsg hcssg
  set y : Complex S := (N.reaction r).source with hy
  -- On the source support both compositions are strictly positive.
  have hcspos : ∀ s : S, y s ≠ 0 → 0 < cs s := fun s hs =>
    lt_of_le_of_ne (hcsnn s) (Ne.symm (hcsg s hs))
  have hcsspos : ∀ s : S, y s ≠ 0 → 0 < css s := fun s hs =>
    lt_of_le_of_ne (hcssnn s) (Ne.symm (hcssg s hs))
  -- Every factor of either monomial, over all species, is strictly positive.
  have hfcs : ∀ s ∈ (Finset.univ : Finset S), 0 < cs s ^ y s := by
    intro s _
    by_cases hs : y s = 0
    · rw [hs, pow_zero]; exact one_pos
    · exact pow_pos (hcspos s hs) _
  have hfcss : ∀ s ∈ (Finset.univ : Finset S), 0 < css s ^ y s := by
    intro s _
    by_cases hs : y s = 0
    · rw [hs, pow_zero]; exact one_pos
    · exact pow_pos (hcsspos s hs) _
  -- The rate equals the rate constant times the source monomial.
  have hrate : ∀ x : Concentration S,
      (N.massActionKinetics κ).rate r x = κ.k r * ∏ s : S, x s ^ y s := fun x => rfl
  have hκpos : 0 < κ.k r := κ.positive r
  constructor
  · -- Clause (i): a strict rate increase forces a strict increase on the source support.
    intro hlt
    by_contra hcon
    push Not at hcon
    -- No source species strictly increases, so the monomial does not increase.
    have hmono : ∏ s : S, css s ^ y s ≤ ∏ s : S, cs s ^ y s := by
      refine Finset.prod_le_prod₀ (fun s _ => le_of_lt (hfcss s (Finset.mem_univ s)))
        (fun s _ => ?_)
      by_cases hs : y s = 0
      · rw [hs, pow_zero, pow_zero]
      · exact pow_le_pow_left₀ (le_of_lt (hcsspos s hs)) (hcon s hs) _
    rw [hrate, hrate] at hlt
    have := mul_le_mul_of_nonneg_left hmono hκpos.le
    linarith
  · -- Clause (ii): equal rates force agreement on the support or opposite strict changes.
    intro heq
    rw [hrate, hrate] at heq
    have hmoneq : ∏ s : S, cs s ^ y s = ∏ s : S, css s ^ y s :=
      mul_left_cancel₀ hκpos.ne' heq
    by_cases hall : ∀ s : S, y s ≠ 0 → cs s = css s
    · left; exact hall
    · right
      push Not at hall
      -- There is a support species where the compositions differ.
      obtain ⟨s₀, hs₀supp, hs₀ne⟩ := hall
      -- A strictly increasing source species exists, else the monomial strictly decreases.
      have hgt : ∃ s : S, y s ≠ 0 ∧ cs s < css s := by
        by_contra hcon
        push Not at hcon
        have hle : ∏ s : S, css s ^ y s ≤ ∏ s : S, cs s ^ y s := by
          refine Finset.prod_le_prod₀ (fun s _ => le_of_lt (hfcss s (Finset.mem_univ s)))
            (fun s _ => ?_)
          by_cases hs : y s = 0
          · rw [hs, pow_zero, pow_zero]
          · exact pow_le_pow_left₀ (le_of_lt (hcsspos s hs)) (hcon s hs) _
        -- Some support species strictly decreases (the differing one), so the product is
        -- strictly smaller, contradicting equality of monomials.
        have hs₀lt : css s₀ < cs s₀ := lt_of_le_of_ne (hcon s₀ hs₀supp) (by
          intro h; exact hs₀ne h.symm)
        have hstrict : ∏ s : S, css s ^ y s < ∏ s : S, cs s ^ y s := by
          refine Finset.prod_lt_prod₀ (fun s _ => hfcss s (Finset.mem_univ s))
            (fun s _ => ?_)
            ⟨s₀, Finset.mem_univ s₀, ?_⟩
          · by_cases hs : y s = 0
            · rw [hs, pow_zero, pow_zero]
            · exact pow_le_pow_left₀ (le_of_lt (hcsspos s hs)) (hcon s hs) _
          · exact pow_lt_pow_left₀ hs₀lt (le_of_lt (hcsspos s₀ hs₀supp)) hs₀supp
        rw [hmoneq] at hstrict
        exact lt_irrefl _ hstrict
      -- A strictly decreasing source species exists, by the symmetric argument.
      have hlt : ∃ s : S, y s ≠ 0 ∧ css s < cs s := by
        by_contra hcon
        push Not at hcon
        have hs₀gt : cs s₀ < css s₀ := lt_of_le_of_ne (hcon s₀ hs₀supp) hs₀ne
        have hstrict : ∏ s : S, cs s ^ y s < ∏ s : S, css s ^ y s := by
          refine Finset.prod_lt_prod₀ (fun s _ => hfcs s (Finset.mem_univ s))
            (fun s _ => ?_)
            ⟨s₀, Finset.mem_univ s₀, ?_⟩
          · by_cases hs : y s = 0
            · rw [hs, pow_zero, pow_zero]
            · exact pow_le_pow_left₀ (le_of_lt (hcspos s hs)) (hcon s hs) _
          · exact pow_lt_pow_left₀ hs₀gt (le_of_lt (hcspos s₀ hs₀supp)) hs₀supp
        rw [hmoneq] at hstrict
        exact lt_irrefl _ hstrict
      obtain ⟨sg, hsg, hsglt⟩ := hgt
      obtain ⟨sl, hsl, hsllt⟩ := hlt
      exact ⟨sg, sl, hsg, hsl, hsglt, hsllt⟩

/-- **Injectivity of a concordant network.** A weakly monotonic kinetics on a concordant
network is injective in the Craciun–Feinberg sense: its induced field is injective on every
positive stoichiometric compatibility class. This holds for every weakly monotonic kinetics, with no further
assumption on the rate law. -/
theorem Concordant.injective_of_weaklyMonotonic (hN : N.Concordant) {K : Kinetics N}
    (hwm : K.WeaklyMonotonic) : K.Injective := by
  intro x₀ cs hcs css hcss hfield
  by_contra hne
  -- `css - cs` lies in the stoichiometric subspace (both compatible with `x₀`).
  have hmem : css - cs ∈ N.stoichSubspace := by
    have h1 : cs - x₀ ∈ N.stoichSubspace := hcs.1
    have h2 : css - x₀ ∈ N.stoichSubspace := hcss.1
    have : css - cs = (css - x₀) - (cs - x₀) := by ring
    rw [this]
    exact N.stoichSubspace.sub_mem h2 h1
  exact hN ⟨_, _, K.concordanceWitness_of_eq_vectorField hwm hcs.2 hcss.2 hmem hne hfield⟩

/-- **Kinetics-independent monostationarity.** A weakly monotonic kinetics on a concordant
network has at most one positive steady state per stoichiometric compatibility class. -/
theorem Concordant.subsingleton_steadyState (hN : N.Concordant) {K : Kinetics N}
    (hwm : K.WeaklyMonotonic) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsKineticSteadyState K x) (hsy : N.IsKineticSteadyState K y) : x = y :=
  (hN.injective_of_weaklyMonotonic hwm).subsingleton_steadyState hx hy hsx hsy

/-- **Mass-action specialization.** A concordant network has at most one positive mass-action
steady state per stoichiometric compatibility class, for every choice of rate constants,
since mass action is weakly monotonic. -/
theorem Concordant.massAction_subsingleton_steadyState (hN : N.Concordant)
    (κ : RateConstants N) {x₀ x y : Concentration S}
    (hx : x ∈ N.positiveCompatibilityClass x₀) (hy : y ∈ N.positiveCompatibilityClass x₀)
    (hsx : N.IsMassActionSteadyState κ x) (hsy : N.IsMassActionSteadyState κ y) : x = y :=
  hN.subsingleton_steadyState (N.massActionKinetics_weaklyMonotonic κ) hx hy
    ((N.isMassActionSteadyState_iff_kinetic κ x).mp hsx)
    ((N.isMassActionSteadyState_iff_kinetic κ y).mp hsy)

end Network

end CRNT
