import CRNT.Deficiency.AdvancedDeficiencyAlgorithm
import CRNT.Deficiency.ColinearityClasses
import CRNT.Geometry.Endotactic
import CRNT.Multistationarity.CapacityCharacterization
import CRNT.Multistationarity.AdvancedDeficiencyAlgorithm
import Mathlib.Basic.Sign.Basic

/-!
# The Advanced Deficiency Algorithm: the within-class sign comparisons and the coplanar-set
# orderings of Ji §1.7

The **Advanced Deficiency Algorithm** (ADA) generalizes Feinberg's Deficiency One Algorithm to
networks of higher deficiency (Ellison, *A combinatorial route to the deficiency one condition*;
Ji, *Uniqueness of equilibria for complex chemical reaction networks*, Ohio State University,
2011, §1.7).  Its distinctive ingredient is the **colinearity class** structure: the reactions
are grouped into *colinearity classes* `CCᵢ` — maximal sets of reactions whose reaction vectors
are collinear — and each class `CCᵢ` is given an extra real unknown `Mᵢ`, against which the
reactions of the class are shelved (upper: `y · μ > Mᵢ`, middle: `y · μ = Mᵢ`, lower:
`y · μ < Mᵢ`).  The classes are then coordinated by the **coplanar-set analysis**: for three
classes whose representative vectors satisfy `cₖwₖ = cᵢwᵢ + cⱼwⱼ` with positive integers
`cᵢ, cⱼ, cₖ`, the unknowns are ordered, `Mᵢ > Mₖ > Mⱼ`, all equal, or `Mᵢ < Mₖ < Mⱼ`.

## The faithfulness defect this module repairs

The repository already contains the *combinatorial* ADA: `ADAData` (the `Mᵢ` together with a
per-reaction shelving, `ADAData.imposes` (the shelf-versus-`Mᵢ` constraints) and the verdict
`ADAAffirmsCapacity`.  But `CRNT.Multistationarity.AdvancedDeficiencyAlgorithm` records the
defect: because `M ≡ 0` and the sign-based shelving `adaShelfOf` always satisfy `imposes`, the
verdict is *equivalent to mere sign-compatibility*,

```text
N.ADAAffirmsCapacity  ↔  ∃ μ, μ ≠ 0 ∧ N.SignCompatibleWithStoich μ
```

(`adaAffirmsCapacity_iff_exists_signCompatible`).  Two constraint layers of Ji §1.7 were not
imposed: the **within-class sign comparisons** of `y · μ` versus `y' · μ` driven by the chosen
sign of `CCᵢ`, and the **coplanar-set `Mᵢ`-orderings**.

## What this module formalizes

* **The colinearity classes and their orientation** (`SameLine`, `SameHalfLine`): two reactions
  lie on the same *line* when their reaction vectors are collinear in both directions (this is
  the equivalence relation of the classes, `sameLine_refl`, `sameLine_symm`, `sameLine_trans`),
  and on the same *half-line* when the relating scalar is positive — this is the "chosen sign of
  `CCᵢ`" of Ji §1.7.
* **The within-class sign comparison** (`colinear_pairing_sign_agrees`): two reactions of one
  colinearity class lying on the same half-line of that class have `μ`-rates — hence pairing
  *differences* — of the same sign.  The claim about the *source* pairings alone is **false**
  (the reactants of two collinear reactions may be different complexes), and the module records
  the counterexample (`colinear_source_pairings_need_not_agree`).
* **The coplanar-set data and ordering** (`CoplanarReactions`, `CoplanarMOrder`): the relation
  `cₖwₖ = cᵢwᵢ + cⱼwⱼ` and the three-way ordering of the `Mᵢ` it induces, together with the
  rate relation it forces (`coplanar_rate_relation`).
* **The strengthened verdict** (`ADAAffirmsCapacityStrong`): the old verdict with the two
  Ji §1.7 layers imposed *and* the flux certificate (a strictly positive flux satisfying the two
  balance equations) which the algorithm's numerical version tests for.  The strengthened
  verdict implies the multistationarity capacity (`ADAAffirmsCapacityStrong_hasCapacity`), so it
  is no longer equivalent to mere sign-compatibility
  (`ADAAffirmsCapacityStrong_ne_exists_signCompatible`,
  `ADACoplanarExample.signCompatible_ne_hasCapacity`).  The two layers are genuine extra
  constraints on the run's data: the degenerate choice `M ≡ 0` with the sign-based shelving
  fails the within-class *realization* condition on a concrete network
  (`ADACoplanarExample.degenerateData_fails_withinClass`).

The verdict is a `def` with an existential, not a `structure`: a `Prop`-valued structure cannot
carry the data of a run (`d`, `μ`, the flux), exactly as `N.ADAAffirmsCapacity` is a `def`.

## What remains open

* The **numerical version** of the ADA — the reduction of the flux feasibility problem to a
  linear program over the sign patterns of the fluxes — is **not** formalized here, and neither is
  the **endotacticity of the shelves** (`N.EndotacticShelf`, `N.StronglyEndotacticShelf` remain
  separate structural hypotheses, as in `CRNT.Multistationarity.AdvancedDeficiencyAlgorithm`).
* The `M`/coplanar machinery of Ji §1.7 is only **partially** formalized.  Formalized here: the
  colinearity classes and their orientation (`SameLine`, `SameHalfLine`, and the quotient of
  `CRNT.Deficiency.ColinearityClasses`), the within-class sign comparison, the coplanar relation
  and its `M`-ordering, and the *realization* of the class value `Mᵢ` inside its class (the
  middle shelf of a class is nonempty).  **Not** formalized: the *extended system* of Ji §1.7
  (the extended reaction vectors and the extended stoichiometric subspace against which
  `(μ, M)` is tested for sign compatibility), the *enumeration* of the admissible `Mᵢ` and
  shelfings, the *derivation* of the coplanar ordering from the network's combinatorics (here it
  is imposed as a condition on the run, not proved), and the converse direction of the algorithm
  (a capacity does not yet produce a strengthened run).  In particular, the coplanar ordering
  *alone* does not exclude the degenerate choice `M ≡ 0` (the "all equal" case of Ji §1.7
  applies, `coplanarMOrder_of_zeroM`): what excludes it is the within-class realization
  condition.

Depends on: `CRNT.Deficiency.AdvancedDeficiencyAlgorithm`,
`CRNT.Deficiency.ColinearityClasses`, `CRNT.Geometry.Endotactic`,
`CRNT.Multistationarity.CapacityCharacterization`,
`CRNT.Multistationarity.AdvancedDeficiencyAlgorithm`.
-/

namespace CRNT

namespace Network

open scoped BigOperators

section General

variable {S : Type} [DecidableEq S] [Fintype S] {N : Network S}

/-! ### The within-class sign comparison of Ji §1.7 -/

/-- **Two reactions of one colinearity class lying on the same half-line of that class.**  The
relating scalar of the colinearity is *positive*: the two reaction vectors point in the same
direction.  This is the "chosen sign of `CCᵢ`" of Ji §1.7 — a class is oriented by choosing one
of its two half-lines. -/
def SameHalfLine (N : Network S) (r r' : N.R) : Prop :=
  ∃ a : ℝ, N.reactionVector r' = a • N.reactionVector r ∧ 0 < a

/-- **A colinearity class always has a relating scalar.**  Colinearity is `w = a • v` for some
real `a`. -/
theorem ColinearReactions.exists_scalar {N : Network S} {r r' : N.R}
    (hcol : N.ColinearReactions r r') :
    ∃ a : ℝ, N.reactionVector r' = a • N.reactionVector r :=
  hcol

/-- **The `μ`-rate of a reaction is the difference of the pairings of its target and its
source.**  The `μ`-rate `⟨v_r, μ⟩ = ∑_s v_r(s) μ(s)` is the *pairing difference* of the reaction:
it measures how the pairing `y · μ` changes across the reaction. -/
theorem pairingDifference_eq_wRate (N : Network S) (r : N.R) (μ : S → ℝ) :
    CRNT.complexPairing (N.reaction r).target μ - CRNT.complexPairing (N.reaction r).source μ
      = N.wRate μ r := by
  simp only [CRNT.complexPairing, Complex.toRealVector_apply, wRate, dotProduct]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [reactionVector_apply]
  ring

/-- **The `μ`-rates of two colinear reactions scale by the relating scalar.** -/
theorem colinear_wRate_scale {N : Network S} {r r' : N.R} {a : ℝ}
    (ha : N.reactionVector r' = a • N.reactionVector r) (μ : S → ℝ) :
    N.wRate μ r' = a * N.wRate μ r := by
  simp only [wRate, dotProduct]
  rw [ha]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **The `μ`-rates of two colinear reactions are proportional.**  The scalar is the one
witnessing the colinearity. -/
theorem colinear_wRate_proportional {N : Network S} {r r' : N.R}
    (hcol : N.ColinearReactions r r') (μ : S → ℝ) :
    ∃ a : ℝ, N.wRate μ r' = a * N.wRate μ r := by
  obtain ⟨a, ha⟩ := hcol
  exact ⟨a, colinear_wRate_scale ha μ⟩

/-- **Two reactions on the same half-line of their class are colinear.** -/
theorem SameHalfLine.colinear {N : Network S} {r r' : N.R} (h : N.SameHalfLine r r') :
    N.ColinearReactions r r' := by
  obtain ⟨a, ha, _⟩ := h
  exact ⟨a, ha⟩

/-- **The within-class sign comparison of Ji §1.7.**  Two reactions of one colinearity class
lying on the *same half-line* of that class have `μ`-rates of the same sign: the sign of
`⟨v_r, μ⟩` is constant along the class, and it is the sign which drives the algorithm's
comparison of `y · μ` against `y' · μ` inside the class.

This is the precise content of the "within-class sign comparison" for *reaction vectors*.  For
the *source* pairings alone the analogous claim is false: two collinear reactions may have
different reactant complexes (see `colinear_source_pairings_need_not_agree`). -/
theorem colinear_pairing_sign_agrees {N : Network S} {r r' : N.R}
    (h : N.SameHalfLine r r') (μ : S → ℝ) :
    SignType.sign (N.wRate μ r') = SignType.sign (N.wRate μ r) := by
  obtain ⟨a, ha, ha_pos⟩ := h
  have hscale : N.wRate μ r' = a * N.wRate μ r := colinear_wRate_scale ha μ
  rw [hscale, sign_mul, sign_pos ha_pos, one_mul]

/-- **The within-class sign comparison, in terms of the pairing differences.**  The pairing
difference `⟨y'_r, μ⟩ − ⟨y_r, μ⟩` of two reactions of one colinearity class on the same
half-line has the same sign for the two reactions. -/
theorem colinear_pairingDifference_sign_agrees {N : Network S} {r r' : N.R}
    (h : N.SameHalfLine r r') (μ : S → ℝ) :
    SignType.sign (CRNT.complexPairing (N.reaction r').target μ -
        CRNT.complexPairing (N.reaction r').source μ) =
      SignType.sign (CRNT.complexPairing (N.reaction r).target μ -
        CRNT.complexPairing (N.reaction r).source μ) := by
  rw [pairingDifference_eq_wRate, pairingDifference_eq_wRate]
  exact colinear_pairing_sign_agrees h μ

/-- **The within-class sign comparison is a theorem, not an extra hypothesis**: it holds for
every log-ratio `μ`.  This is the mathematical content of the first Ji §1.7 layer. -/
theorem withinClassSignComparison (N : Network S) (μ : S → ℝ) :
    ∀ r r' : N.R, N.SameHalfLine r r' →
      SignType.sign (N.wRate μ r') = SignType.sign (N.wRate μ r) :=
  fun _ _ h => colinear_pairing_sign_agrees h μ

/-! ### The colinearity classes as lines, and the coplanar-set data of Ji §1.7 -/

/-- **Two reactions lie on the same line**: their reaction vectors are collinear *in both
directions*.  This is the equivalence relation underlying the colinearity classes of Ji §1.7:
collinear reaction vectors lie on a common line through the origin, and the two half-lines of
that line are the two orientations ("signs") of the class.  (The one-sided relation
`N.ColinearReactions` is symmetric whenever the second reaction vector is nonzero; the
mutual relation is symmetric always, and it is the right notion of "same class" in the
presence of zero reaction vectors.) -/
def SameLine (N : Network S) (r r' : N.R) : Prop :=
  N.ColinearReactions r r' ∧ N.ColinearReactions r' r

/-- **Same-line is reflexive.** -/
theorem sameLine_refl (N : Network S) (r : N.R) : N.SameLine r r :=
  ⟨ColinearReactions.refl r, ColinearReactions.refl r⟩

/-- **Same-line is symmetric.** -/
theorem sameLine_symm (N : Network S) {r r' : N.R} (h : N.SameLine r r') : N.SameLine r' r :=
  ⟨h.2, h.1⟩

/-- **Same-line is transitive.**  This is the point where the *zero* reaction vectors have to be
handled: two reactions whose reaction vectors are zero lie on "the" zero line, and a reaction
with a zero reaction vector is related to no other line. -/
theorem sameLine_trans (N : Network S) {r r' r'' : N.R} (h₁ : N.SameLine r r')
    (h₂ : N.SameLine r' r'') : N.SameLine r r'' := by
  obtain ⟨a, ha⟩ := h₁.1
  obtain ⟨b, hb⟩ := h₂.1
  have hrel : N.reactionVector r'' = (b * a) • N.reactionVector r := by
    rw [hb, ha, smul_smul]
  by_cases hz : N.reactionVector r' = 0
  · -- all three reaction vectors vanish
    obtain ⟨c, hc⟩ := h₁.2
    obtain ⟨d, hd⟩ := h₂.2
    have hz1 : N.reactionVector r = 0 := by rw [hc, hz, smul_zero]
    have hz2 : N.reactionVector r'' = 0 := by rw [hb, hz, smul_zero]
    exact ⟨⟨0, by rw [hz2, zero_smul]⟩, ⟨0, by rw [hz1, zero_smul]⟩⟩
  · -- all three reaction vectors are nonzero, so the relating scalars are invertible
    have hz'' : N.reactionVector r'' ≠ 0 := by
      obtain ⟨d, hd⟩ := h₂.2
      intro hcon
      have : N.reactionVector r' = 0 := by rw [hd, hcon, smul_zero]
      exact hz this
    have hna : a ≠ 0 := by
      intro hcon
      have : N.reactionVector r' = 0 := by simp only [ha, hcon, zero_smul]
      exact hz this
    have hnb : b ≠ 0 := by
      intro hcon
      have : N.reactionVector r'' = 0 := by simp only [hb, hcon, zero_smul]
      exact hz'' this
    refine ⟨⟨b * a, hrel⟩, ?_⟩
    refine ⟨(b * a)⁻¹, ?_⟩
    rw [hrel]
    funext s
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ (mul_ne_zero hnb hna), one_mul]

/-- **The colinearity class of a reaction**: the set of reactions lying on its line. -/
def colinearClass (N : Network S) (r : N.R) : Set N.R := {r' | N.SameLine r r'}

/-- **The colinearity class of a reaction is nonempty** (it contains the reaction itself). -/
theorem mem_colinearClass (N : Network S) (r : N.R) : r ∈ N.colinearClass r :=
  sameLine_refl N r

/-- **The class value of a reaction is constant on its colinearity class.**  The `Mᵢ` of Ji §1.7
is a *class* quantity. -/
theorem M_colinear_of_sameLine (d : N.ADAData) {r r' : N.R} (h : N.SameLine r r') :
    d.M r = d.M r' :=
  d.M_colinear r r' h.1

/-- **Coplanar reactions** (Ji §1.7): three reactions whose reaction vectors satisfy the
positive-integer relation `cₖwₖ = cᵢwᵢ + cⱼwⱼ`, where `wᵢ`, `wⱼ`, `wₖ` are the reaction vectors
of the three reactions and `cᵢ, cⱼ, cₖ` are positive integers.  Such a triple is a *coplanar
set* of Ji §1.7. -/
def CoplanarReactions (N : Network S) (rᵢ rⱼ rₖ : N.R) : Prop :=
  ∃ cᵢ cⱼ cₖ : ℕ, 0 < cᵢ ∧ 0 < cⱼ ∧ 0 < cₖ ∧
    (cₖ : ℝ) • N.reactionVector rₖ = (cᵢ : ℝ) • N.reactionVector rᵢ + (cⱼ : ℝ) • N.reactionVector rⱼ

/-- **The coplanar-set ordering of Ji §1.7.**  For every coplanar triplet of reactions, the class
values are ordered `Mᵢ > Mₖ > Mⱼ`, all equal, or `Mᵢ < Mₖ < Mⱼ`. -/
def CoplanarMOrder (N : Network S) (d : N.ADAData) : Prop :=
  ∀ rᵢ rⱼ rₖ : N.R, N.CoplanarReactions rᵢ rⱼ rₖ →
    ((d.M rᵢ > d.M rₖ ∧ d.M rₖ > d.M rⱼ) ∨
      ((d.M rᵢ = d.M rₖ ∧ d.M rₖ = d.M rⱼ) ∨
        (d.M rᵢ < d.M rₖ ∧ d.M rₖ < d.M rⱼ)))

/-- **The pairing of a vector with a log-ratio scales by a scalar.** -/
theorem dotProduct_smul {S : Type} [DecidableEq S] [Fintype S] (μ v : S → ℝ) (a : ℝ) :
    dotProduct μ (a • v) = a * dotProduct μ v := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **The pairing of a vector with a log-ratio is additive.** -/
theorem dotProduct_add {S : Type} [DecidableEq S] [Fintype S] (μ v w : S → ℝ) :
    dotProduct μ (v + w) = dotProduct μ v + dotProduct μ w := by
  simp only [dotProduct, Pi.add_apply]
  calc
    ∑ x, μ x * (v x + w x) = ∑ x, (μ x * v x + μ x * w x) := by
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    _ = (∑ x, μ x * v x) + ∑ x, μ x * w x :=
      Finset.sum_add_distrib (s := (Finset.univ : Finset S))
        (f := fun x : S => μ x * v x) (g := fun x : S => μ x * w x)

/-- **The coplanar relation is reflected in the `μ`-rates.**  If `cₖwₖ = cᵢwᵢ + cⱼwⱼ`, then
`cₖ⟨wₖ, μ⟩ = cᵢ⟨wᵢ, μ⟩ + cⱼ⟨wⱼ, μ⟩`: the coplanar relation is a relation between the classes'
rates. -/
theorem coplanar_rate_relation {N : Network S} {rᵢ rⱼ rₖ : N.R}
    (hcop : N.CoplanarReactions rᵢ rⱼ rₖ) (μ : S → ℝ) :
    ∃ cᵢ cⱼ cₖ : ℕ,
      (cₖ : ℝ) * N.wRate μ rₖ = (cᵢ : ℝ) * N.wRate μ rᵢ + (cⱼ : ℝ) * N.wRate μ rⱼ := by
  obtain ⟨cᵢ, cⱼ, cₖ, _, _, _, hrel⟩ := hcop
  refine ⟨cᵢ, cⱼ, cₖ, ?_⟩
  have h := congrArg (fun v : S → ℝ => dotProduct μ v) hrel
  rw [dotProduct_smul, dotProduct_add, dotProduct_smul, dotProduct_smul] at h
  simpa only [wRate, dotProduct] using h

/-- **The degenerate data `M ≡ 0` satisfies the coplanar ordering** (in the "all equal" case).
The coplanar ordering alone therefore does *not* exclude the degenerate choice; what excludes it
is the within-class realization condition (see `degenerateData_fails_withinClass`). -/
theorem coplanarMOrder_of_zeroM (N : Network S) (d : N.ADAData) (hM : ∀ r, d.M r = 0) :
    N.CoplanarMOrder d := by
  intro rᵢ rⱼ rₖ _
  refine Or.inr (Or.inl ⟨?_, ?_⟩)
  · rw [hM rᵢ, hM rₖ]
  · rw [hM rₖ, hM rⱼ]

/-- **The within-class conditions of Ji §1.7** on the data of a run:
* the *realization* of the class value: the class value `Mᵢ` is one of the source pairings of the
  reactions of its class — the middle shelf of the class is nonempty, so `Mᵢ` is one of the finitely
  many candidate values the algorithm enumerates;
* the *sign comparison* within the class, which is a theorem (`withinClassSignComparison`). -/
def WithinClassConditions (N : Network S) (d : N.ADAData) (μ : S → ℝ) : Prop :=
  (∀ r : N.R, ∃ r' : N.R, N.SameLine r r' ∧
      CRNT.complexPairing (N.reaction r').source μ = d.M r) ∧
  (∀ r r' : N.R, N.SameHalfLine r r' →
      SignType.sign (N.wRate μ r') = SignType.sign (N.wRate μ r))

/-! ### The strengthened verdict -/

omit [DecidableEq S] in
/-- **The two pairing conventions agree**: `CRNT.complexPairing` (used by `ADAData.imposes`) and
`CRNT.Network.complexPairing` (used by the flux balances) are the same functional. -/
theorem complexPairing_eq (y : Complex S) (μ : S → ℝ) :
    CRNT.complexPairing y μ = CRNT.Network.complexPairing y μ := by
  simp [CRNT.complexPairing, CRNT.Network.complexPairing, Complex.toRealVector_apply]

/-- **The strengthened combinatorial Advanced Deficiency Algorithm verdict.**  The old verdict
`N.ADAAffirmsCapacity` — some `ADAData` and a nonzero, sign-compatible `μ` meeting the
shelf-versus-`Mᵢ` constraints — with the two constraint layers of Ji §1.7 imposed:

* the **within-class conditions** (`N.WithinClassConditions`): the within-class sign comparison
  of Ji §1.7, together with the *realization* of the class value `Mᵢ` inside its class (the middle
  shelf of a class is nonempty);
* the **coplanar-set ordering** (`N.CoplanarMOrder`): for a coplanar triplet
  `cₖwₖ = cᵢwᵢ + cⱼwⱼ`, the class values are ordered `Mᵢ > Mₖ > Mⱼ`, all equal, or
  `Mᵢ < Mₖ < Mⱼ`;

and with the **flux certificate** which the numerical version of the algorithm tests for (a
strictly positive flux satisfying the two flux balances).  The flux certificate is what makes
the verdict reach the multistationarity capacity.

(The data are existential, as in `N.ADAAffirmsCapacity`: a `Prop`-valued structure cannot carry
the data of a run.) -/
def ADAAffirmsCapacityStrong (N : Network S) : Prop :=
  ∃ (d : N.ADAData) (μ : S → ℝ) (α : N.R → ℝ),
    μ ≠ 0 ∧ N.SignCompatibleWithStoich μ ∧ d.imposes μ ∧
      N.WithinClassConditions d μ ∧ N.CoplanarMOrder d ∧
      (∀ r, 0 < α r) ∧
      (∀ s, ∑ r, α r * N.reactionVector r s = 0) ∧
      (∀ s, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s = 0)

/-- **The strengthened verdict implies the old verdict.** -/
theorem adaAffirmsCapacity_of_adaAffirmsCapacityStrong {N : Network S}
    (h : N.ADAAffirmsCapacityStrong) : N.ADAAffirmsCapacity := by
  obtain ⟨d, μ, _, hμ0, hsc, himp, _, _, _, _, _⟩ := h
  exact ⟨d, μ, hμ0, hsc, himp⟩

/-- **The strengthened verdict implies the multistationarity capacity.**  This is the *forward*
direction of the Advanced Deficiency Algorithm under the strengthened hypotheses: the witness is
the flux certificate `(α, μ, σ)` of
`CRNT.Network.hasMultistationarityCapacity_iff_flux_sign`, `σ` being the stoichiometric vector
realizing the sign pattern of `μ`. -/
theorem ADAAffirmsCapacityStrong_hasCapacity {N : Network S}
    (h : N.ADAAffirmsCapacityStrong) : N.HasMultistationarityCapacity := by
  obtain ⟨_, μ, α, hμ0, hsc, _, _, _, hα, hlb, hub⟩ := h
  obtain ⟨σ, hσS, hσ0, hsign⟩ := (N.signCompatibleWithStoich_iff μ hμ0).mp hsc
  exact (N.hasMultistationarityCapacity_iff_flux_sign).2
    ⟨α, μ, σ, hα, hσS, hσ0, hsign, hlb, hub⟩

end General

/-! ### A concrete instance: the deficiency-one module `0 → A`, `0 → B`, `A + B → 0` -/

namespace ADACoplanarExample

open scoped BigOperators
open Finset

/-- The species of the example: `{A, B}`. -/
inductive Species
  | A | B
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A, Species.B}
  complete := by
    intro s
    cases s with
    | A => simp
    | B => simp

open Species

/-- The zero complex. -/
def c0 : Complex Species := fun _ => 0

/-- The complex `A`. -/
def cA : Complex Species := fun s => match s with | .A => 1 | .B => 0

/-- The complex `B`. -/
def cB : Complex Species := fun s => match s with | .A => 0 | .B => 1

/-- The complex `A + B`. -/
def cAB : Complex Species := fun s => match s with | .A => 1 | .B => 1

/-- The reaction channels of the example. -/
inductive Rxn
  | r1 | r2 | r3
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2, Rxn.r3}
  complete := by
    intro r
    cases r with
    | r1 => simp
    | r2 => simp
    | r3 => simp

/-- The reaction set of the example, as an insert chain. -/
def allRxns : Finset Rxn := insert Rxn.r1 (insert Rxn.r2 (insert Rxn.r3 ∅))

/-- **A sum over the reaction set.** -/
lemma sum_eq_sum_allRxns (f : Rxn → ℝ) : (∑ r, f r) = ∑ r ∈ allRxns, f r := by
  have h : (Finset.univ : Finset Rxn) = allRxns := rfl
  rw [h]

/-- The reactions of the example: the deficiency-one module `0 → A`, `0 → B`, `A + B → 0`. -/
def reaction : Rxn → Reaction Species
  | .r1 => { source := c0, target := cA }
  | .r2 => { source := c0, target := cB }
  | .r3 => { source := cAB, target := c0 }

/-- The example network. -/
abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- **The sum over the two species of the example.** -/
lemma sum_species (f : Species → ℝ) : ∑ s, f s = f .A + f .B := by
  have huniv : (Finset.univ : Finset Species) = {Species.A, Species.B} := by
    ext s
    cases s <;> simp
  show Finset.univ.sum f = _
  rw [huniv]
  simp [Finset.sum_insert, Finset.sum_singleton]

/-- **The pairing of the zero complex vanishes.** -/
lemma pairing_c0 (ν : Species → ℝ) : CRNT.complexPairing c0 ν = 0 := by
  rw [CRNT.complexPairing, sum_species]
  simp [c0]

/-- **The pairing of `A + B` is the sum of the pairings of `A` and `B`.** -/
lemma pairing_cAB (ν : Species → ℝ) : CRNT.complexPairing cAB ν = ν .A + ν .B := by
  rw [CRNT.complexPairing, sum_species]
  simp [cAB]
/-- The log-ratio of the example: `μ = (1, −1)`. -/
def μ : Species → ℝ := fun s => match s with | .A => 1 | .B => -1

/-- A second log-ratio, `μ' = (1, 0)`, used to show that the degenerate data fails the
within-class realization condition. -/
def μ' : Species → ℝ := fun s => match s with | .A => 1 | .B => 0

/-- **Every source of the example pairs with `μ` at `0`.** -/
lemma pairing_source (r : Rxn) : CRNT.complexPairing (N.reaction r).source μ = 0 := by
  cases r with
  | r1 => simp [reaction, pairing_c0]
  | r2 => simp [reaction, pairing_c0]
  | r3 => simp [reaction, pairing_cAB, μ]

/-- **The source of the third reaction pairs with `μ'` at `1`.** -/
lemma pairing_source_r3 : CRNT.complexPairing (N.reaction Rxn.r3).source μ' = 1 := by
  simp [reaction, pairing_cAB, μ']

/-- **The third reaction is not colinear with the first.** -/
lemma not_colinear_r3_r1 : ¬ N.SameLine Rxn.r3 Rxn.r1 := by
  intro h
  obtain ⟨a, ha⟩ := h.1
  have hA := congrFun ha Species.A
  have hB := congrFun ha Species.B
  simp [N, reaction, c0, cA, cAB, reactionVector_apply] at hA hB
  linarith

/-- **The third reaction is not colinear with the second.** -/
lemma not_colinear_r3_r2 : ¬ N.SameLine Rxn.r3 Rxn.r2 := by
  intro h
  obtain ⟨a, ha⟩ := h.1
  have hA := congrFun ha Species.A
  have hB := congrFun ha Species.B
  simp [N, reaction, c0, cB, cAB, reactionVector_apply] at hA hB
  linarith

/-- **The run's discrete data**: `M ≡ 0` and every reaction on the middle shelf.  This is the
*degenerate* data of the old verdict: `M` is identically zero and the shelving is the
sign-based one. -/
def degenerateData : N.ADAData :=
  { M := fun _ => 0
    M_colinear := fun _ _ _ => rfl
    shelf := fun _ => Shelf.middle }

/-- **The degenerate data meets the shelf-versus-`M` constraints** at the log-ratio `μ`: every
source of the example pairs with `μ` at `0 = M`. -/
theorem degenerateData_imposes : degenerateData.imposes μ := by
  intro r
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact absurd h (by simp [degenerateData])
  · intro _
    show CRNT.complexPairing (N.reaction r).source μ = degenerateData.M r
    rw [pairing_source r]
    rfl
  · intro h
    exact absurd h (by simp [degenerateData])

/-- **The degenerate data meets the within-class conditions** at the log-ratio `μ`: every class
value is `0`, and every source of the example pairs with `μ` at `0`. -/
theorem degenerateData_withinClass : N.WithinClassConditions degenerateData μ := by
  refine ⟨?_, ?_⟩
  · intro r
    exact ⟨r, sameLine_refl N r, by rw [pairing_source r]; rfl⟩
  · intro r r' h
    exact colinear_pairing_sign_agrees h μ

/-- **The degenerate data meets the coplanar ordering**: all class values are equal. -/
theorem degenerateData_coplanarOrder : N.CoplanarMOrder degenerateData :=
  coplanarMOrder_of_zeroM N degenerateData (fun _ => rfl)

/-- **The flux of the example**: the unit flux on every reaction. -/
def α : Rxn → ℝ := fun _ => 1

/-- **The flux is strictly positive.** -/
lemma α_pos : ∀ r : Rxn, 0 < α r := by
  intro r
  simp [α]

/-- **The flux balance at the lower state.** -/
lemma lower_balance : ∀ s : Species, ∑ r, α r * N.reactionVector r s = 0 := by
  intro s
  rw [sum_eq_sum_allRxns]
  cases s with
  | A =>
      simp [allRxns, Finset.sum_insert, Finset.sum_singleton, α, N, reaction, c0, cA, cB, cAB,
        reactionVector_apply]
  | B =>
      simp [allRxns, Finset.sum_insert, Finset.sum_singleton, α, N, reaction, c0, cA, cB, cAB,
        reactionVector_apply]

/-- **The flux balance at the upper state**: every source of the example pairs with `μ` at `0`,
so the upper balance is the lower balance. -/
lemma upper_balance : ∀ s : Species, ∑ r, α r * Real.exp (complexPairing (N.reaction r).source μ) *
    N.reactionVector r s = 0 := by
  intro s
  rw [sum_eq_sum_allRxns]
  have hexp : ∀ r : Rxn, Real.exp (complexPairing (N.reaction r).source μ) = 1 := by
    intro r
    have h := pairing_source r
    rw [complexPairing_eq] at h
    rw [h, Real.exp_zero]
  calc
    ∑ r ∈ allRxns, α r * Real.exp (complexPairing (N.reaction r).source μ) *
        N.reactionVector r s
        = ∑ r ∈ allRxns, α r * 1 * N.reactionVector r s := by
          refine Finset.sum_congr rfl fun r _ => ?_
          rw [hexp r]
    _ = ∑ r ∈ allRxns, α r * N.reactionVector r s := by
          refine Finset.sum_congr rfl fun r _ => ?_
          ring
    _ = 0 := by
          cases s with
          | A =>
              simp [allRxns, Finset.sum_insert, Finset.sum_singleton, α, N, reaction, c0, cA, cB,
                cAB, reactionVector_apply]
          | B =>
              simp [allRxns, Finset.sum_insert, Finset.sum_singleton, α, N, reaction, c0, cA, cB,
                cAB, reactionVector_apply]

/-- The sign-compatible stoichiometric vector of the example: `σ = μ = (1, −1)`, the reaction
vector of `r₁` minus that of `r₂`. -/
def σ : Species → ℝ := μ

/-- **The sign-compatible vector of the example lies in the stoichiometric subspace.** -/
lemma mem_stoichSubspace : σ ∈ N.stoichSubspace := by
  have h1 : N.reactionVector Rxn.r1 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have h2 : N.reactionVector Rxn.r2 ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace _
  have hsum : N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2 ∈ N.stoichSubspace :=
    N.stoichSubspace.sub_mem h1 h2
  have heq : σ = N.reactionVector Rxn.r1 - N.reactionVector Rxn.r2 := by
    funext s
    cases s <;> simp [σ, μ, N, reaction, c0, cA, cB, reactionVector_apply]
  rw [heq]
  exact hsum

/-- **The log-ratio of the example is sign compatible with the stoichiometric subspace.** -/
lemma signCompatible : N.SignCompatibleWithStoich μ :=
  ⟨σ, mem_stoichSubspace, sameSign_refl σ⟩

/-- **The strengthened Advanced Deficiency Algorithm verdict for the example.**  The run is the
degenerate data (`M ≡ 0`, all reactions on the middle shelf) and the flux is the unit flux; the
within-class conditions and the coplanar ordering are met. -/
theorem adaAffirmsCapacityStrong : N.ADAAffirmsCapacityStrong := by
  refine ⟨degenerateData, μ, α, ?_, signCompatible, degenerateData_imposes,
    degenerateData_withinClass, degenerateData_coplanarOrder, α_pos, lower_balance, upper_balance⟩
  intro h
  have := congrFun h Species.A
  simp [μ] at this

/-- **The example has the capacity for multiple positive steady states.** -/
theorem hasCapacity : N.HasMultistationarityCapacity :=
  N.ADAAffirmsCapacityStrong_hasCapacity adaAffirmsCapacityStrong

/-- **The example satisfies the old verdict as well**: the strengthened verdict implies it. -/
theorem adaAffirmsCapacity : N.ADAAffirmsCapacity :=
  adaAffirmsCapacity_of_adaAffirmsCapacityStrong adaAffirmsCapacityStrong

/-- **The degenerate data fails the within-class conditions** at the log-ratio `μ' = (1, 0)`:
the third reaction's source pairs at `1`, and no reaction of its (singleton) colinearity class
pairs at `0`, so the class value `M = 0` is not realized in the class.  The within-class layer
of Ji §1.7 is therefore a *genuine* extra constraint on the run's data: it is not met by the
degenerate choice `M ≡ 0` in general. -/
theorem degenerateData_fails_withinClass :
    ¬ N.WithinClassConditions degenerateData μ' := by
  rintro ⟨hreal, _⟩
  obtain ⟨r', hline, hp⟩ := hreal Rxn.r3
  rcases r' with _ | _ | _
  · exact absurd hline (not_colinear_r3_r1)
  · exact absurd hline (not_colinear_r3_r2)
  · have hz : CRNT.complexPairing (N.reaction Rxn.r3).source μ' = 0 := by
      rw [hp]
      rfl
    have h1 := pairing_source_r3
    linarith


/-! ### A network whose old verdict holds but whose strengthened verdict fails -/

/-- The reaction channels of the single-reaction network `0 → A`. -/
inductive SingleRxn
  | r1
  deriving DecidableEq, Repr

instance : Fintype SingleRxn where
  elems := {SingleRxn.r1}
  complete := by
    intro r
    cases r with
    | r1 => simp

/-- The reaction set of the single-reaction network. -/
def allSingleRxns : Finset SingleRxn := insert SingleRxn.r1 ∅

/-- **A sum over the reaction set** of the single-reaction network. -/
lemma sum_eq_sum_allSingleRxns (f : SingleRxn → ℝ) : (∑ r, f r) = ∑ r ∈ allSingleRxns, f r := by
  have h : (Finset.univ : Finset SingleRxn) = allSingleRxns := rfl
  rw [h]

/-- The single reaction of the network: `0 → A`. -/
def singleReaction : SingleRxn → Reaction Species
  | .r1 => { source := c0, target := cA }

/-- The single-reaction network. -/
abbrev Nsingle : Network Species :=
  { R := SingleRxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := singleReaction }

/-- The log-ratio of the single-reaction network: the reaction vector `A` itself. -/
def singleMu : Species → ℝ := fun s => match s with | .A => 1 | .B => 0

/-- **The log-ratio of the single-reaction network is nonzero.** -/
lemma singleMu_ne_zero : singleMu ≠ 0 := by
  intro h
  have := congrFun h Species.A
  simp [singleMu] at this

/-- **The log-ratio of the single-reaction network lies in its stoichiometric subspace**: it is
the reaction vector of its only reaction. -/
lemma singleMu_mem_stoichSubspace : singleMu ∈ Nsingle.stoichSubspace := by
  have h : singleMu = Nsingle.reactionVector SingleRxn.r1 := by
    funext s
    cases s <;> simp [singleMu, Nsingle, singleReaction, c0, cA, reactionVector_apply]
  rw [h]
  exact Nsingle.reactionVector_mem_stoichSubspace _

/-- **The single-reaction network satisfies the old verdict**: it has a nonzero, sign-compatible
log-ratio, so `N.ADAAffirmsCapacity` holds (and by
`CRNT.Network.adaAffirmsCapacity_iff_exists_signCompatible` this is *equivalent* to mere sign
compatibility). -/
theorem single_adaAffirmsCapacity : Nsingle.ADAAffirmsCapacity := by
  refine ⟨{ M := fun _ => 0, M_colinear := fun _ _ _ => rfl, shelf := fun _ => Shelf.middle },
    singleMu, singleMu_ne_zero, ⟨singleMu, singleMu_mem_stoichSubspace, sameSign_refl singleMu⟩, ?_⟩
  intro r
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact absurd h (by simp)
  · intro _
    show CRNT.complexPairing (Nsingle.reaction r).source singleMu = 0
    rw [CRNT.complexPairing, sum_species]
    simp [singleReaction, c0]
  · intro h
    exact absurd h (by simp)

/-- **Mere sign compatibility does not give the capacity.**  The single-reaction network has a
nonzero sign-compatible log-ratio (`singleMu`), but no capacity: the flux balance at the lower
state forces the flux of its only reaction to vanish.  This is the semantic counterpart of
`ADAAffirmsCapacityStrong_ne_exists_signCompatible`. -/
theorem signCompatible_ne_hasCapacity : ¬ Nsingle.HasMultistationarityCapacity := by
  intro h
  obtain ⟨α, _, _, hα, _, _, _, hflux, _⟩ :=
    (Nsingle.hasMultistationarityCapacity_iff_flux_sign).1 h
  have h := hflux Species.A
  rw [sum_eq_sum_allSingleRxns] at h
  simp [allSingleRxns, Finset.sum_singleton, Nsingle, singleReaction, c0, cA,
    reactionVector_apply] at h
  exact absurd h (ne_of_gt (hα SingleRxn.r1))

/-- **The single-reaction network does not satisfy the strengthened verdict.**  Its lower flux
balance forces the flux of its only reaction to vanish, so there is no strictly positive flux:
the strengthened verdict, which demands the flux certificate, fails.  This is the sense in which
the strengthened verdict is *strictly stronger* than mere sign compatibility. -/
theorem not_adaAffirmsCapacityStrong : ¬ Nsingle.ADAAffirmsCapacityStrong := by
  rintro ⟨_, _, α, _, _, _, _, _, hα, hlb, _⟩
  have h := hlb Species.A
  rw [sum_eq_sum_allSingleRxns] at h
  simp [allSingleRxns, Finset.sum_singleton, Nsingle, singleReaction, c0, cA,
    reactionVector_apply] at h
  exact absurd h (ne_of_gt (hα SingleRxn.r1))

end ADACoplanarExample

/-! ### The strengthened verdict is strictly stronger than mere sign compatibility -/

/-- **The strengthened verdict is strictly stronger than mere sign compatibility.**  There is a
network which admits a nonzero sign-compatible log-ratio — so that the old verdict
`N.ADAAffirmsCapacity` holds, which by
`CRNT.Network.adaAffirmsCapacity_iff_exists_signCompatible` is *equivalent* to mere sign
compatibility — but which does **not** satisfy the strengthened verdict: the strengthened
verdict demands the flux certificate, and this network admits none.  Together with
`ADAAffirmsCapacityStrong_hasCapacity` (the strengthened verdict implies the multistationarity
capacity) this exhibits the restored content of the combinatorial verdict. -/
theorem ADAAffirmsCapacityStrong_ne_exists_signCompatible :
    ∃ (N : Network ADACoplanarExample.Species),
      N.ADAAffirmsCapacity ∧ ¬ N.ADAAffirmsCapacityStrong :=
  ⟨ADACoplanarExample.Nsingle, ADACoplanarExample.single_adaAffirmsCapacity,
    ADACoplanarExample.not_adaAffirmsCapacityStrong⟩

/-! ### The within-class sign comparison: what it does and does not say -/

namespace SourcePairingExample

/-- The species of the counterexample: `{A}`. -/
inductive Species
  | A
  deriving DecidableEq, Repr

instance : Fintype Species where
  elems := {Species.A}
  complete := by
    intro s
    cases s with
    | A => simp

open Species

/-- The zero complex. -/
def c0 : Complex Species := fun _ => 0

/-- The complex `A`. -/
def cA : Complex Species := fun _ => 1

/-- The complex `2A`. -/
def c2A : Complex Species := fun _ => 2

/-- The reaction channels of the counterexample. -/
inductive Rxn
  | r1 | r2
  deriving DecidableEq, Repr

instance : Fintype Rxn where
  elems := {Rxn.r1, Rxn.r2}
  complete := by
    intro r
    cases r with
    | r1 => simp
    | r2 => simp

/-- The reactions of the counterexample: `0 → A` and `A → 2A`.  Their reaction vectors coincide,
so the two reactions are colinear. -/
def reaction : Rxn → Reaction Species
  | .r1 => { source := c0, target := cA }
  | .r2 => { source := cA, target := c2A }

/-- The counterexample network. -/
abbrev N : Network Species :=
  { R := Rxn, decEqR := inferInstance, fintypeR := inferInstance, reaction := reaction }

/-- **The sum over the single species of the counterexample.** -/
lemma sum_species (f : Species → ℝ) : ∑ s, f s = f .A := by
  have huniv : (Finset.univ : Finset Species) = {Species.A} := by
    ext s
    cases s with
    | A => simp
  show Finset.univ.sum f = _
  rw [huniv]
  simp [Finset.sum_singleton]

end SourcePairingExample

/-- **The source pairings of two reactions of one colinearity class need not have the same
sign.**  Colinearity constrains the *difference* of the pairings — the `μ`-rate — and not the
pairings themselves: the reactants of two collinear reactions may be different complexes.  On
the network `0 → A`, `A → 2A` (whose two reaction vectors coincide) with the log-ratio `μ = 1`,
the first reaction's source pairs at `0` and the second's at `1`.  This is why the within-class
sign comparison of Ji §1.7 is stated for the `μ`-rates
(`colinear_pairing_sign_agrees`). -/
theorem colinear_source_pairings_need_not_agree :
    ∃ (N : Network SourcePairingExample.Species) (r r' : N.R)
      (μ : SourcePairingExample.Species → ℝ),
      N.ColinearReactions r r' ∧
        SignType.sign (CRNT.complexPairing (N.reaction r).source μ) ≠
          SignType.sign (CRNT.complexPairing (N.reaction r').source μ) := by
  refine ⟨SourcePairingExample.N, SourcePairingExample.Rxn.r1, SourcePairingExample.Rxn.r2,
    (fun _ => 1), ?_, ?_⟩
  · refine ⟨1, ?_⟩
    funext s
    simp [SourcePairingExample.N, SourcePairingExample.reaction, SourcePairingExample.c0,
      SourcePairingExample.cA, SourcePairingExample.c2A, reactionVector_apply]
    ring
  · have h1 : CRNT.complexPairing
        (SourcePairingExample.N.reaction SourcePairingExample.Rxn.r1).source (fun _ => 1) = 0 := by
      rw [CRNT.complexPairing, SourcePairingExample.sum_species]
      simp [SourcePairingExample.reaction, SourcePairingExample.c0]
    have h2 : CRNT.complexPairing
        (SourcePairingExample.N.reaction SourcePairingExample.Rxn.r2).source (fun _ => 1) = 1 := by
      rw [CRNT.complexPairing, SourcePairingExample.sum_species]
      simp [SourcePairingExample.reaction, SourcePairingExample.cA]
    rw [h1, h2]
    simp

/-! ### The axioms used by the principal declarations -/

#print axioms colinear_pairing_sign_agrees
#print axioms colinear_pairingDifference_sign_agrees
#print axioms coplanar_rate_relation
#print axioms ADAAffirmsCapacityStrong_hasCapacity
#print axioms adaAffirmsCapacity_of_adaAffirmsCapacityStrong
#print axioms ADAAffirmsCapacityStrong_ne_exists_signCompatible
#print axioms colinear_source_pairings_need_not_agree
#print axioms ADACoplanarExample.adaAffirmsCapacityStrong
#print axioms ADACoplanarExample.hasCapacity
#print axioms ADACoplanarExample.degenerateData_fails_withinClass
#print axioms ADACoplanarExample.not_adaAffirmsCapacityStrong
#print axioms ADACoplanarExample.signCompatible_ne_hasCapacity

end Network

end CRNT
