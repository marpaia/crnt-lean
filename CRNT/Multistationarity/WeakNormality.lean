import CRNT.Multistationarity.Normality
import CRNT.Kinetics.MassActionJacobian
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Weak normality and network nondegeneracy

Shinar--Feinberg weak normality replaces the special source vector
`η_r (source r ∘ q)` appearing in normality by an arbitrary nonnegative vector `p_r`
whose support is exactly the source support.  The corresponding operator

`T̄ σ = Σ_r (p_r · σ) ν_r`

must be nonsingular on the stoichiometric subspace.

The central classical result is that weak normality is exactly kinetic nondegeneracy:
there exists a differentiably monotonic kinetics and a positive composition at which the
species-formation derivative is nonsingular on the stoichiometric subspace.  A network
that fails this condition is necessarily discordant.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A nonnegative source-influence vector whose support is exactly the support of the
source complex. -/
structure SourceInfluence (y : Complex S) where
  vec : S → ℝ
  nonneg : ∀ s, 0 ≤ vec s
  pos_iff_source : ∀ s, 0 < vec s ↔ y s ≠ 0

/-- One source-influence vector for every reaction. -/
structure SourceInfluenceFamily (N : Network S) where
  influence : ∀ r : N.R, SourceInfluence (N.reaction r).source

/-- Weak-normality operator `T̄`. -/
noncomputable def weakNormalityOperator (N : Network S)
    (P : N.SourceInfluenceFamily) : (S → ℝ) →ₗ[ℝ] (S → ℝ) where
  toFun := fun σ => ∑ r : N.R,
    (∑ s : S, (P.influence r).vec s * σ s) • N.reactionVector r
  map_add' := by
    intro σ τ
    ext s
    -- `ring` cannot see into a `Finset.sum`; distribute, recombine, then compare termwise
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, add_mul]
  map_smul' := by
    intro c σ
    ext s
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Finset.mul_sum,
      RingHom.id_apply]
    refine Finset.sum_congr rfl fun r _ => ?_
    have h : (∑ i, (P.influence r).vec i * (c * σ i))
        = c * ∑ i, (P.influence r).vec i * σ i := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h]
    ring

/-- Weak-normality operator preserves the stoichiometric subspace. -/
theorem weakNormalityOperator_mem_stoichSubspace (N : Network S)
    (P : N.SourceInfluenceFamily) (σ : S → ℝ) :
    N.weakNormalityOperator P σ ∈ N.stoichSubspace := by
  unfold weakNormalityOperator
  exact Submodule.sum_mem _ fun r _ =>
    Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)

/-- Restriction to the stoichiometric subspace. -/
noncomputable def weakNormalityOperatorOnStoich (N : Network S)
    (P : N.SourceInfluenceFamily) : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace :=
  (N.weakNormalityOperator P).domRestrict N.stoichSubspace |>.codRestrict
    N.stoichSubspace (fun σ => N.weakNormalityOperator_mem_stoichSubspace P σ)

/-- A weak-normality certificate. -/
structure WeakNormalWitness (N : Network S) where
  influences : N.SourceInfluenceFamily
  nonsingular : Function.Injective (N.weakNormalityOperatorOnStoich influences)

/-- Weakly normal network. -/
def WeaklyNormal (N : Network S) : Prop := Nonempty N.WeakNormalWitness

/-- Ordinary normality implies weak normality by taking
`p_r = η_r source(r) ∘ q`. -/
theorem weaklyNormal_of_normal (N : Network S) (h : N.Normal) : N.WeaklyNormal := by
  rcases h with ⟨W⟩
  let P : N.SourceInfluenceFamily := {
    influence := fun r => {
      vec := fun s => W.reactionWeights.weight r *
        ((N.reaction r).source s : ℝ) * W.speciesWeights.weight s
      nonneg := fun s => by
        exact mul_nonneg (mul_nonneg (W.reactionWeights.positive r).le
          (Nat.cast_nonneg _)) (W.speciesWeights.positive s).le
      pos_iff_source := fun s => by
        constructor
        · intro hp hzero
          simp [hzero] at hp
        · intro hs
          exact mul_pos (mul_pos (W.reactionWeights.positive r)
            (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs)))
            (W.speciesWeights.positive s) } }
  refine ⟨⟨P, ?_⟩⟩
  -- No simp set can align these: they differ by scalar rearrangement *inside* a
  -- `codRestrict`.  Prove the two operators equal as linear maps, then transport
  -- injectivity across that equality.
  have hop : N.weakNormalityOperatorOnStoich P
      = N.normalityOperatorOnStoich W.speciesWeights W.reactionWeights := by
    refine LinearMap.ext fun σ => Subtype.ext ?_
    simp only [weakNormalityOperatorOnStoich, normalityOperatorOnStoich,
      LinearMap.codRestrict_apply, LinearMap.domRestrict_apply,
      weakNormalityOperator, normalityOperator, P, weightedComplexPairing]
    refine Finset.sum_congr rfl fun r _ => ?_
    congr 1
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hop]
  exact W.nonsingular

/-- Weakly reversible networks are weakly normal. -/
theorem weaklyNormal_of_weaklyReversible (N : Network S) (hwr : N.WeaklyReversible) :
    N.WeaklyNormal :=
  N.weaklyNormal_of_normal (N.normal_of_weaklyReversible hwr)

/-- Linear functional represented by a source-influence vector. -/
noncomputable def rateDerivativeFunctional {N : Network S}
    (P : N.SourceInfluenceFamily) (r : N.R) :
    (S → ℝ) →ₗ[ℝ] ℝ where
  toFun := fun σ => ∑ s : S, (P.influence r).vec s * σ s
  map_add' := by
    intro σ τ
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro c σ
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- Local differentiably-monotonic rate derivative data.  Instead of depending on a
particular Fréchet-derivative representation, we record every directional derivative:
for direction `h`, the derivative of reaction `r` along `x+t h` is `p_r · h`.
The source-influence axioms make these gradients nonnegative and supported exactly on
the reactant support. -/
-- `N` is NOT in this file's `variable` block, so writing it bare here made it an
-- `autoImplicit` of unknown type, which is why `Fintype ?m` got stuck.  Bind it.
structure DifferentiablyMonotonicAt {N : Network S} (K : N.Kinetics)
    (x : Concentration S) where
  influences : N.SourceInfluenceFamily
  directionalDerivative : ∀ (r : N.R) (h : S → ℝ),
    HasDerivAt (fun t : ℝ => K.rate r (x + t • h))
      (rateDerivativeFunctional (N := N) influences r h) 0

/-- A kinetic nondegeneracy witness at one positive composition. -/
structure KineticNondegeneracyWitness (N : Network S) where
  kinetics : Kinetics N
  point : Concentration S
  positive : point.Positive
  differentiablyMonotonic : DifferentiablyMonotonicAt kinetics point
  /-- The species-formation derivative restricted to the stoichiometric subspace is
  nonsingular. Under the directional-derivative identity above this derivative is exactly
  the weak-normality operator. -/
  nonsingular : Function.Injective
    (N.weakNormalityOperatorOnStoich differentiablyMonotonic.influences)

/-- Network nondegeneracy in the differentiably-monotonic sense. -/
def Nondegenerate (N : Network S) : Prop := Nonempty N.KineticNondegeneracyWitness

private noncomputable def realizeGate (p z : ℝ) : ℝ :=
  (1 + (z - 1)^3) * Real.exp (p * (z - 1))

private lemma realizeGate_zero (p : ℝ) : realizeGate p 0 = 0 := by
  norm_num [realizeGate]

private lemma realizeGate_one (p : ℝ) : realizeGate p 1 = 1 := by
  simp [realizeGate]

private lemma realizeGate_nonneg {p z : ℝ} (hz : 0 ≤ z) :
    0 ≤ realizeGate p z := by
  have hsub : (-1 : ℝ) ≤ z - 1 := by linarith
  have hpw : (-1 : ℝ)^3 ≤ (z - 1)^3 :=
    (show Odd 3 by decide).pow_le_pow.mpr hsub
  have hbase : 0 ≤ 1 + (z - 1)^3 := by norm_num at hpw ⊢; linarith
  exact mul_nonneg hbase (Real.exp_pos _).le

private lemma realizeGate_mono {p x y : ℝ} (hp : 0 ≤ p) (hx : 0 ≤ x)
    (hxy : x ≤ y) : realizeGate p x ≤ realizeGate p y := by
  have hsub : x - 1 ≤ y - 1 := by linarith
  have hpw : (x - 1)^3 ≤ (y - 1)^3 :=
    (show Odd 3 by decide).pow_le_pow.mpr hsub
  have hbase : 1 + (x - 1)^3 ≤ 1 + (y - 1)^3 := by linarith
  have hy : 0 ≤ y := hx.trans hxy
  have hbaseY0 : 0 ≤ 1 + (y - 1)^3 := by
    have hsubY : (-1 : ℝ) ≤ y - 1 := by linarith
    have hpwY : (-1 : ℝ)^3 ≤ (y - 1)^3 :=
      (show Odd 3 by decide).pow_le_pow.mpr hsubY
    norm_num at hpwY ⊢
    linarith
  have hexp : Real.exp (p * (x - 1)) ≤ Real.exp (p * (y - 1)) := by
    rw [Real.exp_le_exp]
    exact mul_le_mul_of_nonneg_left hsub hp
  exact mul_le_mul hbase hexp (Real.exp_pos _).le hbaseY0

private lemma realizeGate_hasDerivAt (p : ℝ) : HasDerivAt (realizeGate p) p 1 := by
  have hid : HasDerivAt (fun z : ℝ => z) 1 1 := hasDerivAt_id' 1
  have hsub : HasDerivAt (fun z : ℝ => z - 1) 1 1 := by
    simpa using hid.sub_const 1
  have hpw : HasDerivAt (fun z : ℝ => (z - 1)^3) 0 1 := by
    simpa using! hsub.pow 3
  have hbase : HasDerivAt (fun z : ℝ => 1 + (z - 1)^3) 0 1 := by
    exact hpw.const_add 1
  have hlin : HasDerivAt (fun z : ℝ => p * (z - 1)) p 1 := by
    simpa using hsub.const_mul p
  have hexp : HasDerivAt (fun z : ℝ => Real.exp (p * (z - 1))) p 1 := by
    simpa using! hlin.exp
  simpa [realizeGate] using! hbase.mul hexp

private lemma realizeGate_line_hasDerivAt (p h : ℝ) :
    HasDerivAt (fun t : ℝ => realizeGate p (1 + t * h)) (p * h) 0 := by
  have hline : HasDerivAt (fun t : ℝ => 1 + t * h) h 0 := by
    have ht : HasDerivAt (fun t : ℝ => t * h) h 0 := by
      simpa using (hasDerivAt_id' (0 : ℝ)).mul_const h
    exact ht.const_add 1
  have hout : HasDerivAt (realizeGate p) p (1 + (0 : ℝ) * h) := by
    simpa using realizeGate_hasDerivAt p
  exact hout.comp 0 hline

private noncomputable def realizedKinetics (N : Network S)
    (P : N.SourceInfluenceFamily) : N.Kinetics where
  rate := fun r x => ∏ s ∈ (N.reaction r).source.support,
    realizeGate ((P.influence r).vec s) (x s)
  rate_nonneg := by
    intro r x hx
    exact Finset.prod_nonneg fun s hs => realizeGate_nonneg (hx s)
  rate_vanishing := by
    intro r x s hs hxs
    apply Finset.prod_eq_zero (show s ∈ (N.reaction r).source.support by
      simp [Complex.support, hs])
    simpa [hxs] using realizeGate_zero ((P.influence r).vec s)
  rate_supportDep := by
    intro r x y hxy
    apply Finset.prod_congr rfl
    intro s hs
    rw [hxy s]
    simpa [Complex.support] using hs
  rate_mono := by
    intro r x hx y hy hxy
    apply Finset.prod_le_prod₀
    · intro s hs
      exact realizeGate_nonneg (hx s)
    · intro s hs
      exact realizeGate_mono ((P.influence r).nonneg s) (hx s) (hxy s)

private noncomputable def realizedKinetics_differentiablyMonotonic
    (N : Network S) (P : N.SourceInfluenceFamily) :
    DifferentiablyMonotonicAt (realizedKinetics N P) (fun _ => 1) := by
  refine ⟨P, ?_⟩
  intro r h
  let u := (N.reaction r).source.support
  let f : S → ℝ → ℝ := fun s t => realizeGate ((P.influence r).vec s) (1 + t * h s)
  have hf : ∀ s ∈ u, HasDerivAt (f s) ((P.influence r).vec s * h s) 0 := by
    intro s hs
    exact realizeGate_line_hasDerivAt _ _
  have hprod := HasDerivAt.finsetProd hf
  have hderiv : (∑ s ∈ u, (∏ j ∈ u.erase s, f j 0) •
      ((P.influence r).vec s * h s)) =
      ∑ s : S, (P.influence r).vec s * h s := by
    have hout : ∀ s : S, (N.reaction r).source s = 0 → (P.influence r).vec s = 0 := by
      intro s hs
      have hnpos : ¬ 0 < (P.influence r).vec s := by
        intro hp
        exact ((P.influence r).pos_iff_source s |>.mp hp) hs
      exact le_antisymm (not_lt.mp hnpos) ((P.influence r).nonneg s)
    simp only [f, realizeGate_one, one_smul, Finset.prod_const_one]
    simp only [u, Complex.support]
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro s hs
    by_cases hsrc : (N.reaction r).source s ≠ 0
    · simp [hsrc, f, realizeGate_one]
    · have hz := hout s (not_ne_iff.mp hsrc)
      simp [hsrc, hz]
  have hd : (∑ s ∈ u, (∏ j ∈ u.erase s, f j 0) •
      ((P.influence r).vec s * h s)) = rateDerivativeFunctional P r h := by
    rw [hderiv]
    rfl
  have hp := hprod.congr_deriv hd
  refine hp.congr_of_eventuallyEq (Filter.Eventually.of_forall ?_)
  intro t
  simp [realizedKinetics, f, u, Pi.add_apply, Pi.smul_apply, smul_eq_mul]


/-- **Weak normality = nondegeneracy.** -/
theorem weaklyNormal_iff_nondegenerate (N : Network S) :
    N.WeaklyNormal ↔ N.Nondegenerate := by
  constructor
  · rintro ⟨W⟩
    let x : Concentration S := fun _ => 1
    let K : N.Kinetics := realizedKinetics N W.influences
    let hdiff : DifferentiablyMonotonicAt K x :=
      realizedKinetics_differentiablyMonotonic N W.influences
    refine ⟨⟨K, x, ?_, hdiff, ?_⟩⟩
    · intro s
      exact one_pos
    · simpa [hdiff, realizedKinetics_differentiablyMonotonic] using W.nonsingular
  · rintro ⟨W⟩
    exact ⟨⟨W.differentiablyMonotonic.influences, W.nonsingular⟩⟩
/-- Degenerate networks are exactly networks that are not weakly normal. -/
def Degenerate (N : Network S) : Prop := ¬ N.Nondegenerate

/-- **Every degenerate network is discordant.** -/
theorem discordant_of_degenerate (N : Network S) (hdeg : N.Degenerate) :
    N.Discordant := by
  classical
  simp only [Degenerate] at hdeg
  rw [← N.weaklyNormal_iff_nondegenerate] at hdeg
  let P : N.SourceInfluenceFamily := {
    influence := fun r => {
      vec := fun s => ((N.reaction r).source s : ℝ)
      nonneg := fun s => Nat.cast_nonneg _
      pos_iff_source := fun s => by
        simpa using (Nat.cast_pos : 0 < ((N.reaction r).source s : ℝ) ↔
          0 < (N.reaction r).source s).trans Nat.pos_iff_ne_zero } }
  have hnotinj : ¬ Function.Injective (N.weakNormalityOperatorOnStoich P) := by
    intro hinj
    exact hdeg ⟨⟨P, hinj⟩⟩
  have hkerne : LinearMap.ker (N.weakNormalityOperatorOnStoich P) ≠ ⊥ := by
    intro hk
    exact hnotinj ((LinearMap.ker_eq_bot).mp hk)
  obtain ⟨σ, hσker, hσne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hkerne
  let α : N.R → ℝ := fun r => ∑ s : S, ((N.reaction r).source s : ℝ) * σ.1 s
  have hker : N.InKerL α := by
    have hop : N.weakNormalityOperatorOnStoich P σ = 0 := LinearMap.mem_ker.mp hσker
    have hv := congrArg Subtype.val hop
    simpa [InKerL, weakNormalityOperatorOnStoich, weakNormalityOperator, P, α] using hv
  have hsig_ne : (σ.1 : S → ℝ) ≠ 0 := by
    intro hz
    apply hσne
    apply Subtype.ext
    exact hz
  rw [discordant_iff_exists_witness]
  refine ⟨α, σ.1, ?_⟩
  refine ⟨hker, σ.2, hsig_ne, ?_, ?_⟩
  · intro r hα
    rcases lt_or_gt_of_ne hα with hneg | hpos
    · have hex : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ σ.1 s < 0 := by
        by_contra hn
        push_neg at hn
        have hsum : 0 ≤ α r := by
          dsimp [α]
          apply Finset.sum_nonneg
          intro s _
          by_cases hs : (N.reaction r).source s = 0
          · simp [hs]
          · exact mul_nonneg (Nat.cast_nonneg _) (hn s hs)
        linarith
      obtain ⟨s, hs, hsn⟩ := hex
      refine ⟨s, hs, ?_⟩
      rw [_root_.sign_neg hsn, _root_.sign_neg hneg]
    · have hex : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ 0 < σ.1 s := by
        by_contra hn
        push_neg at hn
        have hsum : α r ≤ 0 := by
          dsimp [α]
          apply Finset.sum_nonpos
          intro s _
          by_cases hs : (N.reaction r).source s = 0
          · simp [hs]
          · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hn s hs)
        linarith
      obtain ⟨s, hs, hsp⟩ := hex
      refine ⟨s, hs, ?_⟩
      rw [_root_.sign_pos hsp, _root_.sign_pos hpos]
  · intro r hα0
    by_cases hall : ∀ s : S, (N.reaction r).source s ≠ 0 → σ.1 s = 0
    · exact Or.inl hall
    · right
      push_neg at hall
      obtain ⟨s0, hs0, hs0ne⟩ := hall
      rcases lt_or_gt_of_ne hs0ne with hs0neg | hs0pos
      · have hexpos : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ 0 < σ.1 s := by
          by_contra hn
          push_neg at hn
          have hnonpos : ∀ s ∈ (Finset.univ : Finset S),
              ((N.reaction r).source s : ℝ) * σ.1 s ≤ 0 := by
            intro s _
            by_cases hs : (N.reaction r).source s = 0
            · simp [hs]
            · exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hn s hs)
          have hstrict : ((N.reaction r).source s0 : ℝ) * σ.1 s0 < 0 :=
            mul_neg_of_pos_of_neg (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs0)) hs0neg
          have hsumneg : (∑ s : S, ((N.reaction r).source s : ℝ) * σ.1 s) < 0 := by
            apply Finset.sum_neg' hnonpos
            exact ⟨s0, Finset.mem_univ s0, hstrict⟩
          dsimp [α] at hα0
          linarith
        obtain ⟨sp, hsp, hsppos⟩ := hexpos
        exact ⟨s0, sp, hs0, hsp, hs0neg, hsppos⟩
      · have hexneg : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ σ.1 s < 0 := by
          by_contra hn
          push_neg at hn
          have hnonneg : ∀ s ∈ (Finset.univ : Finset S),
              0 ≤ ((N.reaction r).source s : ℝ) * σ.1 s := by
            intro s _
            by_cases hs : (N.reaction r).source s = 0
            · simp [hs]
            · exact mul_nonneg (Nat.cast_nonneg _) (hn s hs)
          have hstrict : 0 < ((N.reaction r).source s0 : ℝ) * σ.1 s0 :=
            mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hs0)) hs0pos
          have hsumpos : 0 < (∑ s : S, ((N.reaction r).source s : ℝ) * σ.1 s) := by
            apply Finset.sum_pos' hnonneg
            exact ⟨s0, Finset.mem_univ s0, hstrict⟩
          dsimp [α] at hα0
          linarith
        obtain ⟨sn, hsn, hsnneg⟩ := hexneg
        exact ⟨sn, s0, hsn, hs0, hsnneg, hs0pos⟩

/-- Equivalently, every concordant network is nondegenerate / weakly normal. -/
theorem Concordant.nondegenerate {N : Network S} (h : N.Concordant) :
    N.Nondegenerate := by
  by_contra hdeg
  exact (N.discordant_of_degenerate hdeg) h

-- Generic resolvent helper
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

lemma descent_exists_resolvent_with_bound
    (T : V →ₗ[ℝ] V) (hT : Function.Injective T) (σ : V) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : ℝ, 0 < ε → C * ε < 1 / 2 →
        ∃ χ : V, T χ = σ + ε • χ ∧ ‖χ‖ ≤ 2 * C * ‖σ‖ := by
  let Tc : V →L[ℝ] V := T.toContinuousLinearMap
  have hrange : IsClosed (Set.range Tc) := by
    simpa [Tc, LinearMap.coe_range] using (LinearMap.range T).closed_of_finiteDimensional
  obtain ⟨K, hanti⟩ := Tc.antilipschitz_of_injective_of_isClosed_range hT hrange
  let C : ℝ := (K : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε hε hsmall
  let A : V →ₗ[ℝ] V := T - ε • LinearMap.id
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot]
    apply le_antisymm
    · intro x hx
      have hxA : A x = 0 := LinearMap.mem_ker.mp hx
      have hTx : T x = ε • x := by
        simp only [A, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply] at hxA
        exact sub_eq_zero.mp hxA
      have hboundK : ‖x‖ ≤ (K : ℝ) * ‖T x‖ := by
        have h := hanti.le_mul_dist x 0
        simpa [Tc, dist_eq_norm] using h
      have hKC : (K : ℝ) ≤ C := by dsimp [C]; linarith
      have hboundC : ‖x‖ ≤ C * ‖T x‖ := hboundK.trans (mul_le_mul_of_nonneg_right hKC (norm_nonneg _))
      have hnormTx : ‖T x‖ = ε * ‖x‖ := by
        rw [hTx, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      rw [hnormTx] at hboundC
      have hnormx : ‖x‖ = 0 := by
        have hn : 0 ≤ ‖x‖ := norm_nonneg _
        have hce : C * ε < 1 := lt_trans hsmall (by norm_num)
        nlinarith
      simpa using (norm_eq_zero.mp hnormx)
    · exact bot_le
  have hAsurj : Function.Surjective A := LinearMap.surjective_of_injective hAinj
  obtain ⟨χ, hχ⟩ := hAsurj σ
  refine ⟨χ, ?_, ?_⟩
  · have : T χ - ε • χ = σ := by simpa [A] using hχ
    exact eq_add_of_sub_eq this
  · have hboundK : ‖χ‖ ≤ (K : ℝ) * ‖T χ‖ := by
      have h := hanti.le_mul_dist χ 0
      simpa [Tc, dist_eq_norm] using h
    have hKC : (K : ℝ) ≤ C := by dsimp [C]; linarith
    have hboundC : ‖χ‖ ≤ C * ‖T χ‖ := hboundK.trans (mul_le_mul_of_nonneg_right hKC (norm_nonneg _))
    have heq : T χ = σ + ε • χ := by
      have : T χ - ε • χ = σ := by simpa [A] using hχ
      exact eq_add_of_sub_eq this
    have htri : ‖T χ‖ ≤ ‖σ‖ + ε * ‖χ‖ := by
      rw [heq]
      calc
        ‖σ + ε • χ‖ ≤ ‖σ‖ + ‖ε • χ‖ := norm_add_le _ _
        _ = ‖σ‖ + ε * ‖χ‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hh : ‖χ‖ ≤ C * (‖σ‖ + ε * ‖χ‖) := hboundC.trans (mul_le_mul_of_nonneg_left htri hC.le)
    have hnχ : 0 ≤ ‖χ‖ := norm_nonneg _
    have hnσ : 0 ≤ ‖σ‖ := norm_nonneg _
    nlinarith

lemma descent_exists_resolvent_preserving_sign
    (N : Network S) (T : N.stoichSubspace →ₗ[ℝ] N.stoichSubspace)
    (hT : Function.Injective T) (σ : N.stoichSubspace) (hσne : (σ.1 : S → ℝ) ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ χ : N.stoichSubspace,
      T χ = σ + ε • χ ∧
      ∀ s : S, σ.1 s ≠ 0 →
        SignType.sign ((σ + ε • χ).1 s) = SignType.sign (σ.1 s) := by
  obtain ⟨C, hC, hres⟩ := descent_exists_resolvent_with_bound T hT σ
  have hex : ∃ s : S, σ.1 s ≠ 0 := by
    by_contra hn
    push Not at hn
    apply hσne
    funext s
    exact hn s
  let F : Finset S := Finset.univ.filter fun s => σ.1 s ≠ 0
  have hF : F.Nonempty := by
    obtain ⟨s, hs⟩ := hex
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩⟩
  let G : Finset ℝ := F.image fun s => |σ.1 s|
  have hG : G.Nonempty := hF.image _
  let m : ℝ := G.min' hG
  have hmpos : 0 < m := by
    have hm : m ∈ G := G.min'_mem hG
    rcases Finset.mem_image.mp hm with ⟨s, hsF, hsEq⟩
    have hsne : σ.1 s ≠ 0 := (Finset.mem_filter.mp hsF).2
    calc
      0 < |σ.1 s| := abs_pos.mpr hsne
      _ = G.min' hG := by simpa [m] using hsEq
  have hmle : ∀ s : S, σ.1 s ≠ 0 → m ≤ |σ.1 s| := by
    intro s hs
    apply G.min'_le
    exact Finset.mem_image.mpr ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ s, hs⟩, rfl⟩
  let B : ℝ := 2 * C * ‖σ‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  let a : ℝ := 1 / (2 * C)
  let b : ℝ := m / (B + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hb : 0 < b := by dsimp [b]; positivity
  let q : ℝ := min a b
  have hq : 0 < q := lt_min ha hb
  let ε : ℝ := q / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  have hεa : ε < a := by have := min_le_left a b; dsimp [ε, q]; linarith
  have hεb : ε < b := by have := min_le_right a b; dsimp [ε, q]; linarith
  have hsmall : C * ε < 1 / 2 := by
    have hden : 0 < 2 * C := by positivity
    have hh : ε * (2 * C) < 1 := by
      apply (lt_div_iff₀ hden).mp
      simpa [a, one_div] using hεa
    nlinarith
  obtain ⟨χ, heq, hχbound⟩ := hres ε hε hsmall
  refine ⟨ε, hε, χ, heq, ?_⟩
  intro s hs
  have hBplus : 0 < B + 1 := by linarith
  have hepsB1 : ε * (B + 1) < m := by
    apply (lt_div_iff₀ hBplus).mp
    simpa [b] using hεb
  have hepsB : ε * B < m := by nlinarith
  have hcoord : |χ.1 s| ≤ ‖χ‖ := by
    have h := norm_le_pi_norm χ.1 s
    simpa [Real.norm_eq_abs] using h
  have hpert_le : |ε * χ.1 s| ≤ ε * ‖χ‖ := by
    rw [abs_mul, abs_of_pos hε]
    exact mul_le_mul_of_nonneg_left hcoord hε.le
  have hpertB : ε * ‖χ‖ ≤ ε * B := mul_le_mul_of_nonneg_left hχbound hε.le
  have hpert : |ε * χ.1 s| < |σ.1 s| :=
    lt_of_le_of_lt hpert_le (lt_of_le_of_lt hpertB (lt_of_lt_of_le hepsB (hmle s hs)))
  rcases lt_or_gt_of_ne hs with hsneg | hspos
  · have hdeltaUpper : ε * χ.1 s < |σ.1 s| := (abs_lt.mp hpert).2
    rw [abs_of_neg hsneg] at hdeltaUpper
    have hsumneg : σ.1 s + ε * χ.1 s < 0 := by linarith
    simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
    rw [_root_.sign_neg hsumneg, _root_.sign_neg hsneg]
  · have hdeltaLower : -|σ.1 s| < ε * χ.1 s := (abs_lt.mp hpert).1
    rw [abs_of_pos hspos] at hdeltaLower
    have hsumpos : 0 < σ.1 s + ε * χ.1 s := by linarith
    simp only [Submodule.coe_add, Pi.add_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, smul_eq_mul]
    rw [_root_.sign_pos hsumpos, _root_.sign_pos hspos]

lemma descent_exists_pos_preserving_nonzero_sign
    {ι : Type} [DecidableEq ι] [Fintype ι] (a b : ι → ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ i : ι, a i ≠ 0 →
      SignType.sign (a i + δ * b i) = SignType.sign (a i) := by
  by_cases hnone : ∀ i : ι, a i = 0
  · exact ⟨1, one_pos, fun i hi => (hi (hnone i)).elim⟩
  have hex : ∃ i : ι, a i ≠ 0 := by
    push Not at hnone
    exact hnone
  let F : Finset ι := Finset.univ.filter fun i => a i ≠ 0
  have hF : F.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  let G : Finset ℝ := F.image fun i => |a i|
  have hG : G.Nonempty := hF.image _
  let m : ℝ := G.min' hG
  have hmpos : 0 < m := by
    have hm : m ∈ G := G.min'_mem hG
    rcases Finset.mem_image.mp hm with ⟨i, hiF, hiEq⟩
    have hine : a i ≠ 0 := (Finset.mem_filter.mp hiF).2
    calc
      0 < |a i| := abs_pos.mpr hine
      _ = G.min' hG := by simpa [m] using hiEq
  have hmle : ∀ i : ι, a i ≠ 0 → m ≤ |a i| := by
    intro i hi
    apply G.min'_le
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩, rfl⟩
  let M : ℝ := ∑ i : ι, |b i|
  have hM : 0 ≤ M := Finset.sum_nonneg fun _ _ => abs_nonneg _
  let δ : ℝ := m / (2 * (M + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  refine ⟨δ, hδ, ?_⟩
  intro i hi
  have hbiM : |b i| ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun j _ => abs_nonneg (b j)) (Finset.mem_univ i)
  have hpert : |δ * b i| < |a i| := by
    have hden : 0 < 2 * (M + 1) := by positivity
    have hδM : δ * M < m := by
      dsimp [δ]
      have hfrac : M / (2 * (M + 1)) < 1 := by
        apply (div_lt_one hden).2
        nlinarith
      calc
        m / (2 * (M + 1)) * M = m * (M / (2 * (M + 1))) := by ring
        _ < m * 1 := mul_lt_mul_of_pos_left hfrac hmpos
        _ = m := mul_one _
    calc
      |δ * b i| = δ * |b i| := by rw [abs_mul, abs_of_pos hδ]
      _ ≤ δ * M := mul_le_mul_of_nonneg_left hbiM hδ.le
      _ < m := hδM
      _ ≤ |a i| := hmle i hi
  rcases lt_or_gt_of_ne hi with hneg | hpos
  · have hu := (abs_lt.mp hpert).2
    rw [abs_of_neg hneg] at hu
    have hs : a i + δ * b i < 0 := by linarith
    rw [_root_.sign_neg hs, _root_.sign_neg hneg]
  · have hl := (abs_lt.mp hpert).1
    rw [abs_of_pos hpos] at hl
    have hs : 0 < a i + δ * b i := by linarith
    rw [_root_.sign_pos hs, _root_.sign_pos hpos]

/-- Weak normality suffices for concordance to descend from the fully open extension. -/
theorem concordant_of_fullyOpen_concordant_of_weaklyNormal (N : Network S)
    (hwn : N.WeaklyNormal) (hopen : N.fullyOpen.Concordant) :
    N.Concordant := by
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
    unfold T weakNormalityOperatorOnStoich at hv
    change N.weakNormalityOperator P χ.1 = σ' at hv
    exact hv
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
          change (α r + δ * β r) * N.reactionVector r s =
            (α r + δ * β r) * N.reactionVector r s
          rfl
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
  refine ⟨hker, ?_, hσ'ne, ?_, ?_⟩
  · rw [N.stoichSubspace_fullyOpen_eq_top]
    exact Submodule.mem_top
  · intro q hq
    rcases q with r | q
    · -- original reaction
      by_cases hα : α r = 0
      · have hβne : β r ≠ 0 := by
          intro hβ0
          apply hq
          simp [α', hα, hβ0]
        rcases hW.sign_balance r hα with hzero | hopp
        · -- Original sigma vanishes on the source. The positive source weights make beta
          -- choose a sign already present in chi, hence in sigma'.
          rcases lt_or_gt_of_ne hβne with hβneg | hβpos
          · have hex : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ χ.1 s < 0 := by
              by_contra hn
              push Not at hn
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
            refine ⟨s, ?_, ?_⟩
            · simpa using hs
            · have hσs0 := hzero s hs
              have hσ's : σ' s = ε * χ.1 s := by simp [σ', σ0, hσs0]
              have hσ'neg : σ' s < 0 := by rw [hσ's]; exact mul_neg_of_pos_of_neg hε hχs
              have hα'neg : α' (Sum.inl r) < 0 := by simp [α', hα]; exact mul_neg_of_pos_of_neg hδ hβneg
              rw [_root_.sign_neg hσ'neg, _root_.sign_neg hα'neg]
          · have hex : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ 0 < χ.1 s := by
              by_contra hn
              push Not at hn
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
            refine ⟨s, ?_, ?_⟩
            · simpa using hs
            · have hσs0 := hzero s hs
              have hσ's : σ' s = ε * χ.1 s := by simp [σ', σ0, hσs0]
              have hσ'pos : 0 < σ' s := by rw [hσ's]; exact mul_pos hε hχs
              have hα'pos : 0 < α' (Sum.inl r) := by simp [α', hα]; exact mul_pos hδ hβpos
              rw [_root_.sign_pos hσ'pos, _root_.sign_pos hα'pos]
        · obtain ⟨sn, sp, hsn, hsp, hσn, hσp⟩ := hopp
          rcases lt_or_gt_of_ne hβne with hβneg | hβpos
          · refine ⟨sn, by simpa using hsn, ?_⟩
            have hsigne : SignType.sign (σ' sn) = SignType.sign (σ sn) := by
              simpa [σ', σ0] using hsignσ sn hσn.ne
            have hα'neg : α' (Sum.inl r) < 0 := by simp [α', hα]; exact mul_neg_of_pos_of_neg hδ hβneg
            rw [_root_.sign_neg hα'neg]
            exact hsigne.trans (_root_.sign_neg hσn)
          · refine ⟨sp, by simpa using hsp, ?_⟩
            have hsigne : SignType.sign (σ' sp) = SignType.sign (σ sp) := by
              simpa [σ', σ0] using hsignσ sp hσp.ne'
            have hα'pos : 0 < α' (Sum.inl r) := by simp [α', hα]; exact mul_pos hδ hβpos
            rw [_root_.sign_pos hα'pos]
            exact hsigne.trans (_root_.sign_pos hσp)
      · obtain ⟨s, hs, hmatch⟩ := hW.sign_match r hα
        refine ⟨s, by simpa using hs, ?_⟩
        have hsigma_ne : σ s ≠ 0 := by
          intro hz
          rw [hz, sign_zero] at hmatch
          exact (sign_ne_zero.mpr hα) hmatch.symm
        have hsigne : SignType.sign (σ' s) = SignType.sign (σ s) := by
          simpa [σ', σ0] using hsignσ s hsigma_ne
        exact hsigne.trans (hmatch.trans (hsignα r hα).symm)
    · rcases q with s | s
      · simp [α'] at hq
      · have hsne : σ' s ≠ 0 := by
          intro hs0
          apply hq
          simp [α', hs0]
        refine ⟨s, ?_, ?_⟩
        · simp [fullyOpen_reaction_outflow, outflowReaction, singletonComplex_apply]
        · rcases lt_or_gt_of_ne hsne with hsneg | hspos
          · have hprod : δ * σ' s < 0 := mul_neg_of_pos_of_neg hδ hsneg
            simp [α']
            rw [_root_.sign_neg hsneg, _root_.sign_neg hprod]
          · have hprod : 0 < δ * σ' s := mul_pos hδ hspos
            simp [α']
            rw [_root_.sign_pos hspos, _root_.sign_pos hprod]
  · intro q hq0
    rcases q with r | q
    · by_cases hα : α r = 0
      · have hβ0 : β r = 0 := by
          have : δ * β r = 0 := by simpa [α', hα] using hq0
          exact (mul_eq_zero.mp this).resolve_left hδ.ne'
        rcases hW.sign_balance r hα with hzero | hopp
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
                push Not at hn
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
              refine ⟨s0, sp, by simpa using hs0, by simpa using hsp, ?_, ?_⟩
              · have hσ0 := hzero s0 hs0
                have : σ' s0 = ε * χ.1 s0 := by simp [σ', σ0, hσ0]
                rw [this]
                exact mul_neg_of_pos_of_neg hε hχ0neg
              · have hσp0 := hzero sp hsp
                have : σ' sp = ε * χ.1 sp := by simp [σ', σ0, hσp0]
                rw [this]
                exact mul_pos hε hχp
            · have hexneg : ∃ s : S, (N.reaction r).source s ≠ 0 ∧ χ.1 s < 0 := by
                by_contra hn
                push Not at hn
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
              refine ⟨sn, s0, by simpa using hsn, by simpa using hs0, ?_, ?_⟩
              · have hσn0 := hzero sn hsn
                have : σ' sn = ε * χ.1 sn := by simp [σ', σ0, hσn0]
                rw [this]
                exact mul_neg_of_pos_of_neg hε hχn
              · have hσ00 := hzero s0 hs0
                have : σ' s0 = ε * χ.1 s0 := by simp [σ', σ0, hσ00]
                rw [this]
                exact mul_pos hε hχ0pos
        · right
          obtain ⟨sn, sp, hsn, hsp, hσn, hσp⟩ := hopp
          refine ⟨sn, sp, by simpa using hsn, by simpa using hsp, ?_, ?_⟩
          · have hsgn : SignType.sign (σ' sn) = SignType.sign (σ sn) := by
              simpa [σ', σ0] using hsignσ sn hσn.ne
            apply sign_eq_neg_one_iff.mp
            exact hsgn.trans (_root_.sign_neg hσn)
          · have hsgp : SignType.sign (σ' sp) = SignType.sign (σ sp) := by
              simpa [σ', σ0] using hsignσ sp hσp.ne'
            apply sign_eq_one_iff.mp
            exact hsgp.trans (_root_.sign_pos hσp)
      · -- alpha was nonzero, hence alpha' is nonzero by sign preservation, contradiction
        have hsign := hsignα r hα
        have hα'ne : α r + δ * β r ≠ 0 := by
          intro hz
          rw [hz, sign_zero] at hsign
          exact (sign_ne_zero.mpr hα) hsign.symm
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

/-- If the fully open extension is concordant, concordance of the original network is
**equivalent** to nondegeneracy. -/
theorem concordant_iff_nondegenerate_of_fullyOpen_concordant (N : Network S)
    (hopen : N.fullyOpen.Concordant) :
    N.Concordant ↔ N.Nondegenerate := by
  constructor
  · exact Concordant.nondegenerate
  · intro hnd
    apply N.concordant_of_fullyOpen_concordant_of_weaklyNormal
    · exact (N.weaklyNormal_iff_nondegenerate).2 hnd
    · exact hopen

/-! ## Descent of concordance through the fully open extension

`concordant_of_fullyOpen_concordant_of_weaklyNormal` above is the general statement.  The
classical normal-network form and its corollaries are strict special cases of it, because
`weaklyNormal_of_normal` turns a normality witness into a weak-normality witness.  They used
to be stated separately in `Normality.lean` with their own proof obligation; keeping a single
obligation here avoids counting one gap twice.
-/

/-- **Fully-open concordance descends through normality.** -/
theorem concordant_of_fullyOpen_concordant_of_normal (N : Network S)
    (hnormal : N.Normal) (hopen : N.fullyOpen.Concordant) :
    N.Concordant :=
  N.concordant_of_fullyOpen_concordant_of_weaklyNormal
    (N.weaklyNormal_of_normal hnormal) hopen

/-- Weak reversibility therefore lets concordance of the fully open extension descend to
that of the original network. -/
theorem concordant_of_fullyOpen_concordant_of_weaklyReversible (N : Network S)
    (hwr : N.WeaklyReversible) (hopen : N.fullyOpen.Concordant) :
    N.Concordant :=
  N.concordant_of_fullyOpen_concordant_of_normal (N.normal_of_weaklyReversible hwr) hopen

/-- Contrapositive form: discordance of a normal network forces discordance of its fully
open extension. -/
theorem Discordant.fullyOpen_of_normal {N : Network S}
    (hd : N.Discordant) (hn : N.Normal) :
    N.fullyOpen.Discordant := by
  intro hopen
  exact hd (N.concordant_of_fullyOpen_concordant_of_normal hn hopen)

end Network
end CRNT
