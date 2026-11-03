import CRNT.Kinetics.GeneralizedConditions
import CRNT.Multistationarity.SignConstruction
import CRNT.Kinetics.GeneralizedNondegeneracy
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient
import Mathlib.Topology.IsLocalHomeomorph
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Sequences
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Generalized Birch existence and bijectivity

The genuinely two-subspace part of generalized Birch theory asks when the toric leaf

`x* ⊙ exp(Tᗮ)`

meets every positive affine stoichiometric class `c + S`.  In the square setting, the
robust sign-closure condition `sign(S) ⊆ sign(T)` (together with equal rank, implicit in
the matrix formulation) makes the associated exponential map a global diffeomorphism.
The independent sign-compatibility condition gives uniqueness/transversality.

This module promotes that theorem family to first-class Lean statements.  The hard
topological/proper-map existence argument is intentionally localized in
`generalized_birch_existence_of_conditions`.
-/

namespace CRNT

open Filter Metric Bornology
open scoped Topology

variable {ι : Type*} [Fintype ι]

/-- Positive generalized Birch intersection problem. -/
def GeneralizedBirchPoint
    (S T : Submodule ℝ (ι → ℝ)) (xstar c x : ι → ℝ) : Prop :=
  (∀ i, 0 < x i) ∧
  x - c ∈ S ∧
  (fun i => Real.log (x i) - Real.log (xstar i)) ∈ orthSum T

/-- Every positive `S`-class meets the toric leaf through `xstar`. -/
def GeneralizedBirchSurjective
    (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ xstar c : ι → ℝ,
    (∀ i, 0 < xstar i) → (∀ i, 0 < c i) →
      ∃ x, GeneralizedBirchPoint S T xstar c x

/-- Every positive class has at most one generalized Birch point. -/
def GeneralizedBirchInjective
    (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ xstar c : ι → ℝ,
    ∀ x y,
      GeneralizedBirchPoint S T xstar c x →
      GeneralizedBirchPoint S T xstar c y → x = y

/-- Every positive class has exactly one generalized Birch point. -/
def GeneralizedBirchBijective
    (S T : Submodule ℝ (ι → ℝ)) : Prop :=
  ∀ xstar c : ι → ℝ,
    (∀ i, 0 < xstar i) → (∀ i, 0 < c i) →
      ∃! x, GeneralizedBirchPoint S T xstar c x

/-- The sign condition is exactly generalized Birch injectivity. -/
theorem generalizedBirchInjective_iff_signCompatible
    (S T : Submodule ℝ (ι → ℝ)) :
    GeneralizedBirchInjective S T ↔ SignCompatible S (orthSum T) := by
  constructor
  · intro hinj
    rw [signCompatible_iff_not_signIncompatible]
    intro hbad
    obtain ⟨xstar, c, x, y, hxs, hc, hx, hy, hxy⟩ :=
      exists_toric_multistationarity_of_signIncompatible S T hbad
    exact hxy (hinj xstar c x y hx hy)
  · intro hsign xstar c x y hx hy
    exact gen_birch_uniqueness S T hsign hx.1 hy.1
      (by
        have h1 := hx.2.1
        have h2 := hy.2.1
        rw [show x - y = (x - c) - (y - c) by ext i; simp [Pi.sub_apply]]
        exact S.sub_mem h1 h2)
      (by
        have h1 := hx.2.2
        have h2 := hy.2.2
        have hsub := (orthSum T).sub_mem h1 h2
        simpa [Pi.sub_apply] using hsub)


private theorem generalizedBirch_closure_signCompatible
    {S T : Submodule ℝ (ι → ℝ)}
    (h : GeneralizedClosureCondition S T) : SignCompatible S (orthSum T) := by
  intro u hu v hv huv
  have hsu : signVector u ∈ RealizableSignVector S :=
    mem_realizableSignVector.mpr ⟨u, hu, rfl⟩
  have hsuT : signVector u ∈ RealizableSignVector T := h.sign_subset hsu
  obtain ⟨t, ht, htu⟩ := mem_realizableSignVector.mp hsuT
  have htv : SameSign t v := by
    rw [sameSign_iff_signVector_eq]
    exact htu.trans (sameSign_iff_signVector_eq.mp huv)
  have ht0 : t = 0 := signCompatible_self T t ht v hv htv
  have hsignu0 : signVector u = (fun _ => 0) := by
    rw [← htu, ht0]
    funext i
    simp [signVector]
  exact (signVector_eq_zero_iff u).mp hsignu0

private theorem generalizedBirch_closure_finrank
    {S T : Submodule ℝ (ι → ℝ)}
    (h : GeneralizedClosureCondition S T) :
    Module.finrank ℝ S + Module.finrank ℝ (orthSum T) = Fintype.card ι := by
  have hle : Module.finrank ℝ T ≤ Fintype.card ι :=
    (Submodule.finrank_le _).trans (Module.finrank_pi ℝ).le
  rw [finrank_orthSum, h.finrank_eq]
  omega

private noncomputable def generalizedBirchPath
    (xstar c : ι → ℝ) (t : ℝ) : ι → ℝ :=
  fun i => (1 - t) * xstar i + t * c i

private noncomputable def generalizedBirchExp
    (xstar : ι → ℝ) (w : ι → ℝ) : ι → ℝ :=
  fun i => xstar i * Real.exp (w i)

private theorem generalizedBirchPath_bounds
    (xstar c : ι → ℝ) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) (i : ι) :
    min (xstar i) (c i) ≤ generalizedBirchPath xstar c t i ∧
      generalizedBirchPath xstar c t i ≤ max (xstar i) (c i) := by
  rcases le_total (xstar i) (c i) with hxc | hcx
  · constructor
    · rw [min_eq_left hxc]
      simp only [generalizedBirchPath]
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hxc)]
    · rw [max_eq_right hxc]
      simp only [generalizedBirchPath]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hxc)]
  · constructor
    · rw [min_eq_right hcx]
      simp only [generalizedBirchPath]
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hcx)]
    · rw [max_eq_left hcx]
      simp only [generalizedBirchPath]
      nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hcx)]

private theorem generalizedBirchMap_isLocalHomeomorph
    (S T : Submodule ℝ (ι → ℝ))
    (hclosure : GeneralizedClosureCondition S T)
    (xstar c : ι → ℝ) (hxs : ∀ i, 0 < xstar i) :
    IsLocalHomeomorph (fun w : orthSum T =>
      S.mkQ (fun i => xstar i * Real.exp (w.1 i) - c i)) := by
  letI : IsClosed (S : Set (ι → ℝ)) := S.closed_of_finiteDimensional
  let f : orthSum T → ((ι → ℝ) ⧸ S) := fun w =>
      S.mkQ (fun i => xstar i * Real.exp (w.1 i) - c i)
  change IsLocalHomeomorph f
  intro w
  let x : ι → ℝ := fun i => xstar i * Real.exp (w.1 i)
  have hx : ∀ i, 0 < x i := by
    intro i
    exact mul_pos (hxs i) (Real.exp_pos _)
  let A : orthSum T →L[ℝ] (ι → ℝ) :=
    ContinuousLinearMap.pi (fun i =>
      x i • ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (orthSum T).subtypeL))
  let D : orthSum T →L[ℝ] ((ι → ℝ) ⧸ S) := S.mkQL.comp A
  have hA : HasStrictFDerivAt
      (fun z : orthSum T => fun i => xstar i * Real.exp (z.1 i) - c i) A w := by
    apply hasStrictFDerivAt_pi.mpr
    intro i
    have hcoord : HasStrictFDerivAt (fun z : orthSum T => z.1 i)
        ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
          (orthSum T).subtypeL) w := by
      exact ((ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp
        (orthSum T).subtypeL).hasStrictFDerivAt
    have hcomp := (Real.hasStrictDerivAt_exp (w.1 i)).hasStrictFDerivAt.comp w hcoord
    convert (hcomp.const_mul (xstar i)).sub_const (c i) using 1
    ext v
    simp [x, ContinuousLinearMap.comp_apply]
    ring
  have hmk : HasStrictFDerivAt (fun z : ι → ℝ => S.mkQL z) S.mkQL
      (fun i => xstar i * Real.exp (w.1 i) - c i) := S.mkQL.hasStrictFDerivAt
  have hD : HasStrictFDerivAt f D w := by
    have hQ := hmk.comp w hA
    simpa [f, D] using hQ
  have hinj : Function.Injective D := by
    intro u v huv
    let d : orthSum T := u - v
    have hd0 : D d = 0 := by
      dsimp [d]
      rw [map_sub, huv, sub_self]
    have hq : S.mkQ (A d) = 0 := by
      simpa [D, ContinuousLinearMap.comp_apply] using hd0
    have hmemS : A d ∈ S := (Submodule.Quotient.mk_eq_zero S).mp hq
    have hAd : A d = diagonalScale x d.1 := by
      ext i
      simp [A, x, diagonalScale_apply, ContinuousLinearMap.comp_apply]
    have hmemTan : A d ∈ toricTangentSubspace T x := by
      rw [hAd]
      exact ⟨d.1, d.2, rfl⟩
    have hnd := generalizedToricNondegenerate_of_signCompatible S T
      (generalizedBirch_closure_signCompatible hclosure) hx
    have hzero : A d = 0 := by
      have hm : A d ∈ S ⊓ toricTangentSubspace T x := ⟨hmemS, hmemTan⟩
      rw [hnd] at hm
      simpa using hm
    have hdval : d.1 = 0 := by
      funext i
      have hi := congrFun (hAd.symm.trans hzero) i
      simp [diagonalScale_apply] at hi
      exact hi.resolve_left (ne_of_gt (hx i))
    have hd : d = 0 := Subtype.ext hdval
    exact sub_eq_zero.mp hd
  have hker : D.ker = ⊥ := LinearMap.ker_eq_bot.mpr hinj
  have hfin : Module.finrank ℝ (orthSum T) =
      Module.finrank ℝ ((ι → ℝ) ⧸ S) := by
    have hs := Submodule.finrank_quotient_add_finrank S
    have hc := generalizedBirch_closure_finrank hclosure
    have hpi : Module.finrank ℝ (ι → ℝ) = Fintype.card ι := Module.finrank_pi ℝ
    omega
  have hsurj : Function.Surjective D :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin).mp hinj
  have hrange : D.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  let e : orthSum T ≃L[ℝ] ((ι → ℝ) ⧸ S) :=
    ContinuousLinearEquiv.ofBijective D hker hrange
  have hDe : HasStrictFDerivAt f
      (e : orthSum T →L[ℝ] ((ι → ℝ) ⧸ S)) w := by
    simpa [e, ContinuousLinearEquiv.coe_ofBijective] using hD
  refine ⟨hDe.toOpenPartialHomeomorph f,
    hDe.mem_toOpenPartialHomeomorph_source, ?_⟩
  exact hDe.toOpenPartialHomeomorph_coe.symm

private theorem generalizedBirch_preimage_bounded
    (S T : Submodule ℝ (ι → ℝ))
    (hclosure : GeneralizedClosureCondition S T)
    (xstar c : ι → ℝ) (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    Bornology.IsBounded {w : orthSum T | ∃ t ∈ Set.Icc (0 : ℝ) 1,
      generalizedBirchExp xstar w.1 - generalizedBirchPath xstar c t ∈ S} := by
  rw [isBounded_iff_forall_norm_le]
  by_contra hnot
  push Not at hnot
  choose w hwP hwnorm using fun n : ℕ => hnot (n : ℝ)
  choose tn htnI hsn using fun n => hwP n
  let s : ℕ → (ι → ℝ) := fun n =>
    generalizedBirchExp xstar (w n).1 - generalizedBirchPath xstar c (tn n)
  let σ : ℕ → (ι → SignType) := fun n => signVector (s n)
  have hsS : ∀ n, s n ∈ S := by intro n; exact hsn n
  classical
  obtain ⟨σ0, hfiber⟩ := Finite.exists_infinite_fiber σ
  have hIinf : (σ ⁻¹' ({σ0} : Set (ι → SignType))).Infinite :=
    Set.infinite_coe_iff.mp hfiber
  let e := hIinf.natEmbedding (σ ⁻¹' ({σ0} : Set (ι → SignType)))
  let k : ℕ → ℕ := fun n => (e n).1
  have hkσ : ∀ n, σ (k n) = σ0 := by
    intro n
    exact Set.mem_singleton_iff.mp (e n).2
  have hkinj : Function.Injective k := by
    intro a b hab
    apply e.injective
    exact Subtype.ext hab
  have hkTop : Filter.Tendsto k Filter.atTop Filter.atTop := hkinj.nat_tendsto_atTop
  have hkReal : Filter.Tendsto (fun n => (k n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp hkTop
  have hnormTop : Filter.Tendsto (fun n => ‖w (k n)‖) Filter.atTop Filter.atTop :=
    tendsto_atTop_mono (fun n => le_of_lt (hwnorm (k n))) hkReal
  let u : ℕ → orthSum T := fun n => (‖w (k n)‖)⁻¹ • w (k n)
  have hwnz : ∀ n, w (k n) ≠ 0 := by
    intro n hzero
    have := hwnorm (k n)
    rw [hzero, norm_zero] at this
    exact (not_lt_of_ge (Nat.cast_nonneg _)) this
  have hunorm : ∀ n, ‖u n‖ = 1 := by
    intro n
    simp [u, norm_smul, norm_inv, hwnz n]
  have huSphere : ∀ n, u n ∈ Metric.sphere (0 : orthSum T) 1 := by
    intro n
    simp [hunorm n]
  obtain ⟨u0, hu0sphere, φ, hφmono, huconv⟩ :=
    (isCompact_sphere (0 : orthSum T) 1).tendsto_subseq huSphere
  have hu0norm : ‖u0‖ = 1 := by
    simpa [Metric.mem_sphere, dist_eq_norm] using hu0sphere
  have hu0ne : (u0 : ι → ℝ) ≠ 0 := by
    intro h
    have : u0 = 0 := Subtype.ext h
    simp [this] at hu0norm
  have hσ0S : σ0 ∈ RealizableSignVector S := by
    refine mem_realizableSignVector.mpr ⟨s (k 0), hsS (k 0), ?_⟩
    exact hkσ 0
  have hσ0T := hclosure.sign_subset hσ0S
  obtain ⟨v, hvT, hvσ⟩ := mem_realizableSignVector.mp hσ0T
  let j : ℕ → ℕ := fun n => k (φ n)
  have hnormPhi : Filter.Tendsto (fun n => ‖w (j n)‖) Filter.atTop Filter.atTop := by
    exact hnormTop.comp hφmono.tendsto_atTop
  have hucoord (i : ι) :
      Filter.Tendsto (fun n => (u (φ n) : ι → ℝ) i) Filter.atTop
        (𝓝 ((u0 : ι → ℝ) i)) := by
    let ev : orthSum T →L[ℝ] ℝ :=
      (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ).comp (orthSum T).subtypeL
    exact ev.continuous.continuousAt.tendsto.comp huconv
  have hwcoord_eq (n : ℕ) (i : ι) :
      (w (j n) : ι → ℝ) i = ‖w (j n)‖ * (u (φ n) : ι → ℝ) i := by
    have hnz : ‖w (j n)‖ ≠ 0 := norm_ne_zero_iff.mpr (hwnz (φ n))
    change (w (k (φ n)) : ι → ℝ) i =
      ‖w (k (φ n))‖ * (‖w (k (φ n))‖⁻¹ * (w (k (φ n)) : ι → ℝ) i)
    rw [← mul_assoc, mul_inv_cancel₀ hnz, one_mul]
  have hsigma_pos (i : ι) (hi : 0 < (u0 : ι → ℝ) i) : σ0 i = 1 := by
    let a : ℝ := (u0 : ι → ℝ) i / 2
    have ha : 0 < a := half_pos hi
    have hua : ∀ᶠ n in Filter.atTop, a < (u (φ n) : ι → ℝ) i :=
      (tendsto_order.mp (hucoord i)).1 a (by dsimp [a]; linarith)
    have hbase : Filter.Tendsto (fun n => ‖w (j n)‖ * a) Filter.atTop Filter.atTop :=
      hnormPhi.atTop_mul_const ha
    have hwtop : Filter.Tendsto (fun n => (w (j n) : ι → ℝ) i)
        Filter.atTop Filter.atTop := by
      apply tendsto_atTop_mono' Filter.atTop _ hbase
      filter_upwards [hua] with n hun
      rw [hwcoord_eq]
      exact mul_le_mul_of_nonneg_left hun.le (norm_nonneg _)
    have hxetop : Filter.Tendsto
        (fun n => xstar i * Real.exp ((w (j n) : ι → ℝ) i))
        Filter.atTop Filter.atTop :=
      (Real.tendsto_exp_atTop.comp hwtop).const_mul_atTop (hxs i)
    let M : ℝ := max (xstar i) (c i)
    have hlarge0 : ∀ᶠ n in Filter.atTop,
        M + 1 ≤ xstar i * Real.exp ((w (j n) : ι → ℝ) i) :=
      hxetop.eventually_ge_atTop (M + 1)
    have hlarge : ∀ᶠ n in Filter.atTop,
        M < xstar i * Real.exp ((w (j n) : ι → ℝ) i) := by
      filter_upwards [hlarge0] with n hn
      linarith
    have hspos : ∀ᶠ n in Filter.atTop, 0 < s (j n) i := by
      filter_upwards [hlarge] with n hn
      have hpathle :=
        (generalizedBirchPath_bounds xstar c (tn (j n)) (htnI (j n)) i).2
      dsimp [s, generalizedBirchExp]
      exact sub_pos.mpr (hpathle.trans_lt hn)
    obtain ⟨n, hn⟩ := hspos.exists
    have hsig : signVector (s (j n)) i = σ0 i := by
      simpa [j, σ] using congrFun (hkσ (φ n)) i
    have hsp : signVector (s (j n)) i = 1 := sign_pos hn
    exact hsig.symm.trans hsp
  have hsigma_neg (i : ι) (hi : (u0 : ι → ℝ) i < 0) : σ0 i = -1 := by
    let a : ℝ := (u0 : ι → ℝ) i / 2
    have ha : a < 0 := by dsimp [a]; linarith
    have hua : ∀ᶠ n in Filter.atTop, (u (φ n) : ι → ℝ) i < a :=
      (tendsto_order.mp (hucoord i)).2 a (by dsimp [a]; linarith)
    have hbase : Filter.Tendsto (fun n => ‖w (j n)‖ * a)
        Filter.atTop Filter.atBot := hnormPhi.atTop_mul_const_of_neg ha
    have hwbot : Filter.Tendsto (fun n => (w (j n) : ι → ℝ) i)
        Filter.atTop Filter.atBot := by
      apply tendsto_atBot_mono' Filter.atTop _ hbase
      filter_upwards [hua] with n hun
      rw [hwcoord_eq]
      exact mul_le_mul_of_nonneg_left hun.le (norm_nonneg _)
    have hexp0 : Filter.Tendsto
        (fun n => Real.exp ((w (j n) : ι → ℝ) i)) Filter.atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp hwbot
    have hxe0 : Filter.Tendsto
        (fun n => xstar i * Real.exp ((w (j n) : ι → ℝ) i)) Filter.atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hexp0
    let m : ℝ := min (xstar i) (c i)
    have hm : 0 < m := lt_min (hxs i) (hc i)
    have hsmall : ∀ᶠ n in Filter.atTop,
        xstar i * Real.exp ((w (j n) : ι → ℝ) i) < m :=
      (tendsto_order.mp hxe0).2 m hm
    have hsneg : ∀ᶠ n in Filter.atTop, s (j n) i < 0 := by
      filter_upwards [hsmall] with n hn
      have hpathge :=
        (generalizedBirchPath_bounds xstar c (tn (j n)) (htnI (j n)) i).1
      dsimp [s, generalizedBirchExp]
      exact sub_neg.mpr (hn.trans_le hpathge)
    obtain ⟨n, hn⟩ := hsneg.exists
    have hsig : signVector (s (j n)) i = σ0 i := by
      simpa [j, σ] using congrFun (hkσ (φ n)) i
    have hsn' : signVector (s (j n)) i = -1 := sign_neg hn
    exact hsig.symm.trans hsn'
  have hvpos (i : ι) (hi : 0 < (u0 : ι → ℝ) i) : 0 < v i := by
    apply sign_eq_one_iff.mp
    rw [← signVector_apply, hvσ, hsigma_pos i hi]
  have hvneg (i : ι) (hi : (u0 : ι → ℝ) i < 0) : v i < 0 := by
    apply sign_eq_neg_one_iff.mp
    rw [← signVector_apply, hvσ, hsigma_neg i hi]
  have hconf : Conformal v (u0 : ι → ℝ) := by
    intro i
    rcases lt_trichotomy ((u0 : ι → ℝ) i) 0 with hi | hi | hi
    · exact mul_nonneg_of_nonpos_of_nonpos (hvneg i hi).le hi.le
    · simp [hi]
    · exact mul_nonneg (hvpos i hi).le hi.le
  have hprod0 := mul_eq_zero_of_conformal_mem_orthSum hvT u0.2 hconf
  obtain ⟨i, hi⟩ : ∃ i, (u0 : ι → ℝ) i ≠ 0 := by
    by_contra hzero
    push Not at hzero
    exact hu0ne (funext hzero)
  rcases lt_or_gt_of_ne hi with hi | hi
  · exact (mul_ne_zero (hvneg i hi).ne hi.ne) (hprod0 i)
  · exact (mul_ne_zero (hvpos i hi).ne' hi.ne') (hprod0 i)

/-- Equal rank plus `sign(S) ⊆ sign(T)` imply that every positive stoichiometric
class meets the positive toric leaf.  This is the robust generalized Birch existence
criterion (the surjectivity half of the global-diffeomorphism theorem). -/
theorem generalized_birch_existence_of_conditions
    (S T : Submodule ℝ (ι → ℝ))
    (hclosure : GeneralizedClosureCondition S T) :
    GeneralizedBirchSurjective S T := by
  intro xstar c hxs hc
  letI : IsClosed (S : Set (ι → ℝ)) := S.closed_of_finiteDimensional
  let E : orthSum T → ((ι → ℝ) ⧸ S) := fun w =>
    S.mkQ (fun i => xstar i * Real.exp (w.1 i))
  let q : ℝ → ((ι → ℝ) ⧸ S) := fun t =>
    S.mkQ (generalizedBirchPath xstar c t)
  have hElocal : IsLocalHomeomorph E := by
    simpa [E] using
      generalizedBirchMap_isLocalHomeomorph S T hclosure xstar (0 : ι → ℝ) hxs
  have hEcont : Continuous E := hElocal.continuous
  have hEopen : IsOpen (Set.range E) := by
    rw [← Set.image_univ]
    exact hElocal.isOpenMap Set.univ isOpen_univ
  have hqcont : Continuous q := by
    apply S.mkQL.continuous.comp
    apply continuous_pi
    intro i
    dsimp [q, generalizedBirchPath]
    fun_prop
  let K : Set ((ι → ℝ) ⧸ S) := q '' Set.Icc (0 : ℝ) 1
  have hKcompact : IsCompact K := isCompact_Icc.image hqcont
  have hKclosed : IsClosed K := hKcompact.isClosed
  let P : Set (orthSum T) := E ⁻¹' K
  have hPclosed : IsClosed P := hKclosed.preimage hEcont
  have hquot_iff (w : orthSum T) (t : ℝ) :
      E w = q t ↔
        generalizedBirchExp xstar w.1 - generalizedBirchPath xstar c t ∈ S := by
    change S.mkQ (generalizedBirchExp xstar w.1) =
      S.mkQ (generalizedBirchPath xstar c t) ↔ _
    constructor
    · intro heq
      apply (Submodule.Quotient.mk_eq_zero S).mp
      have hz : S.mkQL
          (generalizedBirchExp xstar w.1 - generalizedBirchPath xstar c t) = 0 := by
        rw [map_sub]
        change S.mkQ (generalizedBirchExp xstar w.1) -
          S.mkQ (generalizedBirchPath xstar c t) = 0
        rw [heq, sub_self]
      exact hz
    · intro hmem
      have hz : S.mkQL
          (generalizedBirchExp xstar w.1 - generalizedBirchPath xstar c t) = 0 := by
        exact (Submodule.Quotient.mk_eq_zero S).mpr hmem
      rw [map_sub] at hz
      exact sub_eq_zero.mp hz
  have hPbounded : Bornology.IsBounded P := by
    apply (generalizedBirch_preimage_bounded S T hclosure xstar c hxs hc).subset
    intro w hwP
    change E w ∈ K at hwP
    rcases hwP with ⟨t, htI, hEt⟩
    exact ⟨t, htI, (hquot_iff w t).mp hEt.symm⟩
  have hPcompact : IsCompact P :=
    Metric.isCompact_iff_isClosed_bounded.mpr ⟨hPclosed, hPbounded⟩
  have hEKcompact : IsCompact (Set.range E ∩ K) := by
    have himg : Set.range E ∩ K = E '' P := by
      ext y
      constructor
      · rintro ⟨⟨w, rfl⟩, hwK⟩
        exact ⟨w, hwK, rfl⟩
      · rintro ⟨w, hwP, rfl⟩
        exact ⟨⟨w, rfl⟩, hwP⟩
    rw [himg]
    exact hPcompact.image hEcont
  have hEKclosed : IsClosed (Set.range E ∩ K) := hEKcompact.isClosed
  let J := Set.Icc (0 : ℝ) 1
  let qJ : J → ((ι → ℝ) ⧸ S) := fun t => q t.1
  let R : Set J := qJ ⁻¹' Set.range E
  have hqJcont : Continuous qJ := hqcont.comp continuous_subtype_val
  have hRopen : IsOpen R := hEopen.preimage hqJcont
  have hRclosed : IsClosed R := by
    have hpre : R = qJ ⁻¹' (Set.range E ∩ K) := by
      ext t
      simp only [R, Set.mem_preimage, Set.mem_inter_iff]
      constructor
      · intro ht
        refine ⟨ht, ?_⟩
        exact ⟨t.1, t.2, rfl⟩
      · exact fun ht => ht.1
    rw [hpre]
    exact hEKclosed.preimage hqJcont
  have hRne : R.Nonempty := by
    let t0 : J := ⟨0, by norm_num [J]⟩
    refine ⟨t0, ?_⟩
    change q 0 ∈ Set.range E
    refine ⟨0, (hquot_iff 0 0).mpr ?_⟩
    have heq : generalizedBirchExp xstar ((0 : orthSum T) : ι → ℝ) =
        generalizedBirchPath xstar c 0 := by
      funext i
      simp [generalizedBirchExp, generalizedBirchPath]
    rw [heq, sub_self]
    exact S.zero_mem
  have hRuniv : R = Set.univ :=
    (show IsClopen R from ⟨hRclosed, hRopen⟩).eq_univ hRne
  let t1 : J := ⟨1, by norm_num [J]⟩
  have ht1 : t1 ∈ R := by rw [hRuniv]; trivial
  change q 1 ∈ Set.range E at ht1
  rcases ht1 with ⟨w, hw⟩
  let x : ι → ℝ := generalizedBirchExp xstar w.1
  refine ⟨x, ?_, ?_, ?_⟩
  · intro i
    exact mul_pos (hxs i) (Real.exp_pos _)
  · have hmem := (hquot_iff w 1).mp hw
    have hpath1 : generalizedBirchPath xstar c 1 = c := by
      funext i
      simp [generalizedBirchPath]
    simpa [x, hpath1] using hmem
  · have hwT : (w : ι → ℝ) ∈ orthSum T := w.2
    have hlogeq :
        (fun i => Real.log (x i) - Real.log (xstar i)) = (w : ι → ℝ) := by
      funext i
      simp [x, generalizedBirchExp,
        Real.log_mul (ne_of_gt (hxs i)) (Real.exp_ne_zero _)]
    simpa [hlogeq] using hwT

/-- Bundled generalized CBE conditions imply existence in every positive class. -/
theorem GeneralizedCBEConditions.generalizedBirchSurjective
    {S T : Submodule ℝ (ι → ℝ)} (h : GeneralizedCBEConditions S T) :
    GeneralizedBirchSurjective S T :=
  generalized_birch_existence_of_conditions S T h.closure

/-- Full generalized Birch bijectivity theorem. -/
theorem generalized_birch_bijective_of_conditions
    (S T : Submodule ℝ (ι → ℝ))
    (h : GeneralizedCBEConditions S T) :
    GeneralizedBirchBijective S T := by
  intro xstar c hxs hc
  obtain ⟨x, hx⟩ := h.generalizedBirchSurjective xstar c hxs hc
  refine ⟨x, hx, ?_⟩
  intro y hy
  exact gen_birch_uniqueness S T h.uniqueness hy.1 hx.1
    (by
      have h1 := hy.2.1
      have h2 := hx.2.1
      rw [show y - x = (y - c) - (x - c) by ext i; simp [Pi.sub_apply]]
      exact S.sub_mem h1 h2)
    (by
      have h1 := hy.2.2
      have h2 := hx.2.2
      have hsub := (orthSum T).sub_mem h1 h2
      simpa [Pi.sub_apply] using hsub)

/-- Classical Birch theorem is recovered because the single-subspace case satisfies the
required oriented-matroid conditions. -/
theorem generalizedBirchBijective_self (S : Submodule ℝ (ι → ℝ)) :
    GeneralizedBirchBijective S S := by
  -- Can be proved directly from classical Birch existence/uniqueness; stated here as
  -- a sanity bridge independent of the generalized closure/face theorem.
  intro xstar c hxs hc
  obtain ⟨x, hx, hxc, horth⟩ := birch_existence S hxs hc
  refine ⟨x, ⟨hx, hxc, mem_orthSum.mpr horth⟩, ?_⟩
  intro y hy
  exact birch_uniqueness_of_self S hy.1 hx
    (by
      rw [show y - x = (y - c) - (x - c) by ext i; simp [Pi.sub_apply]]
      exact S.sub_mem hy.2.1 hxc)
    (by
      have hsub := (orthSum S).sub_mem hy.2.2 (mem_orthSum.mpr horth)
      simpa [Pi.sub_apply] using hsub)

/-- Closure + face + uniqueness give existence, uniqueness, and transversality at the
intersection point. -/
theorem generalizedBirch_unique_nondegenerate
    (S T : Submodule ℝ (ι → ℝ))
    (h : GeneralizedCBEConditions S T)
    {xstar c : ι → ℝ} (hxs : ∀ i, 0 < xstar i) (hc : ∀ i, 0 < c i) :
    ∃! x : ι → ℝ,
      GeneralizedBirchPoint S T xstar c x ∧
      GeneralizedToricNondegenerateAt S T x := by
  obtain ⟨x, hx, huniq⟩ := generalized_birch_bijective_of_conditions S T h xstar c hxs hc
  refine ⟨x, ⟨hx, generalizedToricNondegenerate_of_signCompatible S T h.uniqueness hx.1⟩, ?_⟩
  intro y hy
  exact huniq y hy.1

end CRNT
