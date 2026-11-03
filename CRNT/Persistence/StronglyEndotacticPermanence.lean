import CRNT.Persistence.StronglyEndotacticPersistence
import CRNT.Dynamics.PermanenceAssembly
import CRNT.Dynamics.GlobalPersistenceFrontier

/-!
# Permanence of strongly endotactic mass-action systems

`StronglyEndotacticStd.structurallyPermanent`: for a strongly endotactic network, every positive
rate vector and every genuine mass-action flow, each positive stoichiometric class contains one
compact set that absorbs a tail of every positive orbit in the class (Gopalkrishnan–Miller–Shiu
2014, Theorem 1.1 for fixed rates; Anderson–Cappelletti–Kim–Nguyen 2020, Theorem 5.5). This discharges
`TierDescendingPermanenceClaim`.

The proof feeds `permanentForFlow_of_entry_and_uniform_bounds` with
`Υ = class ∩ logBox (R + 1)`, where outside `logBox R` the tier dissipation is negative on the
class:
* **uniform bounds** from `Υ`: a uniform upper bound by the entropy comparison argument, and a
  uniform lower bound by `StronglyEndotacticStd.persistent_uniform`;
* **entry**: along an orbit the coordinates stay in some `[m, M]` (persistence and boundedness);
  on the compact set of class points in `[m, M]^S` outside the open box of radius `R + 1`, the
  dissipation is at most `−η < 0`, so the tier entropy, which is at least `1`, would decrease
  without bound if the orbit stayed there.
-/

open Filter Set
open scoped BigOperators Topology NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Uniform boundedness from a compact set of initial states.** -/
theorem TierDescending.forward_bounded_on {N : Network S} (htd : N.TierDescending)
    (κ : N.RateConstants) (xref : Concentration S) {Υ : Set (Concentration S)}
    (hΥc : IsCompact Υ) (hΥ : Υ ⊆ N.positiveCompatibilityClass xref) :
    ∃ M : ℝ, ∀ γ : ℝ → Concentration S, γ 0 ∈ Υ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M := by
  classical
  obtain ⟨R, hR⟩ := exists_logBox_negative_outside_fixed htd κ xref
  set K : Set (Concentration S) := N.compatibilityClass xref ∩ logBox (S := S) (R : ℝ)
  have hKc : IsCompact K :=
    (isCompact_logBox (S := S) (R : ℝ)).inter_left (N.isClosed_compatibilityClass xref)
  have href : Concentration.Positive (tierReference S : Concentration S) := fun _ => zero_lt_one
  have hVc : Continuous (fun x : Concentration S => tierEntropy x) := by
    unfold tierEntropy; exact continuous_const.add (relEntropy_continuous href)
  obtain ⟨c, hc⟩ := hKc.bddAbove_image hVc.continuousOn
  obtain ⟨cΥ, hcΥ⟩ := hΥc.bddAbove_image hVc.continuousOn
  set c' : ℝ := max c cΥ + 1 with hc'
  refine ⟨max (Real.exp 2 * 1) (c' - 1), fun γ hγΥ hsol => ?_⟩
  have hγ0 : (γ 0).Positive := (hΥ hγΥ).2
  have hpos := N.genuineOrbit_pos κ hγ0 hsol
  have hcomp : ∀ t, 0 ≤ t → N.StoichCompatible xref (γ t) := fun t ht =>
    (hΥ hγΥ).1.trans (N.stoichCompatible_of_forward_solution κ hsol t ht)
  have hV0 : tierEntropy (γ 0) ≤ cΥ := hcΥ ⟨γ 0, hγΥ, rfl⟩
  have hV : ∀ t, 0 ≤ t → tierEntropy (γ t) ≤ c' := by
    intro t ht
    have hd : ∀ τ, 0 ≤ τ → HasDerivAt (fun τ => tierEntropy (γ τ))
        (N.tierDissipation κ (γ τ)) τ := fun τ hτ =>
      N.tierEntropy_hasDerivAt κ (hpos τ hτ) fun s => (hasDerivAt_pi.mp (hsol τ hτ)) s
    refine image_le_of_deriv_right_lt_deriv_boundary' (f := fun τ => tierEntropy (γ τ))
      (f' := fun τ => N.tierDissipation κ (γ τ)) (a := 0) (b := t)
      (fun τ hτ => (hd τ hτ.1).continuousAt.continuousWithinAt)
      (fun τ hτ => (hd τ hτ.1).hasDerivWithinAt)
      (B := fun _ => c') (B' := fun _ => 0)
      (by simp only [hc']; linarith [le_max_right c cΥ])
      continuousOn_const (fun _ _ => hasDerivWithinAt_const _ _ _)
      (fun τ hτ heq => ?_) (Set.right_mem_Icc.2 ht)
    have hnotK : γ τ ∉ K := by
      intro hK
      have h0 : tierEntropy (γ τ) ≤ c := hc ⟨γ τ, hK, rfl⟩
      have := heq ▸ h0
      simp only [hc'] at this
      linarith [le_max_left c cΥ]
    have hnotbox : γ τ ∉ logBox (S := S) (R : ℝ) := fun hb => hnotK ⟨hcomp τ hτ.1, hb⟩
    exact hR (γ τ) ⟨hcomp τ hτ.1, hpos τ hτ.1⟩ hnotbox
  intro t ht s
  have h1 : relEntropy (tierReference S) (γ t) ≤ c' - 1 := by
    have := hV t ht; unfold tierEntropy at this; linarith
  exact relEntropy_coord_le href (hpos t ht).nonnegative h1 s

/-- Tier dissipation is continuous on the positive orthant. -/
theorem continuousOn_tierDissipation (N : Network S) (κ : N.RateConstants) :
    ContinuousOn (N.tierDissipation κ) {x | x.Positive} := by
  have hmon : ∀ y : Complex S, Continuous fun x : Concentration S => tierMonomial x y := by
    intro y; unfold tierMonomial; fun_prop
  have hmpos : ∀ y : Complex S, ∀ x : Concentration S, x.Positive → 0 < tierMonomial x y :=
    fun y x hx => Finset.prod_pos fun s _ => pow_pos (hx s) _
  unfold tierDissipation
  refine continuousOn_finset_sum _ fun r _ => ?_
  refine ((continuous_const.mul (hmon _)).continuousOn).mul ?_
  refine ContinuousOn.log ((hmon _).continuousOn.div (hmon _).continuousOn
    fun x hx => (hmpos _ x hx).ne') fun x hx => ?_
  exact (div_pos (hmpos _ x hx) (hmpos _ x hx)).ne'

/-- **Every orbit enters the box.** If outside `logBox R` the dissipation is negative on the
class, an orbit whose coordinates stay in `[m, M]` (`m > 0`) meets `logBox (R + 1)`. -/
theorem exists_entry_logBox {N : Network S} (κ : N.RateConstants) (xref : Concentration S)
    {R : ℝ} (hR : ∀ x : Concentration S, x ∈ N.positiveCompatibilityClass xref →
      x ∉ logBox (S := S) R → N.tierDissipation κ x < 0)
    {γ : ℝ → Concentration S} (hγ0 : N.StoichCompatible xref (γ 0))
    (hsol : ∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
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
  have hΛneg : ∀ x ∈ Λ, N.tierDissipation κ x < 0 := fun x hx =>
    hR x ⟨hx.1.1, hΛpos x hx⟩ fun hb => hx.2 (hboxO x hb)
  have hcls : ∀ t, 0 ≤ t → N.StoichCompatible xref (γ t) := fun t ht =>
    hγ0.trans (N.stoichCompatible_of_forward_solution κ hsol t ht)
  by_contra hno
  push Not at hno
  have hinΛ : ∀ t, 0 ≤ t → γ t ∈ Λ := fun t ht =>
    ⟨⟨hcls t ht, fun s => hbounds t ht s⟩, fun hO => hno t ht (hOlog _ hO)⟩
  -- a uniform negative bound on `Λ`
  obtain ⟨x₁, hx₁, hmax⟩ := hΛc.exists_isMaxOn ⟨γ 0, hinΛ 0 le_rfl⟩
    ((N.continuousOn_tierDissipation κ).mono fun x hx => hΛpos x hx)
  set η := -N.tierDissipation κ x₁
  have hη : 0 < η := by have := hΛneg x₁ hx₁; simp only [η]; linarith
  have hDle : ∀ t, 0 ≤ t → N.tierDissipation κ (γ t) ≤ -η := fun t ht => by
    have := hmax (hinΛ t ht); simp only [η, neg_neg]; exact this
  have hpos : ∀ t, 0 ≤ t → (γ t).Positive := fun t ht => hΛpos _ (hinΛ t ht)
  -- `V(γ t) + η t` is antitone
  set W : ℝ → ℝ := fun t => tierEntropy (γ t) + η * t
  have hd : ∀ t, 0 ≤ t → HasDerivAt W (N.tierDissipation κ (γ t) + η * 1) t := fun t ht =>
    (N.tierEntropy_hasDerivAt κ (hpos t ht) fun s => (hasDerivAt_pi.mp (hsol t ht)) s).add
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

/-- **Permanence, trajectory form.** For a strongly endotactic network and positive rate constants,
each positive stoichiometric class contains one compact set `K` such that every forward solution
from a positive state of the class is in `K` from some time on. (This form does not assume a
mass-action flow defined on all of `ℝ^S`.) -/
theorem StronglyEndotacticStd.permanent_trajectories {N : Network S}
    (hse : N.StronglyEndotacticStd) (κ : N.RateConstants) (xref : Concentration S) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ γ : ℝ → Concentration S, γ 0 ∈ N.positiveCompatibilityClass xref →
        (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
        ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → γ t ∈ K := by
  classical
  have htd : N.TierDescending := (N.stronglyEndotacticStd_iff_tierDescending).mp hse
  obtain ⟨R, hR⟩ := exists_logBox_negative_outside_fixed htd κ xref
  set Υ : Set (Concentration S) := N.compatibilityClass xref ∩ logBox (S := S) ((R : ℝ) + 1)
  have hΥc : IsCompact Υ :=
    (isCompact_logBox (S := S) ((R : ℝ) + 1)).inter_left (N.isClosed_compatibilityClass xref)
  have hΥpos : Υ ⊆ N.positiveCompatibilityClass xref := fun x hx => ⟨hx.1, logBox_positive hx.2⟩
  obtain ⟨M, hM⟩ := htd.forward_bounded_on κ xref hΥc hΥpos
  set G : (ℝ → Concentration S) → Prop := fun δ => δ 0 ∈ Υ ∧
    ∀ t, 0 ≤ t → HasDerivAt δ (N.massActionVectorField κ (δ t)) t
  obtain ⟨m, hm, hmle⟩ := StronglyEndotacticStd.persistent_uniform hse κ G xref
    (fun δ hδ => hδ.2) (fun δ hδ => hδ.1.1)
    (g := Real.exp (-((R : ℝ) + 1))) (Real.exp_pos _) (fun δ hδ s => (hδ.1.2 s).1)
    (M := M) (fun δ hδ => hM δ hδ.1 hδ.2)
  refine ⟨N.classInteriorBox xref m M, N.isCompact_classInteriorBox xref m M,
    N.classInteriorBox_subset_positiveCompatibilityClass xref hm, fun γ hγ0 hsol => ?_⟩
  -- entry into `Υ`
  obtain ⟨m₀, hm₀, hm₀le⟩ := StronglyEndotacticStd.persistent hse κ hγ0.2 hsol
  obtain ⟨M₀, hM₀⟩ := StronglyEndotacticStd.forward_bounded hse κ hγ0.2 hsol
  obtain ⟨t₀, ht₀, hbox⟩ := exists_entry_logBox κ xref hR hγ0.1 hsol hm₀
    (M := M₀) fun t ht s => ⟨hm₀le t ht s, hM₀ t ht s⟩
  have hcls : ∀ t, 0 ≤ t → N.StoichCompatible xref (γ t) := fun t ht =>
    hγ0.1.trans (N.stoichCompatible_of_forward_solution κ hsol t ht)
  -- the shifted solution starts in `Υ`
  set δ : ℝ → Concentration S := fun t => γ (t₀ + t)
  have hδ : G δ := by
    refine ⟨⟨by simpa [δ] using (mem_compatibilityClass.mpr (hcls t₀ ht₀)), by simpa [δ] using hbox⟩,
      fun t ht => ?_⟩
    have h := hsol (t₀ + t) (by linarith)
    have hshift : HasDerivAt (fun τ : ℝ => t₀ + τ) 1 t := (hasDerivAt_id t).const_add t₀
    have := h.scomp t hshift
    simpa [δ, Function.comp_def] using this
  refine ⟨t₀, ht₀, fun t ht => ⟨hcls t (ht₀.trans ht), fun s => ?_⟩⟩
  have heq : γ t = δ (t - t₀) := by simp [δ]
  rw [heq]
  exact ⟨hmle δ hδ (t - t₀) (by linarith) s, hM δ hδ.1 hδ.2 (t - t₀) (by linarith) s⟩

/-- **Permanence of strongly endotactic networks** (Gopalkrishnan–Miller–Shiu 2014, Theorem 1.1 for fixed rates;
Anderson–Cappelletti–Kim–Nguyen 2020, Theorem 5.5). For every positive rate vector and every
genuine mass-action flow, each positive stoichiometric class has one compact subset that absorbs a
tail of every positive orbit in the class. -/
theorem StronglyEndotacticStd.structurallyPermanent {N : Network S}
    (hse : N.StronglyEndotacticStd) : N.StructurallyPermanent := by
  classical
  intro κ ϕ γf hflow
  have htd : N.TierDescending := (N.stronglyEndotacticStd_iff_tierDescending).mp hse
  refine permanentForFlow_of_entry_and_uniform_bounds hflow (fun xref hxref => ?_) hflow
  obtain ⟨R, hR⟩ := exists_logBox_negative_outside_fixed htd κ xref
  set Υ : Set (Concentration S) := N.compatibilityClass xref ∩ logBox (S := S) ((R : ℝ) + 1)
  have hΥc : IsCompact Υ :=
    (isCompact_logBox (S := S) ((R : ℝ) + 1)).inter_left (N.isClosed_compatibilityClass xref)
  have hΥpos : Υ ⊆ N.positiveCompatibilityClass xref := fun x hx => ⟨hx.1, logBox_positive hx.2⟩
  obtain ⟨hzero, hϕγ, hsolf⟩ := hflow
  refine ⟨Υ, ?_, ?_⟩
  · -- every positive orbit in the class enters `Υ`
    intro x₀ hx₀
    have hsol := hsolf x₀
    have hγ0 : (γf x₀ 0).Positive := by rw [hzero]; exact hx₀.2
    obtain ⟨m, hm, hmle⟩ := StronglyEndotacticStd.persistent hse κ hγ0 hsol
    obtain ⟨M, hM⟩ := StronglyEndotacticStd.forward_bounded hse κ hγ0 hsol
    obtain ⟨t, ht, hbox⟩ := exists_entry_logBox κ xref hR (by rw [hzero]; exact hx₀.1) hsol hm
      (M := M) fun t ht s => ⟨hmle t ht s, hM t ht s⟩
    refine ⟨⟨t, ht⟩, ?_⟩
    rw [hϕγ x₀ ⟨t, ht⟩]
    refine ⟨?_, hbox⟩
    have := N.stoichCompatible_of_forward_solution κ hsol t ht
    rw [hzero] at this
    exact hx₀.1.trans this
  · -- uniform bounds from `Υ`
    obtain ⟨M, hM⟩ := htd.forward_bounded_on κ xref hΥc hΥpos
    set G : (ℝ → Concentration S) → Prop := fun δ => ∃ x ∈ Υ, δ = γf x
    obtain ⟨m, hm, hmle⟩ := StronglyEndotacticStd.persistent_uniform hse κ G xref
      (fun δ ⟨x, _, hδ⟩ => hδ ▸ hsolf x)
      (fun δ ⟨x, hx, hδ⟩ => by rw [hδ, hzero]; exact hx.1)
      (g := Real.exp (-((R : ℝ) + 1))) (Real.exp_pos _)
      (fun δ ⟨x, hx, hδ⟩ s => by rw [hδ, hzero]; exact (hx.2 s).1)
      (M := M) (fun δ ⟨x, hx, hδ⟩ => hδ ▸ hM (γf x) (by rw [hzero]; exact hx) (hsolf x))
    refine ⟨m, M, hm, fun x hx t s => ?_⟩
    rw [hϕγ]
    exact ⟨hmle (γf x) ⟨x, hx, rfl⟩ t t.2 s,
      hM (γf x) (by rw [hzero]; exact hx) (hsolf x) t t.2 s⟩

/-- Tier-descending networks are permanent. -/
theorem TierDescending.structurallyPermanent {N : Network S} (htd : N.TierDescending) :
    N.StructurallyPermanent :=
  StronglyEndotacticStd.structurallyPermanent htd.stronglyEndotacticStd

/-- **`TierDescendingPermanenceClaim` holds for every network.** -/
theorem tierDescendingPermanenceClaim (N : Network S) : N.TierDescendingPermanenceClaim :=
  fun htd => htd.structurallyPermanent

end Network
end CRNT
