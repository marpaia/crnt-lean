import CRNT.Persistence.StronglyEndotacticVarK
import CRNT.Persistence.StronglyEndotacticConsequences
import CRNT.Dynamics.SingleLinkageStructure

/-!
# Weakly reversible networks whose linkage classes span the stoichiometric subspace

Gopalkrishnan–Miller–Shiu, Corollary 3.19: if every linkage class of a weakly reversible network
has the stoichiometric subspace of the whole network, the network is strongly endotactic; hence
(Corollary 8.9) it is permanent, also with tempered rates, and complex-balanced systems on it have
the global attractor property. This contains the one-linkage-class case.

The hypothesis is stated as: for every complex `c`, every reaction vector lies in the span of the
differences `d − c` over the complexes `d` linked to `c`.
-/

open Filter
open scoped NNReal

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Every linkage class spans the stoichiometric subspace. -/
def LinkageClassesSpan (N : Network S) : Prop :=
  ∀ c ∈ N.complexes, ∀ r : N.R, N.reactionVector r ∈ Submodule.span ℝ
    {v : S → ℝ | ∃ d ∈ N.complexes, N.Linked c d ∧ v = fun s => (d s : ℝ) - c s}

/-- In a weakly reversible network every complex is a source. -/
theorem WeaklyReversible.exists_source {N : Network S} (hwr : N.WeaklyReversible) {d : Complex S}
    (hd : d ∈ N.complexes) : ∃ r : N.R, (N.reaction r).source = d := by
  unfold complexes at hd
  rcases Finset.mem_union.mp hd with h | h
  · obtain ⟨r, -, hr⟩ := Finset.mem_image.mp h
    exact ⟨r, hr⟩
  · obtain ⟨r, -, hr⟩ := Finset.mem_image.mp h
    obtain ⟨r', hr'⟩ := hwr.exists_source_eq_target r
    exact ⟨r', hr'.trans hr⟩

/-- **Gopalkrishnan–Miller–Shiu, Corollary 3.19.** -/
theorem WeaklyReversible.stronglyEndotacticStd_of_linkageClassesSpan {N : Network S}
    (hwr : N.WeaklyReversible) (hspan : N.LinkageClassesSpan) : N.StronglyEndotacticStd := by
  classical
  refine ⟨hwr.endotactic, fun w hactive => ?_⟩
  obtain ⟨ra, hrate_ne⟩ := hactive
  obtain ⟨rmax, hmax⟩ := N.exists_isMaxSource_of_nonempty w ⟨ra⟩
  set c := (N.reaction rmax).source
  -- a complex linked to `c` at a different `w`-level
  obtain ⟨d, hd, hlink, hne⟩ : ∃ d ∈ N.complexes, N.Linked c d ∧
      complexWValue w d ≠ complexWValue w c := by
    by_contra hno
    push Not at hno
    let φ : (S → ℝ) →ₗ[ℝ] ℝ :=
      { toFun := fun v => ∑ s, w s * v s
        map_add' := fun u v => by simp [mul_add, Finset.sum_add_distrib]
        map_smul' := fun a v => by
          simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
          exact Finset.sum_congr rfl fun s _ => by ring }
    have hgen : {v : S → ℝ | ∃ d ∈ N.complexes, N.Linked c d ∧ v = fun s => (d s : ℝ) - c s} ⊆
        LinearMap.ker φ := by
      rintro v ⟨d, hd, hl, rfl⟩
      have h := hno d hd hl
      simp only [complexWValue, Network.dotProduct, exponentVector] at h
      simp only [SetLike.mem_coe, LinearMap.mem_ker, φ, LinearMap.coe_mk, AddHom.coe_mk, mul_sub,
        Finset.sum_sub_distrib]
      rw [h, sub_self]
    have hmem := Submodule.span_le.mpr hgen (hspan c (N.source_mem_complexes rmax) ra)
    apply hrate_ne
    simpa [φ, Network.wRate, Network.dotProduct] using hmem
  obtain ⟨rd, hrd⟩ := hwr.exists_source hd
  have hlow : N.wValue w rd < N.wValue w rmax := by
    have hle := hmax rd
    rw [wValue_eq_complexWValue_source, wValue_eq_complexWValue_source, hrd] at hle ⊢
    exact lt_of_le_of_ne hle hne
  have hreach : N.Reaches (N.reaction rmax).source (N.reaction rd).source := by
    rw [hrd]; exact hwr.reaches_of_linked hlink
  exact Reaches.exists_maxSource_strict_drop hmax hreach hlow

/-- **Gopalkrishnan–Miller–Shiu, Corollary 8.9 (tempered form).** -/
theorem WeaklyReversible.permanent_varK_of_linkageClassesSpan {N : Network S}
    (hwr : N.WeaklyReversible) (hspan : N.LinkageClassesSpan) {ε : ℝ} (hε : 0 < ε)
    (xref : Concentration S) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → N.RateConstants, N.Tempered ε κ →
      ∀ γ : ℝ → Concentration S, γ 0 ∈ N.positiveCompatibilityClass xref →
        (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) →
        ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → γ t ∈ K :=
  (hwr.stronglyEndotacticStd_of_linkageClassesSpan hspan).permanent_varK hε xref

/-- Fixed-rate permanence (trajectory form). -/
theorem WeaklyReversible.genuinePermanentForRates_of_linkageClassesSpan {N : Network S}
    (hwr : N.WeaklyReversible) (hspan : N.LinkageClassesSpan) (κ : N.RateConstants) :
    N.GenuinePermanentForRates κ :=
  (hwr.stronglyEndotacticStd_of_linkageClassesSpan hspan).genuinePermanentForRates κ

/-- Compact confinement from each positive state. -/
theorem WeaklyReversible.persistentFrom_of_linkageClassesSpan {N : Network S}
    (hwr : N.WeaklyReversible) (hspan : N.LinkageClassesSpan) (κ : N.RateConstants)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) : N.PersistentFrom κ x₀ :=
  (hwr.stronglyEndotacticStd_of_linkageClassesSpan hspan).persistentFrom κ hx₀

/-- One linkage class spans: the hypothesis holds for a single linkage class. -/
theorem linkageClassesSpan_of_singleLinkageClass {N : Network S} (hslc : N.SingleLinkageClass) :
    N.LinkageClassesSpan := by
  classical
  intro c hc r
  have hlinked := allComplexesLinked_of_singleLinkageClass N hslc
  have h1 : (fun s => ((N.reaction r).target s : ℝ) - c s) ∈ Submodule.span ℝ
      {v : S → ℝ | ∃ d ∈ N.complexes, N.Linked c d ∧ v = fun s => (d s : ℝ) - c s} :=
    Submodule.subset_span ⟨_, N.target_mem_complexes r,
      hlinked c hc _ (N.target_mem_complexes r), rfl⟩
  have h2 : (fun s => ((N.reaction r).source s : ℝ) - c s) ∈ Submodule.span ℝ
      {v : S → ℝ | ∃ d ∈ N.complexes, N.Linked c d ∧ v = fun s => (d s : ℝ) - c s} :=
    Submodule.subset_span ⟨_, N.source_mem_complexes r,
      hlinked c hc _ (N.source_mem_complexes r), rfl⟩
  have heq : N.reactionVector r = (fun s => ((N.reaction r).target s : ℝ) - c s) -
      (fun s => ((N.reaction r).source s : ℝ) - c s) := by
    funext s; simp [reactionVector_apply]
  rw [heq]
  exact Submodule.sub_mem _ h1 h2

/-- **Rank one.** A weakly reversible network without trivial reactions and with a
one-dimensional stoichiometric subspace has linkage classes spanning that subspace. -/
theorem WeaklyReversible.linkageClassesSpan_of_stoichRank_one {N : Network S}
    (hwr : N.WeaklyReversible) (hnt : ∀ r : N.R, (N.reaction r).source ≠ (N.reaction r).target)
    (hrank : N.stoichRank = 1) : N.LinkageClassesSpan := by
  classical
  intro c hc r
  obtain ⟨rc, hrc⟩ := hwr.exists_source hc
  set v := N.reactionVector rc
  have hv0 : v ≠ 0 := by
    intro h
    apply hnt rc
    funext s
    have := congrFun h s
    simp only [v, reactionVector_apply, Pi.zero_apply, sub_eq_zero] at this
    exact_mod_cast this.symm
  have hvS : v ∈ N.stoichSubspace := N.reactionVector_mem_stoichSubspace rc
  have hS : Submodule.span ℝ {v} = N.stoichSubspace := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem v _).mpr hvS
    · rw [finrank_span_singleton hv0]; exact hrank.symm
  have hvgen : v ∈ Submodule.span ℝ
      {w : S → ℝ | ∃ d ∈ N.complexes, N.Linked c d ∧ w = fun s => (d s : ℝ) - c s} := by
    apply Submodule.subset_span
    refine ⟨(N.reaction rc).target, N.target_mem_complexes rc, ?_, ?_⟩
    · rw [← hrc]; exact linked_of_reaction N rc
    · funext s; simp [v, reactionVector_apply, hrc]
  have hr : N.reactionVector r ∈ Submodule.span ℝ {v} := by
    rw [hS]; exact N.reactionVector_mem_stoichSubspace r
  exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hvgen)) hr

/-- **Weakly reversible networks of stoichiometric rank one are permanent** (tempered rates). -/
theorem WeaklyReversible.permanent_varK_of_stoichRank_one {N : Network S}
    (hwr : N.WeaklyReversible) (hnt : ∀ r : N.R, (N.reaction r).source ≠ (N.reaction r).target)
    (hrank : N.stoichRank = 1) {ε : ℝ} (hε : 0 < ε) (xref : Concentration S) :
    ∃ K : Set (Concentration S), IsCompact K ∧ K ⊆ N.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → N.RateConstants, N.Tempered ε κ →
      ∀ γ : ℝ → Concentration S, γ 0 ∈ N.positiveCompatibilityClass xref →
        (∀ t, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) →
        ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → γ t ∈ K :=
  hwr.permanent_varK_of_linkageClassesSpan (hwr.linkageClassesSpan_of_stoichRank_one hnt hrank)
    hε xref

end Network
end CRNT
