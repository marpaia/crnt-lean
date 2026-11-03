import CRNT.Persistence.LinkageSpanPermanence

/-!
# A two-linkage-class network covered by `LinkageClassesSpan`

`X ⇌ Y`, `2X ⇌ 2Y` is weakly reversible, has two linkage classes (`not_singleLinkageClass`:
undirected edges preserve total molecularity, so `X` and `2X` are not linked), and each linkage
class spans the stoichiometric subspace `ℝ (Y − X)` (`linkageClassesSpan`). Hence it is strongly
endotactic and permanent with tempered rates (`stronglyEndotactic`, `permanent_varK`), which the
single-linkage theorem does not cover.
-/

namespace CRNT
namespace Examples
namespace TwoLinkageSpan

open Network

/-- `X ⇌ Y`, `2X ⇌ 2Y`. -/
abbrev net : Network (Fin 2) :=
  ⟨Fin 4, inferInstance, inferInstance, fun r =>
    if r = 0 then ⟨![1, 0], ![0, 1]⟩ else if r = 1 then ⟨![0, 1], ![1, 0]⟩
    else if r = 2 then ⟨![2, 0], ![0, 2]⟩ else ⟨![0, 2], ![2, 0]⟩⟩

theorem weaklyReversible : net.WeaklyReversible := by
  intro r
  fin_cases r
  · exact Relation.ReflTransGen.single ⟨1, rfl, rfl⟩
  · exact Relation.ReflTransGen.single ⟨0, rfl, rfl⟩
  · exact Relation.ReflTransGen.single ⟨3, rfl, rfl⟩
  · exact Relation.ReflTransGen.single ⟨2, rfl, rfl⟩

/-- Reactions preserve total molecularity. -/
theorem total_eq (r : net.R) :
    (net.reaction r).source 0 + (net.reaction r).source 1 =
      (net.reaction r).target 0 + (net.reaction r).target 1 := by
  fin_cases r <;> rfl

theorem linked_total {c d : Complex (Fin 2)} (h : net.Linked c d) : c 0 + c 1 = d 0 + d 1 := by
  induction h with
  | refl => rfl
  | @tail e f _ hef ih =>
      rw [ih]
      rcases hef with ⟨r, hs, ht⟩ | ⟨r, hs, ht⟩
      · rw [← hs, ← ht]; exact total_eq r
      · rw [← hs, ← ht]; exact (total_eq r).symm

theorem not_singleLinkageClass : ¬ net.SingleLinkageClass := by
  intro h
  have hX : (![1, 0] : Complex (Fin 2)) ∈ net.complexes := net.source_mem_complexes 0
  have h2X : (![2, 0] : Complex (Fin 2)) ∈ net.complexes := net.source_mem_complexes 2
  have := linked_total (allComplexesLinked_of_singleLinkageClass net h _ hX _ h2X)
  simp at this

/-- The direction `Y − X`. -/
def u : Fin 2 → ℝ := ![-1, 1]

theorem complexes_cases {c : Complex (Fin 2)} (hc : c ∈ net.complexes) :
    c = ![1, 0] ∨ c = ![0, 1] ∨ c = ![2, 0] ∨ c = ![0, 2] := by
  simp only [Network.complexes, Finset.mem_union, Finset.mem_image, Finset.mem_univ,
    true_and] at hc
  rcases hc with ⟨r, rfl⟩ | ⟨r, rfl⟩ <;> fin_cases r <;> simp

theorem reactionVector_eq (r : net.R) :
    ∃ ν : ℝ, net.reactionVector r = ν • u := by
  fin_cases r
  · exact ⟨1, by funext s; fin_cases s <;> simp [reactionVector_apply, u]⟩
  · exact ⟨-1, by funext s; fin_cases s <;> simp [reactionVector_apply, u]⟩
  · exact ⟨2, by funext s; fin_cases s <;> simp [reactionVector_apply, u]⟩
  · exact ⟨-2, by funext s; fin_cases s <;> simp [reactionVector_apply, u]⟩

/-- If some complex linked to `c` differs from `c` by a nonzero multiple of `u`, every reaction
vector lies in the span. -/
theorem span_of_partner {c d : Complex (Fin 2)} (hd : d ∈ net.complexes) (hl : net.Linked c d)
    {μ : ℝ} (hμ : μ ≠ 0) (hdc : (fun s => (d s : ℝ) - c s) = μ • u) (r : net.R) :
    net.reactionVector r ∈ Submodule.span ℝ
      {v : Fin 2 → ℝ | ∃ d ∈ net.complexes, net.Linked c d ∧ v = fun s => (d s : ℝ) - c s} := by
  obtain ⟨ν, hν⟩ := reactionVector_eq r
  have hmem : (fun s => (d s : ℝ) - c s) ∈ Submodule.span ℝ
      {v : Fin 2 → ℝ | ∃ d ∈ net.complexes, net.Linked c d ∧ v = fun s => (d s : ℝ) - c s} :=
    Submodule.subset_span ⟨d, hd, hl, rfl⟩
  have : net.reactionVector r = (ν / μ) • (fun s => (d s : ℝ) - c s) := by
    rw [hν, hdc, smul_smul, div_mul_cancel₀ ν hμ]
  rw [this]
  exact Submodule.smul_mem _ _ hmem

theorem linkageClassesSpan : net.LinkageClassesSpan := by
  intro c hc r
  have e01 : net.Linked ![1, 0] ![0, 1] :=
    Relation.ReflTransGen.single (Or.inl ⟨0, rfl, rfl⟩)
  have e10 : net.Linked ![0, 1] ![1, 0] :=
    Relation.ReflTransGen.single (Or.inl ⟨1, rfl, rfl⟩)
  have e23 : net.Linked ![2, 0] ![0, 2] :=
    Relation.ReflTransGen.single (Or.inl ⟨2, rfl, rfl⟩)
  have e32 : net.Linked ![0, 2] ![2, 0] :=
    Relation.ReflTransGen.single (Or.inl ⟨3, rfl, rfl⟩)
  rcases complexes_cases hc with rfl | rfl | rfl | rfl
  · exact span_of_partner (net.target_mem_complexes 0) e01 one_ne_zero
      (by funext s; fin_cases s <;> simp [u]) r
  · exact span_of_partner (net.target_mem_complexes 1) e10 (by norm_num : (-1 : ℝ) ≠ 0)
      (by funext s; fin_cases s <;> simp [u]) r
  · exact span_of_partner (net.target_mem_complexes 2) e23 (by norm_num : (2 : ℝ) ≠ 0)
      (by funext s; fin_cases s <;> simp [u]) r
  · exact span_of_partner (net.target_mem_complexes 3) e32 (by norm_num : (-2 : ℝ) ≠ 0)
      (by funext s; fin_cases s <;> simp [u]) r

theorem stronglyEndotactic : net.StronglyEndotacticStd :=
  weaklyReversible.stronglyEndotacticStd_of_linkageClassesSpan linkageClassesSpan

/-- Permanence with tempered rates for a network with two linkage classes. -/
theorem permanent_varK {ε : ℝ} (hε : 0 < ε) (xref : Concentration (Fin 2)) :
    ∃ K : Set (Concentration (Fin 2)), IsCompact K ∧ K ⊆ net.positiveCompatibilityClass xref ∧
      ∀ κ : ℝ → net.RateConstants, net.Tempered ε κ →
      ∀ γ : ℝ → Concentration (Fin 2), γ 0 ∈ net.positiveCompatibilityClass xref →
        (∀ t, 0 ≤ t → HasDerivAt γ (net.massActionVectorField (κ t) (γ t)) t) →
        ∃ T, 0 ≤ T ∧ ∀ t, T ≤ t → γ t ∈ K :=
  weaklyReversible.permanent_varK_of_linkageClassesSpan linkageClassesSpan hε xref

end TwoLinkageSpan
end Examples
end CRNT
