import CRNT.Persistence.EndotacticFloor
import CRNT.Persistence.PlanarRegion
import CRNT.Dynamics.GlobalPermanence

/-!
# Two-species endotactic networks are bounded and persistent

Craciun–Nazarov–Pantea 2013: mass-action systems of a two-species network that is endotactic in
the standard sense are bounded and stay away from the boundary.  Here, for rate constants
varying in time inside `[ε, 1/ε]` (the variable-k setting of the Extended Persistence
Conjecture), every forward solution from a positive state stays in a compact box `[η, B]^S`
determined by the start point and `ε`
(`twoSpecies_endotacticStd_confined_varK`).

Proof: the compact planar region `exists_planar_region` for the set of complex differences,
the endotactic field condition `dot_massActionField_nonneg_of_endotacticStd` on every facet (its
normals are fixed before the slack, so the ratio constant is fixed first), and the band form of
the barrier lemma.  Positivity in the band comes from the region itself, so no a priori bound
on the solution is needed.

Consequences: structural persistence (`twoSpecies_endotacticStd_structurallyPersistent`); in
particular two-species weakly reversible networks are structurally persistent
(`twoSpecies_weaklyReversible_structurallyPersistent`), the two-species case of the Persistence
Conjecture without a boundedness hypothesis.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Finset Real CRNT.Persistence CRNT.PolyhedralBarrier

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **Two-species endotactic confinement, variable rates.** For a two-species network that is
endotactic in the standard sense, with rate constants varying in time inside `[ε, 1/ε]`, there is
a box `[η, B]` with `η > 0`, depending only on the start point and `ε`, containing every forward
solution from that start point for all `t ≥ 0`. -/
theorem twoSpecies_endotacticStd_confined_varK (N : Network S) (hS : Fintype.card S = 2)
    (κ : ℝ → N.RateConstants) (hend : N.EndotacticStd) {ε : ℝ} (hε : 0 < ε)
    (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ η B, 0 < η ∧ ∀ γ : ℝ → Concentration S, γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ γ t s ∧ γ t s ≤ B := by
  obtain e : S ≃ Fin 2 := Fintype.equivFinOfCardEq hS
  -- complex differences, closed under permutations
  obtain ⟨D, hD⟩ : ∃ D : Complex S × Complex S → Fin 2 → ℝ,
      D = fun p q => ((p.1 (e.symm q) : ℝ) - p.2 (e.symm q)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Finset (Fin 2 → ℝ), H =
      (Finset.univ : Finset (Equiv.Perm (Fin 2))).biUnion
        fun ρ => (N.complexes ×ˢ N.complexes).image fun p => D p ∘ ρ := ⟨_, rfl⟩
  have hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin 2), h ∘ ρ ∈ H := by
    intro h hh ρ'
    rw [hH] at hh ⊢
    simp only [mem_biUnion, mem_univ, true_and, mem_image] at hh ⊢
    obtain ⟨ρ, p, hp, rfl⟩ := hh
    exact ⟨ρ * ρ', p, hp, by funext q; simp⟩
  have hDmem : ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes, D (c, c') ∈ H := by
    intro c hc c' hc'
    rw [hH]
    simp only [mem_biUnion, mem_univ, true_and, mem_image]
    exact ⟨1, (c, c'), mem_product.mpr ⟨hc, hc'⟩, by funext q; simp⟩
  -- transport to `Fin 2`
  have htr : ∀ (a x : S → ℝ), fdot (a ∘ e.symm) (x ∘ e.symm) = ∑ s, a s * x s := by
    intro a x
    unfold fdot
    exact Equiv.sum_comp e.symm (fun s => a s * x s)
  have htrlog : ∀ (h : Fin 2 → ℝ) (x : S → ℝ),
      ∑ q, h q * log (x (e.symm q)) = ∑ s, h (e s) * log (x s) := by
    intro h x
    rw [← Equiv.sum_comp e (fun q => h q * log (x (e.symm q)))]
    simp
  -- the normals, fixed before the slack
  obtain ⟨ι, hFι, hNι, nrm, hreg⟩ := exists_planar_region H hsym
  have := hFι
  have := hNι
  set nS : ι → S → ℝ := fun i s => nrm i (e s) with hnS
  have hdotS : ∀ i (x : S → ℝ), fdot (nrm i) (x ∘ e.symm) = ∑ s, nS i s * x s := by
    intro i x
    have : nrm i = nS i ∘ e.symm := by funext q; simp [hnS]
    rw [this, htr]
  -- the ratio constant and the slack
  obtain ⟨C, -, hC⟩ := exists_ratio_bound
    (fun (i : ι) (r : N.R) => ∑ s, (-nS i s) * N.reactionVector r s)
  obtain ⟨δ, hδ⟩ := N.exists_slack_varK_ratio hε C
  obtain ⟨c, R', η, B, hR', hη, hstart, hbox, hposband, hvalid⟩ :=
    hreg δ (x₀ ∘ e.symm) (fun q => hx₀ _)
  refine ⟨η, B, hη, fun γ hγx hsol => ?_⟩
  set L : ι → ((S → ℝ) →L[ℝ] ℝ) := fun i =>
    ∑ s, nS i s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s with hL
  have hLapp : ∀ i (x : S → ℝ), L i x = ∑ s, nS i s * x s := by
    intro i x
    simp [hL, smul_eq_mul]
  have hγcont : ContinuousOn γ (Set.Ici 0) := fun t ht =>
    (hsol t ht).continuousAt.continuousWithinAt
  have hinv := barrier_le_of_local_descent_in_band (L := L) (b := c) (R := 0) (R' := R') hR'
    hγcont hsol (by
      rw [barrier_le_iff]
      intro i
      rw [hLapp, ← hdotS, hγx]
      linarith [hstart i]) (by
      intro t ht hlev hband i hact
      set x := γ t with hx
      set σ := barrier L c x with hσ
      have hall : ∀ i', fdot (nrm i') (x ∘ e.symm) ≤ c i' + σ := by
        intro i'
        have := le_barrier L c x i'
        rw [hLapp, ← hdotS] at this
        linarith
      have hacteq : fdot (nrm i) (x ∘ e.symm) = c i + σ := by
        rw [hLapp, ← hdotS] at hact
        linarith
      have hxpos : x.Positive := fun s => by
        have := hposband σ hlev hband (x ∘ e.symm) hall (e s)
        simpa using this
      have hv := hvalid σ hlev hband (x ∘ e.symm) hall i hacteq
      have hnn := N.dot_massActionField_nonneg_of_endotacticStd (κ t) hend hxpos
        (fun s => -nS i s) δ C (fun r r' h => hC i r r' h) (hδ (κ t) (fun r => hκ t r)) (by
        intro c₁ hc₁ c₂ hc₂ hneg
        have hmem := hDmem c₁ hc₁ c₂ hc₂
        have hdot : fdot (nrm i) (D (c₁, c₂)) = ∑ s, nS i s * ((c₁ s : ℝ) - c₂ s) := by
          have : D (c₁, c₂) = (fun s => ((c₁ s : ℝ) - c₂ s)) ∘ e.symm := by
            rw [hD]; rfl
          rw [this, hdotS]
        have hpos' : 0 < fdot (nrm i) (D (c₁, c₂)) := by
          rw [hdot]
          have : ∑ s, (-nS i s) * ((c₁ s : ℝ) - c₂ s) = -∑ s, nS i s * ((c₁ s : ℝ) - c₂ s) := by
            rw [← sum_neg_distrib]; exact sum_congr rfl fun s _ => by ring
          linarith
        have := hv (D (c₁, c₂)) hmem hpos'
        simp only [Function.comp_apply] at this
        rw [htrlog, hD] at this
        simpa using this)
      rw [hLapp]
      have : ∑ s, (-nS i s) * N.massActionVectorField (κ t) x s =
          -∑ s, nS i s * N.massActionVectorField (κ t) x s := by
        rw [← sum_neg_distrib]; exact sum_congr rfl fun s _ => by ring
      linarith)
  intro t ht s
  have hb := hinv t ht
  rw [barrier_le_iff] at hb
  have hin : ∀ i, fdot (nrm i) (γ t ∘ e.symm) ≤ c i := by
    intro i
    have := hb i
    rw [hLapp, ← hdotS] at this
    linarith
  have := hbox _ hin (e s)
  simpa using this

/-- **Two-species endotactic confinement**, constant rates. -/
theorem twoSpecies_endotacticStd_confined (N : Network S) (hS : Fintype.card S = 2)
    (κ : N.RateConstants) (hend : N.EndotacticStd) {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ η B, 0 < η ∧ ∀ γ : ℝ → Concentration S, γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ γ t s ∧ γ t s ≤ B := by
  obtain ⟨ε, hε, hb⟩ := N.exists_rate_bounds κ
  exact N.twoSpecies_endotacticStd_confined_varK hS (fun _ => κ) hend hε (fun _ r => hb r) hx₀

/-- **Two-species endotactic networks are persistent from every positive state.** -/
theorem twoSpecies_endotacticStd_persistentFrom (N : Network S) (hS : Fintype.card S = 2)
    (κ : N.RateConstants) (hend : N.EndotacticStd) {x₀ : Concentration S}
    (hx₀ : x₀.Positive) : N.PersistentFrom κ x₀ := by
  obtain ⟨η, B, hη, h⟩ := N.twoSpecies_endotacticStd_confined hS κ hend hx₀
  refine ⟨Set.univ.pi fun _ => Set.Icc η B, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1, fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact h Γ hΓ0 hΓd t ht s

/-- **Two-species endotactic networks are structurally persistent** (Craciun–Nazarov–Pantea
2013, persistence and boundedness half). -/
theorem twoSpecies_endotacticStd_structurallyPersistent (N : Network S)
    (hS : Fintype.card S = 2) (hend : N.EndotacticStd) : N.StructurallyPersistent :=
  fun κ _ hx₀ => N.twoSpecies_endotacticStd_persistentFrom hS κ hend hx₀

/-- **Two-species weakly reversible networks are structurally persistent**: the two-species case
of the Persistence Conjecture, with no boundedness hypothesis. -/
theorem twoSpecies_weaklyReversible_structurallyPersistent (N : Network S)
    (hS : Fintype.card S = 2) (hwr : N.WeaklyReversible) : N.StructurallyPersistent :=
  N.twoSpecies_endotacticStd_structurallyPersistent hS hwr.endotacticStd

/-- Variable-k form: every forward solution from `x₀` stays in one compact set of positive
states (Extended Persistence Conjecture, two species, endotactic networks). -/
theorem twoSpecies_endotacticStd_confined_compact_varK (N : Network S)
    (hS : Fintype.card S = 2) (κ : ℝ → N.RateConstants) (hend : N.EndotacticStd) {ε : ℝ}
    (hε : 0 < ε) (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ K₀ : Set (Concentration S), IsCompact K₀ ∧ (∀ y ∈ K₀, y.Positive) ∧
      ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∀ t : ℝ, 0 ≤ t → Γ t ∈ K₀ := by
  obtain ⟨η, B, hη, h⟩ := N.twoSpecies_endotacticStd_confined_varK hS κ hend hε hκ hx₀
  refine ⟨Set.univ.pi fun _ => Set.Icc η B, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1, fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact h Γ hΓ0 hΓd t ht s

/-- **Orbitwise permanence of two-species endotactic networks**: every positive orbit of every
genuine mass-action flow is eventually confined to a compact set of positive states.  (The
class-uniform absorbing set of `StructurallyPermanent` is not proved here.) -/
theorem twoSpecies_endotacticStd_orbitwisePermanent (N : Network S)
    (hS : Fintype.card S = 2) (hend : N.EndotacticStd) : N.StructurallyOrbitwisePermanent := by
  intro κ ϕ γ hflow x₀ hx₀
  obtain ⟨K, hK, hKpos, hKin⟩ := N.twoSpecies_endotacticStd_persistentFrom hS κ hend hx₀
  refine ⟨K, hK, hKpos, Set.univ, Filter.univ_mem, ?_⟩
  refine closure_minimal ?_ hK.isClosed
  rintro _ ⟨t, -, y, hy, rfl⟩
  rw [Set.mem_singleton_iff] at hy
  subst hy
  rw [hflow.2.1 y t]
  exact hKin (γ y) (hflow.1 y) (fun t ht => hflow.2.2 y t ht) t t.2

end Network
end CRNT
