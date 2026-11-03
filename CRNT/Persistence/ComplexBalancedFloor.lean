import CRNT.Persistence.ZeroSeparatingRegion
import CRNT.Persistence.FieldDecomposition
import CRNT.Geometry.PolyhedralBarrier
import CRNT.Dynamics.OrbitRegularity

/-!
# Bounded complex-balanced trajectories stay away from the boundary

`complexBalanced_forward_floor`: for a complex-balanced mass-action system, every forward
solution starting at a positive state and bounded above has all coordinates bounded below by a
positive constant for all `t ≥ 0`.

The proof combines three facts.  `exists_zsh` builds, for the set of complex differences closed
under permutations of species, a polyhedral region containing the starting point and lying in
`{x ≥ η}`, whose active facets near its boundary satisfy the validity condition.
`dot_massActionField_nonneg` turns that condition into nonnegativity of the field along every
active inward normal.  `PolyhedralBarrier.barrier_le_of_local_descent_in_band` then keeps the
trajectory inside the region.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Finset Real CRNT.Persistence CRNT.PolyhedralBarrier

variable {S : Type} [DecidableEq S] [Fintype S]

theorem complexBalanced_forward_floor (N : Network S) (κ : N.RateConstants)
    {xs : Concentration S} (hxs : xs.Positive) (hcb : N.IsComplexBalanced κ xs)
    {γ : ℝ → Concentration S} (hγ0 : (γ 0).Positive)
    (hsol : ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField κ (γ t)) t)
    {M : ℝ} (hbdd : ∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M) :
    ∃ η, 0 < η ∧ ∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ γ t s := by
  set n := Fintype.card S with hn
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · refine ⟨1, one_pos, fun t _ s => ?_⟩
    exact absurd (Fintype.card_pos_iff.mpr ⟨s⟩) (by omega)
  have hpos := N.orbit_pos_forward κ hγ0 hbdd hsol
  obtain ⟨e⟩ : Nonempty (S ≃ Fin n) := ⟨Fintype.equivFin S⟩
  obtain ⟨M', hM'1, hMM'⟩ : ∃ M', 1 ≤ M' ∧ M ≤ M' := ⟨max M 1, le_max_right _ _, le_max_left _ _⟩
  -- complex differences, closed under permutations
  obtain ⟨D, hD⟩ : ∃ D : Complex S × Complex S → Fin n → ℝ,
      D = fun p q => ((p.1 (e.symm q) : ℝ) - p.2 (e.symm q)) := ⟨_, rfl⟩
  obtain ⟨H, hH⟩ : ∃ H : Finset (Fin n → ℝ), H =
      (Finset.univ : Finset (Equiv.Perm (Fin n))).biUnion
        fun ρ => (N.complexes ×ˢ N.complexes).image fun p => D p ∘ ρ := ⟨_, rfl⟩
  have hsym : ∀ h ∈ H, ∀ ρ : Equiv.Perm (Fin n), h ∘ ρ ∈ H := by
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
  -- the slack
  obtain ⟨δ, hδlt⟩ : ∃ δ : ℝ, ∀ c ∈ N.complexes, ∀ c' ∈ N.complexes,
      |∑ s, ((c s : ℝ) - c' s) * log (xs s)| < δ := by
    refine ⟨1 + ∑ p ∈ N.complexes ×ˢ N.complexes,
      |∑ s, ((p.1 s : ℝ) - p.2 s) * log (xs s)|, fun c hc c' hc' => ?_⟩
    have := single_le_sum (f := fun p : Complex S × Complex S =>
      |∑ s, ((p.1 s : ℝ) - p.2 s) * log (xs s)|) (fun _ _ => abs_nonneg _)
      (mem_product.mpr ⟨hc, hc'⟩ : (c, c') ∈ N.complexes ×ˢ N.complexes)
    simp only at this
    linarith
  -- transport to `Fin n`
  have htr : ∀ (a x : S → ℝ), fdot (a ∘ e.symm) (x ∘ e.symm) = ∑ s, a s * x s := by
    intro a x
    unfold fdot
    exact Equiv.sum_comp e.symm (fun s => a s * x s)
  have htrlog : ∀ (h : Fin n → ℝ) (x : S → ℝ),
      ∑ q, h q * log (x (e.symm q)) = ∑ s, h (e s) * log (x s) := by
    intro h x
    rw [← Equiv.sum_comp e (fun q => h q * log (x (e.symm q)))]
    simp
  obtain ⟨ι, hFι, hNι, a, b, R', η, hR', hη, hstart, hfloor, hvalid⟩ :=
    exists_zsh (by omega : 1 ≤ n) H hsym δ M' hM'1 (γ 0 ∘ e.symm) (fun q => hγ0 _)
  haveI := hFι
  haveI := hNι
  -- the inward normals in species coordinates
  set aS : ι → S → ℝ := fun i s => a i (e s) with haS
  have hdotS : ∀ i (x : S → ℝ), fdot (a i) (x ∘ e.symm) = ∑ s, aS i s * x s := by
    intro i x
    have : a i = aS i ∘ e.symm := by funext q; simp [haS]
    rw [this, htr]
  set L : ι → ((S → ℝ) →L[ℝ] ℝ) := fun i =>
    -∑ s, aS i s • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : S => ℝ) s with hL
  have hLapp : ∀ i (x : S → ℝ), L i x = -∑ s, aS i s * x s := by
    intro i x
    simp [hL, ContinuousLinearMap.sum_apply, smul_eq_mul]
  set b' : ι → ℝ := fun i => -b i with hb'
  have hγcont : ContinuousOn γ (Set.Ici 0) := fun t ht =>
    (hsol t ht).continuousAt.continuousWithinAt
  have hinv := barrier_le_of_local_descent_in_band (L := L) (b := b') (R := 0) (R' := R') hR'
    hγcont hsol (by
      rw [barrier_le_iff]
      intro i
      rw [hLapp, hb']
      have := hstart i
      rw [hdotS] at this
      linarith) (by
      intro t ht hlev hband i hact
      set x := γ t with hx
      set σ := barrier L b' x with hσ
      have hall : ∀ i', b i' - σ ≤ fdot (a i') (x ∘ e.symm) := by
        intro i'
        have := le_barrier L b' x i'
        rw [hLapp, hdotS] at *
        simp only [hb'] at this
        linarith
      have hacteq : fdot (a i) (x ∘ e.symm) = b i - σ := by
        rw [hLapp] at hact
        rw [hdotS]
        simp only [hb'] at hact
        linarith
      have hv := hvalid σ hlev hband (x ∘ e.symm) (fun q => hpos t ht _)
        (fun q => le_trans (hbdd t ht _) hMM') hall i hacteq
      have hnn := N.dot_massActionField_nonneg κ hxs hcb (hpos t ht) (aS i) δ hδlt (by
        intro c hc c' hc' hneg
        have hmem := hDmem c hc c' hc'
        have hdot : fdot (a i) (D (c, c')) = ∑ s, aS i s * ((c s : ℝ) - c' s) := by
          have : D (c, c') = (fun s => ((c s : ℝ) - c' s)) ∘ e.symm := by
            rw [hD]; rfl
          rw [this, hdotS]
        have := hv (D (c, c')) hmem (by rw [hdot]; exact hneg)
        simp only [Function.comp_apply] at this
        rw [htrlog, hD] at this
        simpa using this)
      rw [hLapp]
      linarith)
  refine ⟨η, hη, fun t ht s => ?_⟩
  have hb := hinv t ht
  rw [barrier_le_iff] at hb
  have hin : ∀ i, b i ≤ fdot (a i) (γ t ∘ e.symm) := by
    intro i
    have := hb i
    rw [hLapp, hb'] at this
    rw [hdotS]; linarith
  have := hfloor _ hin (e s)
  simpa using this

end Network
end CRNT
