import CRNT.Persistence.WeaklyReversibleFloor
import CRNT.Persistence.UniformFieldBound
import CRNT.Persistence.ConservativePersistence

/-!
# Bounded variable-k weakly reversible trajectories stay away from the boundary

Rate constants may depend on time, `κ t`, with `ε ≤ (κ t).k r ≤ 1/ε`.  The proof of
`weaklyReversible_forward_floor_uniform` goes through unchanged: the barrier lemma accepts any
velocity, the slack `δ = |R|/ε²` works at every time (`exists_slack_varK`), and forward
positivity uses a field lower bound uniform in the rates (`orbit_pos_forward_varK`).

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Finset Real CRNT.Persistence CRNT.PolyhedralBarrier

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A slack `δ` that works for every rate vector in `[ε, 1/ε]`. -/
theorem exists_slack_varK (N : Network S) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, ∀ κ : N.RateConstants, (∀ r, ε ≤ κ.k r ∧ κ.k r ≤ 1 / ε) →
      ∀ i j : N.R, (Fintype.card N.R : ℝ) * κ.k i ≤ exp δ * κ.k j := by
  set n : ℝ := (Fintype.card N.R : ℝ)
  have hn : 0 ≤ n := Nat.cast_nonneg _
  refine ⟨n / ε ^ 2, fun κ hκ i j => ?_⟩
  have h1 : n * κ.k i ≤ n * (1 / ε) := mul_le_mul_of_nonneg_left (hκ i).2 hn
  have h2 : n / ε ^ 2 ≤ exp (n / ε ^ 2) := by linarith [add_one_le_exp (n / ε ^ 2)]
  have h3 : n * (1 / ε) = n / ε ^ 2 * ε := by field_simp
  have h4 : n / ε ^ 2 * ε ≤ exp (n / ε ^ 2) * κ.k j :=
    mul_le_mul h2 (hκ j).1 hε.le (exp_pos _).le
  linarith

open Set in
/-- Forward positivity for time-dependent rate constants bounded by `K`. -/
theorem orbit_pos_forward_varK (N : Network S) (κ : ℝ → N.RateConstants) {K B : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t r, (κ t).k r ≤ K)
    {Γ : ℝ → Concentration S} (hΓ0 : (Γ 0).Positive)
    (hΓbdd : ∀ t : ℝ, 0 ≤ t → (Γ t).Nonnegative → ∀ s, Γ t s ≤ B)
    (hΓd : ∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) :
    ∀ t : ℝ, 0 ≤ t → (Γ t).Positive := by
  obtain ⟨L, hL, hbound⟩ := N.exists_field_lower_bound_uniform hK0 B
  have hcs : ∀ s : S, ContinuousOn (fun t => Γ t s) (Ici 0) := by
    intro s t ht
    exact (((hasDerivAt_pi.mp (hΓd t ht)) s).continuousAt).continuousWithinAt
  intro T hT
  by_contra hcon
  obtain ⟨s₀, hs₀⟩ : ∃ s, Γ T s ≤ 0 := by
    by_contra h
    simp only [not_exists, not_le] at h
    exact hcon h
  set A : Set ℝ := ⋃ s : S, {t ∈ Ici (0 : ℝ) | Γ t s ≤ 0} with hA
  have hAne : A.Nonempty := ⟨T, mem_iUnion.mpr ⟨s₀, ⟨hT, hs₀⟩⟩⟩
  have hAcl : IsClosed A := by
    rw [hA]
    exact isClosed_iUnion_of_finite fun s =>
      isClosed_Ici.isClosed_le (hcs s) continuousOn_const
  have hAbdd : BddBelow A := by
    refine ⟨0, fun t ht => ?_⟩
    obtain ⟨s, hs⟩ := mem_iUnion.mp ht
    exact hs.1
  set t₁ := sInf A with ht₁def
  have ht₁A : t₁ ∈ A := hAcl.csInf_mem hAne hAbdd
  obtain ⟨s₁, hs₁mem⟩ := mem_iUnion.mp ht₁A
  have ht₁0 : 0 ≤ t₁ := hs₁mem.1
  have hs₁ : Γ t₁ s₁ ≤ 0 := hs₁mem.2
  have hbefore : ∀ t : ℝ, 0 ≤ t → t < t₁ → (Γ t).Positive := by
    intro t ht htlt s
    by_contra hle
    rw [not_lt] at hle
    exact absurd (csInf_le hAbdd (mem_iUnion.mpr ⟨s, ⟨ht, hle⟩⟩)) (not_le.mpr htlt)
  rcases eq_or_lt_of_le ht₁0 with ht₁eq | ht₁pos
  · rw [← ht₁eq] at hs₁
    exact absurd (hΓ0 s₁) (not_lt.mpr hs₁)
  · have key : ∀ t ∈ Ico (0 : ℝ) t₁, Γ 0 s₁ * Real.exp (-(L * t)) ≤ Γ t s₁ := by
      intro t ht
      refine ge_mul_exp_of_forward_deriv_ge ht.1
        (fun τ hτ => (hasDerivAt_pi.mp (hΓd τ hτ.1)) s₁) ?_
      intro τ hτ
      have hτlt : τ < t₁ := lt_of_le_of_lt hτ.2 ht.2
      have hnn : (Γ τ).Nonnegative := (hbefore τ hτ.1 hτlt).nonnegative
      exact hbound (κ τ) (hK τ) (Γ τ) hnn (hΓbdd τ hτ.1 hnn) s₁
    have hclos : closure (Ico (0 : ℝ) t₁) = Icc 0 t₁ := closure_Ico (ne_of_lt ht₁pos)
    have hcont₁ : ContinuousOn (fun t : ℝ => Γ 0 s₁ * Real.exp (-(L * t)))
        (closure (Ico (0 : ℝ) t₁)) :=
      (continuous_const.mul
        (Real.continuous_exp.comp ((continuous_const.mul continuous_id).neg))).continuousOn
    have hcont₂ : ContinuousOn (fun t => Γ t s₁) (closure (Ico (0 : ℝ) t₁)) := by
      rw [hclos]
      exact (hcs s₁).mono fun t ht => ht.1
    have ht₁mem : t₁ ∈ closure (Ico (0 : ℝ) t₁) := by
      rw [hclos]
      exact ⟨ht₁0, le_rfl⟩
    have hlim := le_on_closure key hcont₁ hcont₂ ht₁mem
    exact absurd (lt_of_lt_of_le (mul_pos (hΓ0 s₁) (Real.exp_pos _)) hlim) (not_lt.mpr hs₁)


/-- **Variable-k floor.** For a weakly reversible network whose rate constants vary in time
inside `[ε, 1/ε]`, every forward solution from `x₀` bounded by `M` has a positive lower bound
depending only on `x₀`, `M`, and `ε`.  This is the Extended Persistence Conjecture
(Craciun–Nazarov–Pantea 2013; Craciun 2019) for bounded trajectories. -/
theorem weaklyReversible_forward_floor_varK (N : Network S) (κ : ℝ → N.RateConstants)
    (hwr : N.WeaklyReversible) {ε : ℝ} (hε : 0 < ε)
    (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) (M : ℝ) :
    ∃ η, 0 < η ∧ ∀ γ : ℝ → Concentration S, γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) →
      (∀ t : ℝ, 0 ≤ t → ∀ s, γ t s ≤ M) → ∀ t : ℝ, 0 ≤ t → ∀ s, η ≤ γ t s := by
  set n := Fintype.card S with hn
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · refine ⟨1, one_pos, fun _ _ _ _ t _ s => ?_⟩
    exact absurd (Fintype.card_pos_iff.mpr ⟨s⟩) (by omega)
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
  obtain ⟨δ, hδ⟩ := N.exists_slack_varK hε
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
    exists_zsh (by omega : 1 ≤ n) H hsym δ M' hM'1 (x₀ ∘ e.symm) (fun q => hx₀ _)
  haveI := hFι
  haveI := hNι
  refine ⟨η, hη, fun γ hγx hsol hbdd => ?_⟩
  have hγ0 : (γ 0).Positive := hγx ▸ hx₀
  have hpos := N.orbit_pos_forward_varK κ (one_div_pos.mpr hε).le (fun t r => (hκ t r).2) hγ0
    (fun t ht _ => hbdd t ht) hsol
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
      rw [← hγx] at this
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
      have hnn := N.dot_massActionField_nonneg_of_weaklyReversible (κ t) hwr (hpos t ht) (aS i) δ
        (hδ (κ t) (fun r => hκ t r)) (by
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
  intro t ht s
  have hb := hinv t ht
  rw [barrier_le_iff] at hb
  have hin : ∀ i, b i ≤ fdot (a i) (γ t ∘ e.symm) := by
    intro i
    have := hb i
    rw [hLapp, hb'] at this
    rw [hdotS]; linarith
  have := hfloor _ hin (e s)
  simpa using this


/-- Displacement along a variable-rate solution stays in the stoichiometric subspace. -/
theorem sub_mem_stoichSubspace_of_solution_varK (N : Network S) (κ : ℝ → N.RateConstants)
    {γ : ℝ → Concentration S} {a b : ℝ} (hab : a ≤ b)
    (hsol : ∀ t ∈ Set.Icc a b, HasDerivAt γ (N.massActionVectorField (κ t) (γ t)) t) :
    γ b - γ a ∈ N.stoichSubspace := by
  rw [← orthSum_orthSum N.stoichSubspace, mem_orthSum]
  intro w hw
  have hp : ∀ t ∈ Set.Icc a b,
      HasDerivWithinAt (fun τ => ∑ i, w i * γ τ i) (0 : ℝ) (Set.Icc a b) t := by
    intro t ht
    have hfun : (fun τ : ℝ => ∑ i, w i * γ τ i)
        = ∑ i ∈ (Finset.univ : Finset S), (fun τ : ℝ => w i * γ τ i) := by
      funext τ; rw [Finset.sum_apply]
    have hzero : (∑ i, w i * N.massActionVectorField (κ t) (γ t) i) = 0 :=
      (mem_orthSum.mp hw) _ (massActionVectorField_mem_stoichSubspace N (κ t) (γ t))
    rw [hfun]
    have hd := HasDerivAt.sum (u := (Finset.univ : Finset S))
      (fun i _ => HasDerivAt.const_mul (w i) ((hasDerivAt_pi.mp (hsol t ht)) i))
    rw [hzero] at hd
    exact hd.hasDerivWithinAt
  have hconst : (∑ i, w i * γ b i) = (∑ i, w i * γ a i) := by
    have hle := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (C := 0) hp
      (fun t _ => by simp) (convex_Icc a b) ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩
    simp only [zero_mul] at hle
    have h0 : ‖(∑ i, w i * γ b i) - (∑ i, w i * γ a i)‖ = 0 := le_antisymm hle (norm_nonneg _)
    rwa [norm_eq_zero, sub_eq_zero] at h0
  calc ∑ i, (γ b - γ a) i * w i
      = ∑ i, (w i * γ b i - w i * γ a i) :=
        Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply]; ring
    _ = (∑ i, w i * γ b i) - (∑ i, w i * γ a i) :=
        Finset.sum_sub_distrib (f := fun i => w i * γ b i) (g := fun i => w i * γ a i)
    _ = 0 := by rw [hconst, sub_self]

/-- **Conservative weakly reversible networks with variable rates are persistent.** For rate
constants varying in time inside `[ε, 1/ε]`, every forward solution from a positive `x₀` stays in
one compact set of positive states. -/
theorem weaklyReversible_conservative_confined_varK (N : Network S) (κ : ℝ → N.RateConstants)
    (hwr : N.WeaklyReversible) (hcons : N.IsConservative) {ε : ℝ} (hε : 0 < ε)
    (hκ : ∀ t r, ε ≤ (κ t).k r ∧ (κ t).k r ≤ 1 / ε)
    {x₀ : Concentration S} (hx₀ : x₀.Positive) :
    ∃ K₀ : Set (Concentration S), IsCompact K₀ ∧ (∀ y ∈ K₀, y.Positive) ∧
      ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
        (∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
        ∀ t : ℝ, 0 ≤ t → Γ t ∈ K₀ := by
  obtain ⟨w, hw⟩ := hcons
  set W := weightedTotal w x₀
  set B : ℝ := ∑ s, W / w s
  have hW : 0 ≤ W := Finset.sum_nonneg fun s _ => mul_nonneg (hw.2 s).le (hx₀ s).le
  have hbound : ∀ Γ : ℝ → Concentration S, Γ 0 = x₀ →
      (∀ t : ℝ, 0 ≤ t → HasDerivAt Γ (N.massActionVectorField (κ t) (Γ t)) t) →
      ∀ t : ℝ, 0 ≤ t → ∀ s, Γ t s ≤ B := by
    intro Γ hΓ0 hΓd
    have hbnn : ∀ t : ℝ, 0 ≤ t → (Γ t).Nonnegative → ∀ s, Γ t s ≤ B := by
      intro t ht hnn s
      have hc : N.StoichCompatible (Γ 0) (Γ t) :=
        N.sub_mem_stoichSubspace_of_solution_varK κ ht fun τ hτ => hΓd τ hτ.1
      rw [hΓ0] at hc
      have h1 := N.coordinate_le_of_strictPSemiflow hw hx₀.nonnegative hnn hc s
      have h2 : W / w s ≤ B :=
        Finset.single_le_sum (f := fun s => W / w s) (fun s _ => div_nonneg hW (hw.2 s).le)
          (Finset.mem_univ s)
      exact h1.trans h2
    have hpos := N.orbit_pos_forward_varK κ (one_div_pos.mpr hε).le (fun t r => (hκ t r).2)
      (hΓ0 ▸ hx₀) hbnn hΓd
    exact fun t ht => hbnn t ht (hpos t ht).nonnegative
  obtain ⟨η, hη, hfloor⟩ := N.weaklyReversible_forward_floor_varK κ hwr hε hκ hx₀ B
  refine ⟨Set.univ.pi fun _ => Set.Icc η B, isCompact_univ_pi fun _ => isCompact_Icc,
    fun y hy s => lt_of_lt_of_le hη (hy s (Set.mem_univ s)).1, fun Γ hΓ0 hΓd t ht => ?_⟩
  intro s _
  exact ⟨hfloor Γ hΓ0 hΓd (hbound Γ hΓ0 hΓd) t ht s, hbound Γ hΓ0 hΓd t ht s⟩

end Network
end CRNT
