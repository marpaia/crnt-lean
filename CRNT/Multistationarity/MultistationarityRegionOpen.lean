import CRNT.Multistationarity.DecoratedSimplicesConservation

/-!
# The region of nondegenerate multistationarity is open

Parameters are rate constants and totals `(κ, T) ∈ ℝ^R × ℝ^{E₂}`. The set of parameters for which
the class `{L x = T}` contains `d` distinct positive steady states, each nondegenerate relative to
the class, is open (`isOpen_nondegRegion`): each nondegenerate steady state continues, by the
implicit function theorem applied to the augmented system `(Z F_κ(x), L x − T)` in
`(κ, T, x)`, to nearby parameters, staying positive, distinct and nondegenerate. With the
Bihan–Dickenstein–Giaroli theorem (`steadyStates_of_augmentedCells`) this gives nonempty open
regions of multistationarity in parameter space.
-/

namespace CRNT

namespace Network

open Filter Topology

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S] {E₁ E₂ : Type} [Fintype E₁] [Fintype E₂]

/-- The mass-action field with an arbitrary rate vector. -/
noncomputable def rawField (N : Network S) (k : N.R → ℝ) (x : S → ℝ) : S → ℝ :=
  ∑ r, (k r * (N.reaction r).source.massActionMonomial x) • N.reactionVector r

theorem rawField_eq (N : Network S) (κ : RateConstants N) (x : S → ℝ) :
    rawField N κ.k x = N.massActionVectorField κ x := by
  funext s
  rw [massActionVectorField_apply]
  simp [rawField, Finset.sum_apply, massActionRate, smul_eq_mul]

/-- The augmented system as a function of parameters and state. -/
noncomputable def augPhi (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (P : ((N.R → ℝ) × (E₂ → ℝ)) × (S → ℝ)) : E₁ ⊕ E₂ → ℝ :=
  inlCLM E₁ E₂ (LinearMap.toContinuousLinearMap Z (rawField N P.1.1 P.2)) +
    inrCLM E₁ E₂ (LinearMap.toContinuousLinearMap L P.2 - P.1.2)

theorem augPhi_contDiff (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) : ContDiff ℝ ⊤ (augPhi N Z L) := by
  have hraw : ContDiff ℝ ⊤ (fun P : ((N.R → ℝ) × (E₂ → ℝ)) × (S → ℝ) => rawField N P.1.1 P.2) := by
    rw [contDiff_pi]
    intro s
    simp only [rawField, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.massActionMonomial]
    fun_prop
  unfold augPhi
  exact ((inlCLM E₁ E₂).contDiff.comp ((LinearMap.toContinuousLinearMap Z).contDiff.comp hraw)).add
    ((inrCLM E₁ E₂).contDiff.comp (((LinearMap.toContinuousLinearMap L).contDiff.comp contDiff_snd).sub
      (contDiff_snd.comp contDiff_fst)))

/-- The state derivative of the augmented system. -/
theorem augPhi_fderiv_inr (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (κ : RateConstants N) (T : E₂ → ℝ) (x : S → ℝ) :
    fderiv ℝ (augPhi N Z L) ((κ.k, T), x) ∘L ContinuousLinearMap.inr ℝ _ (S → ℝ) =
      inlCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap Z ∘L N.massActionJacobianCLM κ x +
        inrCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap L := by
  have hdiff : DifferentiableAt ℝ (augPhi N Z L) ((κ.k, T), x) :=
    ((augPhi_contDiff N Z L).differentiable (by simp)) _
  have hcomp : HasFDerivAt (fun y => augPhi N Z L ((κ.k, T), y))
      (fderiv ℝ (augPhi N Z L) ((κ.k, T), x) ∘L ContinuousLinearMap.inr ℝ _ (S → ℝ)) x :=
    hdiff.hasFDerivAt.comp x (hasFDerivAt_prodMk_right ((κ.k, T) : (N.R → ℝ) × (E₂ → ℝ)) x)
  have heq : (fun y => augPhi N Z L ((κ.k, T), y)) = fun y =>
      inlCLM E₁ E₂ (LinearMap.toContinuousLinearMap Z (N.massActionVectorField κ y)) +
        inrCLM E₁ E₂ (LinearMap.toContinuousLinearMap L y - T) := by
    funext y; simp only [augPhi, rawField_eq]
  rw [heq] at hcomp
  have h1 : HasFDerivAt (fun y => inlCLM E₁ E₂
      (LinearMap.toContinuousLinearMap Z (N.massActionVectorField κ y)))
      (inlCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap Z ∘L N.massActionJacobianCLM κ x) x :=
    (inlCLM E₁ E₂).hasFDerivAt.comp _ ((LinearMap.toContinuousLinearMap Z).hasFDerivAt.comp _
      (N.massActionVectorField_hasFDerivAt κ x))
  have h2 : HasFDerivAt (fun y => inrCLM E₁ E₂ (LinearMap.toContinuousLinearMap L y - T))
      (inrCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap L) x :=
    (inrCLM E₁ E₂).hasFDerivAt.comp _ ((LinearMap.toContinuousLinearMap L).hasFDerivAt.sub_const T)
  exact hcomp.unique (h1.add h2)

/-- The parameters `(κ, T)` with `d` distinct nondegenerate positive steady states in the class
`{L x = T}`. -/
def NondegRegion (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ)) (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ))
    (d : ℕ) : Set ((N.R → ℝ) × (E₂ → ℝ)) :=
  {q | ∃ hk : ∀ r, 0 < q.1 r, ∃ X : Fin d → Concentration S, Function.Injective X ∧
    ∀ j, (X j).Positive ∧ N.IsMassActionSteadyState ⟨q.1, hk⟩ (X j) ∧ L (X j) = q.2 ∧
      N.IsNondegenerateSteadyState ⟨q.1, hk⟩ (X j)}

/-- **The region of nondegenerate multistationarity is open.** -/
theorem isOpen_nondegRegion (N : Network S) (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ))
    (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ)) (hZ : ∀ v ∈ N.stoichSubspace, Z v = 0 → v = 0)
    (hL : ∀ v, L v = 0 ↔ v ∈ N.stoichSubspace)
    (hcard : Fintype.card (E₁ ⊕ E₂) = Fintype.card S) (d : ℕ) :
    IsOpen (NondegRegion N Z L d) := by
  classical
  rw [isOpen_iff_mem_nhds]
  rintro q ⟨hk, X, hinj, hX⟩
  set κ : RateConstants N := ⟨q.1, hk⟩
  have hdim : Module.finrank ℝ (S → ℝ) = Module.finrank ℝ (E₁ ⊕ E₂ → ℝ) := by
    simp [Module.finrank_fintype_fun_eq_card, hcard]
  -- injectivity of the state derivative from nondegeneracy, at any parameters
  have hDinj : ∀ (κ' : RateConstants N) (T' : E₂ → ℝ) (x : Concentration S),
      N.IsNondegenerateSteadyState κ' x →
      Function.Injective (inlCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap Z ∘L
        N.massActionJacobianCLM κ' x + inrCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap L) := by
    intro κ' T' x hnd u v huv
    rw [← sub_eq_zero]
    set w := u - v
    have hw : (inlCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap Z ∘L
        N.massActionJacobianCLM κ' x + inrCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap L) w = 0 := by
      simp only [w, map_sub, huv, sub_self]
    have h1 : Z (N.massActionJacobianCLM κ' x w) = 0 := by
      funext e₁; have := congrFun hw (Sum.inl e₁); simpa [inlCLM, inrCLM] using this
    have h2 : L w = 0 := by
      funext e₂; have := congrFun hw (Sum.inr e₂); simpa [inlCLM, inrCLM] using this
    have hwV := (hL w).mp h2
    have hJV : N.massActionJacobianCLM κ' x w ∈ N.stoichSubspace := by
      rw [massActionJacobianCLM_apply_sum]
      exact Submodule.sum_mem _ fun r _ =>
        Submodule.smul_mem _ _ (N.reactionVector_mem_stoichSubspace r)
    exact hnd w hwV (hZ _ hJV h1)
  -- implicit function branches through each steady state
  have hbranch : ∀ j, ∃ ψ : (N.R → ℝ) × (E₂ → ℝ) → (S → ℝ), ψ q = X j ∧ ContinuousAt ψ q ∧
      (∀ᶠ p in 𝓝 q, augPhi N Z L (p, ψ p) = 0) ∧
      ∀ᶠ p in 𝓝 q, (fderiv ℝ (augPhi N Z L) (p, ψ p) ∘L
        ContinuousLinearMap.inr ℝ _ (S → ℝ)).IsInvertible := by
    intro j
    obtain ⟨hpos, hss, hLx, hnd⟩ := hX j
    have hzero : augPhi N Z L (q, X j) = 0 := by
      simp only [augPhi]
      have hF : N.massActionVectorField κ (X j) = 0 := funext hss
      rw [show N.rawField q.1 (X j) = N.massActionVectorField κ (X j) from rawField_eq N κ (X j),
        hF, map_zero, map_zero, show (LinearMap.toContinuousLinearMap L) (X j) = L (X j) from rfl,
        hLx, sub_self, map_zero, add_zero]
    have hcd : ContDiffAt ℝ 1 (augPhi N Z L) (q, X j) :=
      ((augPhi_contDiff N Z L).of_le (by simp)).contDiffAt
    have hinv : (fderiv ℝ (augPhi N Z L) (q, X j) ∘L
        ContinuousLinearMap.inr ℝ _ (S → ℝ)).IsInvertible := by
      have hq : q = (κ.k, q.2) := rfl
      rw [hq, augPhi_fderiv_inr N Z L κ q.2 (X j)]
      set D := inlCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap Z ∘L N.massActionJacobianCLM κ (X j) +
        inrCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap L
      have hi : Function.Injective (D : (S → ℝ) →ₗ[ℝ] (E₁ ⊕ E₂ → ℝ)) := hDinj κ q.2 (X j) hnd
      have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hi
      refine ⟨(LinearEquiv.ofBijective (D : (S → ℝ) →ₗ[ℝ] (E₁ ⊕ E₂ → ℝ)) ⟨hi, hs⟩).toContinuousLinearEquiv,
        ?_⟩
      ext v; rfl
    set ψ := hcd.implicitFunction one_ne_zero hinv with hψdef
    have hψ0 : ψ q = X j := hcd.implicitFunction_apply_self one_ne_zero hinv
    have hψc : ContinuousAt ψ q := (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt
    refine ⟨ψ, hψ0, hψc, ?_, ?_⟩
    · filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with p hp
      rw [← hψdef] at hp
      rw [hp, hzero]
    · have hfc : Continuous (fderiv ℝ (augPhi N Z L)) :=
        (augPhi_contDiff N Z L).continuous_fderiv (by simp)
      have hpath : ContinuousAt (fun p => ((p, ψ p) : ((N.R → ℝ) × (E₂ → ℝ)) × (S → ℝ))) q :=
        continuousAt_id.prodMk hψc
      set R := (ContinuousLinearMap.compL ℝ (S → ℝ) (((N.R → ℝ) × (E₂ → ℝ)) × (S → ℝ))
        (E₁ ⊕ E₂ → ℝ)).flip (ContinuousLinearMap.inr ℝ _ (S → ℝ)) with hR
      have hD : ContinuousAt (fun p => R (fderiv ℝ (augPhi N Z L) (p, ψ p))) q :=
        R.continuous.continuousAt.comp (hfc.continuousAt.comp hpath)
      have hD0 : R (fderiv ℝ (augPhi N Z L) (q, ψ q)) =
          fderiv ℝ (augPhi N Z L) (q, X j) ∘L ContinuousLinearMap.inr ℝ _ (S → ℝ) := by
        rw [hψ0]; rfl
      have hev := hinv.eventually_nhds
      rw [← hD0] at hev
      exact hD.eventually hev
  choose ψ hψ0 hψc hψz hψinv using hbranch
  -- the eventual properties near `q`
  have hkev : ∀ᶠ p in 𝓝 q, ∀ r, 0 < p.1 r := by
    rw [eventually_all]
    intro r
    have hc : ContinuousAt (fun p : (N.R → ℝ) × (E₂ → ℝ) => p.1 r) q :=
      ((continuous_apply r).comp continuous_fst).continuousAt
    exact hc.eventually (lt_mem_nhds (hk r))
  have hposev : ∀ j, ∀ᶠ p in 𝓝 q, ∀ s, 0 < ψ j p s := by
    intro j
    rw [eventually_all]
    intro s
    have hcs : ContinuousAt (fun p => ψ j p s) q := (continuous_apply s).continuousAt.comp (hψc j)
    have : 0 < ψ j q s := by rw [hψ0 j]; exact (hX j).1 s
    exact hcs.eventually (lt_mem_nhds this)
  have hneev : ∀ j j', j ≠ j' → ∀ᶠ p in 𝓝 q, ψ j p ≠ ψ j' p := by
    intro j j' hjj
    have hc : ContinuousAt (fun p => ψ j p - ψ j' p) q := (hψc j).sub (hψc j')
    have hne : ψ j q - ψ j' q ≠ 0 := by
      rw [hψ0, hψ0, sub_ne_zero]; exact fun h => hjj (hinj h)
    filter_upwards [hc.eventually_ne hne] with p hp
    exact fun h => hp (by rw [h, sub_self])
  have hall : ∀ᶠ p in 𝓝 q, (∀ r, 0 < p.1 r) ∧ (∀ j, ∀ s, 0 < ψ j p s) ∧
      (∀ j, augPhi N Z L (p, ψ j p) = 0) ∧
      (∀ j, (fderiv ℝ (augPhi N Z L) (p, ψ j p) ∘L
        ContinuousLinearMap.inr ℝ _ (S → ℝ)).IsInvertible) ∧
      (∀ jj : Fin d × Fin d, jj.1 ≠ jj.2 → ψ jj.1 p ≠ ψ jj.2 p) := by
    have hne' : ∀ᶠ p in 𝓝 q, ∀ jj : Fin d × Fin d, jj.1 ≠ jj.2 → ψ jj.1 p ≠ ψ jj.2 p := by
      rw [eventually_all]
      intro jj
      by_cases h : jj.1 = jj.2
      · exact Eventually.of_forall fun _ hne => absurd h hne
      · exact (hneev jj.1 jj.2 h).mono fun _ hp _ => hp
    filter_upwards [hkev, eventually_all.mpr hposev, eventually_all.mpr hψz,
      eventually_all.mpr hψinv, hne'] with p a1 a2 a3 a4 a5
    exact ⟨a1, a2, a3, a4, a5⟩
  filter_upwards [hall] with p ⟨hkp, hpos, hzero, hinvp, hne⟩
  set κp : RateConstants N := ⟨p.1, hkp⟩
  refine ⟨hkp, fun j => ψ j p, fun j j' h => ?_, fun j => ?_⟩
  · by_contra hjj; exact hne (j, j') hjj h
  · have hz := hzero j
    have hp : p = (κp.k, p.2) := rfl
    have hZF : Z (N.massActionVectorField κp (ψ j p)) = 0 := by
      funext e₁
      have := congrFun hz (Sum.inl e₁)
      simp only [augPhi] at this
      rw [show N.rawField p.1 (ψ j p) = N.massActionVectorField κp (ψ j p) from
        rawField_eq N κp _] at this
      simpa [inlCLM, inrCLM] using this
    have hLx : L (ψ j p) = p.2 := by
      funext e₂
      have := congrFun hz (Sum.inr e₂)
      simp only [augPhi] at this
      simpa [inlCLM, inrCLM, sub_eq_zero] using this
    have hss : N.IsMassActionSteadyState κp (ψ j p) := by
      intro s
      exact congrFun (hZ _ (field_mem_stoichSubspace N κp (ψ j p)) hZF) s
    refine ⟨hpos j, hss, hLx, ?_⟩
    intro u hu hJu
    have hinvj := hinvp j
    rw [hp, augPhi_fderiv_inr N Z L κp p.2 (ψ j p)] at hinvj
    obtain ⟨e, he⟩ := hinvj
    have h0 : (inlCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap Z ∘L
        N.massActionJacobianCLM κp (ψ j p) + inrCLM E₁ E₂ ∘L LinearMap.toContinuousLinearMap L) u =
        0 := by
      have hLu : L u = 0 := (hL u).mpr hu
      have hJu' : N.massActionJacobianCLM κp (ψ j p) u = 0 := hJu
      simp [hJu', hLu]
    rw [← he] at h0
    have := congrArg e.symm h0
    simpa using this

/-- **Bihan–Dickenstein–Giaroli regions are open and nonempty.** Under the hypotheses of
`steadyStates_of_augmentedCells`, the region of parameters `(κ, T)` with `d` nondegenerate
positive steady states in the class `{L x = T}` is a nonempty open set. -/
theorem nondegRegion_open_nonempty_of_augmentedCells (N : Network S)
    (Z : (S → ℝ) →ₗ[ℝ] (E₁ → ℝ)) (L : (S → ℝ) →ₗ[ℝ] (E₂ → ℝ))
    (hZ : ∀ v ∈ N.stoichSubspace, Z v = 0 → v = 0) (hL : ∀ v, L v = 0 ↔ v ∈ N.stoichSubspace)
    (hcard : Fintype.card (E₁ ⊕ E₂) = Fintype.card S) (κ : RateConstants N) (T : E₂ → ℝ)
    (h : Complex S → ℤ) (hh : ∀ i, h (unitComplex i) = 0) {d : ℕ} (hd : 0 < d)
    (C : Fin d → Patchworking.SysCell (augSupport N) (augCoeff N κ Z L T) h)
    (hw : Function.Injective fun j => (C j).w) :
    IsOpen (NondegRegion N Z L d) ∧ (NondegRegion N Z L d).Nonempty := by
  refine ⟨isOpen_nondegRegion N Z L hZ hL hcard d, ?_⟩
  obtain ⟨κ', x₀, X, hX, hinj⟩ := steadyStates_of_augmentedCells N Z L hZ hL hcard κ T h hh hd C hw
  refine ⟨(κ'.k, L x₀), κ'.positive, X, hinj, fun j => ⟨(hX j).1.2, (hX j).2.1, ?_, (hX j).2.2⟩⟩
  have hc : X j - x₀ ∈ N.stoichSubspace := (hX j).1.1
  have := (hL _).mpr hc
  rw [map_sub, sub_eq_zero] at this
  exact this

end Network

end CRNT
