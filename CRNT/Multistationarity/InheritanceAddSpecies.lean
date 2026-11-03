import CRNT.Multistationarity.InheritanceAddReactions
import CRNT.Kinetics.MassActionJacobian

/-!
# Inheritance of multistationarity under adding a new species

Joshi–Shiu (2013): adding a new species `Y` to some reactions of a network, together with
inflow and outflow `0 ⇌ Y`, preserves nondegenerate multistationarity when the flow rate is large.

`N.addSpecies a b` has species `Option S` (`none` is `Y`): reaction `r` of `N` gains `a r` copies of
`Y` in its source and `b r` copies in its target, and the reactions `0 → Y`, `Y → 0` are added.
With rate constants `κ` on `N`'s reactions and `λ = 1/ε` on the flow reactions,
`multistationarity_inherited_addSpecies`: two distinct nondegenerate positive steady states of a
full-rank `(N, κ)` give, for all small `ε > 0`, two distinct positive steady states of the extended
system in one stoichiometric class.

Proof: the implicit function theorem for `G(ε, z) = F₁ z + ((ε - 1) F₁(z)_Y + 1 - z_Y) e_Y`, whose
zeros at `ε > 0` are the steady states, at the point `(0, (x, 1))`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Network

open Filter Topology

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A complex of `N` with `k` copies of the new species. -/
def extC (c : Complex S) (k : ℕ) : Complex (Option S) := fun o => Option.elim o k c

/-- The reactions of `N` with the new species added (`a` in sources, `b` in targets). -/
def extNet (N : Network S) (a b : N.R → ℕ) : Network (Option S) :=
  ⟨N.R, inferInstance, inferInstance, fun r =>
    ⟨extC (N.reaction r).source (a r), extC (N.reaction r).target (b r)⟩⟩

/-- `extNet` together with inflow `0 → Y` and outflow `Y → 0`. -/
def addSpecies (N : Network S) (a b : N.R → ℕ) : Network (Option S) :=
  ⟨N.R ⊕ Fin 2, inferInstance, inferInstance, fun i => match i with
    | .inl r => ⟨extC (N.reaction r).source (a r), extC (N.reaction r).target (b r)⟩
    | .inr 0 => ⟨extC 0 0, extC 0 1⟩
    | .inr 1 => ⟨extC 0 1, extC 0 0⟩⟩

/-- Rates `κ` on `N`'s reactions. -/
def extRates {N : Network S} (κ : N.RateConstants) (a b : N.R → ℕ) :
    (N.extNet a b).RateConstants := ⟨κ.k, κ.positive⟩

/-- Rates `κ` on `N`'s reactions and `λ` on the flow reactions. -/
def addSpeciesRates {N : Network S} (κ : N.RateConstants) (a b : N.R → ℕ) (lam : ℝ)
    (hlam : 0 < lam) : (N.addSpecies a b).RateConstants :=
  ⟨Sum.elim κ.k (fun _ => lam), by rintro (r | r); exacts [κ.positive r, hlam]⟩

theorem massActionMonomial_extC (c : Complex S) (k : ℕ) (z : Concentration (Option S)) :
    (extC c k).massActionMonomial z = z none ^ k * c.massActionMonomial (fun s => z (some s)) := by
  simp [Complex.massActionMonomial, extC, Fintype.prod_option]

/-- The field of the extended system: `extNet` field plus the flow term `λ (1 - z_Y) e_Y`. -/
theorem massActionVectorField_addSpecies (N : Network S) (κ : N.RateConstants)
    (a b : N.R → ℕ) (lam : ℝ) (hlam : 0 < lam) (z : Concentration (Option S)) :
    (N.addSpecies a b).massActionVectorField (addSpeciesRates κ a b lam hlam) z =
      (N.extNet a b).massActionVectorField (extRates κ a b) z +
        (lam * (1 - z none)) • Pi.single none 1 := by
  funext o
  simp only [massActionVectorField_apply, massActionRate, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  erw [Fintype.sum_sum_type]
  rw [Fin.sum_univ_two]
  congr 1
  simp only [addSpecies, addSpeciesRates, Sum.elim_inr, reactionVector_apply,
    massActionMonomial_extC]
  cases o <;> simp [extC, Complex.massActionMonomial] <;> ring

/-- On the slice `z_Y = 1`, the `S`-components of the `extNet` field are `N`'s field. -/
theorem extNet_field_some (N : Network S) (κ : N.RateConstants) (a b : N.R → ℕ)
    (x : Concentration S) (s : S) :
    (N.extNet a b).massActionVectorField (extRates κ a b) (fun o => Option.elim o 1 x) (some s) =
      N.massActionVectorField κ x s := by
  simp only [massActionVectorField_apply, massActionRate, reactionVector_apply]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp [extNet, extRates, massActionMonomial_extC, extC]

/-- The slice embedding `x ↦ (x, 1)`. -/
def sliceOne (x : Concentration S) : Concentration (Option S) := fun o => Option.elim o 1 x

/-- Its linear part `u ↦ (u, 0)`. -/
noncomputable def sliceLin : (S → ℝ) →L[ℝ] (Option S → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun u o => Option.elim o 0 u
      map_add' := fun u w => by funext o; cases o <;> simp
      map_smul' := fun c u => by funext o; cases o <;> simp }

/-- Restriction to the old species. -/
noncomputable def restrictSome : (Option S → ℝ) →L[ℝ] (S → ℝ) :=
  ContinuousLinearMap.pi fun s => ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Option S => ℝ) (some s)

/-- The rescaled field whose zeros at `ε > 0` are the steady states of the extended system. -/
noncomputable def addSpeciesG (N : Network S) (κ : N.RateConstants) (a b : N.R → ℕ)
    (p : ℝ × (Option S → ℝ)) : Option S → ℝ :=
  (N.extNet a b).massActionVectorField (extRates κ a b) p.2 +
    ((p.1 - 1) * (N.extNet a b).massActionVectorField (extRates κ a b) p.2 none + (1 - p.2 none)) •
      (Pi.single none 1 : Option S → ℝ)

theorem addSpecies_steadyState_of_G (N : Network S) (κ : N.RateConstants) (a b : N.R → ℕ)
    {ε : ℝ} (hε : 0 < ε) {z : Concentration (Option S)} (hG : addSpeciesG N κ a b (ε, z) = 0) :
    (N.addSpecies a b).IsMassActionSteadyState (addSpeciesRates κ a b (1 / ε) (by positivity)) z := by
  intro o
  rw [massActionVectorField_addSpecies]
  have h := congrFun hG o
  have hn := congrFun hG none
  simp only [addSpeciesG, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h hn
  simp only [Pi.single_eq_same, mul_one] at hn
  cases o with
  | none =>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_same, mul_one, Pi.zero_apply]
    field_simp
    linarith
  | some s =>
    simp only [Pi.single_eq_of_ne (Option.some_ne_none s), mul_zero, add_zero] at h
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne (Option.some_ne_none s),
      mul_zero, add_zero, Pi.zero_apply]
    exact h

theorem contDiff_addSpeciesG (N : Network S) (κ : N.RateConstants) (a b : N.R → ℕ) :
    ContDiff ℝ ⊤ (addSpeciesG N κ a b) := by
  have hF := (N.extNet a b).contDiff_massActionVectorField (extRates κ a b)
  have hF2 : ContDiff ℝ ⊤ fun p : ℝ × (Option S → ℝ) =>
      (N.extNet a b).massActionVectorField (extRates κ a b) p.2 := hF.comp contDiff_snd
  have hFn : ContDiff ℝ ⊤ fun p : ℝ × (Option S → ℝ) =>
      (N.extNet a b).massActionVectorField (extRates κ a b) p.2 none :=
    (contDiff_apply ℝ ℝ none).comp hF2
  have hzn : ContDiff ℝ ⊤ fun p : ℝ × (Option S → ℝ) => p.2 none :=
    (contDiff_apply ℝ ℝ none).comp contDiff_snd
  unfold addSpeciesG
  exact hF2.add ((((contDiff_fst.sub contDiff_const).mul hFn).add
    (contDiff_const.sub hzn)).smul contDiff_const)

/-- The `S`-part of the extended Jacobian on the slice is `N`'s Jacobian. -/
theorem restrict_extJacobian_slice (N : Network S) (κ : N.RateConstants) (a b : N.R → ℕ)
    (x₀ : Concentration S) :
    restrictSome ∘L (N.extNet a b).massActionJacobianCLM (extRates κ a b) (sliceOne x₀) ∘L sliceLin =
      fderiv ℝ (N.massActionVectorField κ) x₀ := by
  have hslice : HasFDerivAt (sliceOne (S := S)) sliceLin x₀ := by
    have h := ((sliceLin (S := S)).hasFDerivAt (x := x₀)).const_add (fun o => Option.elim o (1 : ℝ) 0)
    convert h using 1
    funext x o; cases o <;> simp [sliceOne, sliceLin]
  have hcomp := restrictSome.hasFDerivAt.comp x₀
    (((N.extNet a b).massActionVectorField_hasFDerivAt (extRates κ a b) (sliceOne x₀)).comp x₀ hslice)
  have heq : (restrictSome ∘ (fun z => (N.extNet a b).massActionVectorField (extRates κ a b) z) ∘
      sliceOne) = N.massActionVectorField κ := by
    funext x s
    simp only [Function.comp, restrictSome, ContinuousLinearMap.pi_apply,
      ContinuousLinearMap.proj_apply]
    exact N.extNet_field_some κ a b x s
  rw [heq] at hcomp
  have hd : DifferentiableAt ℝ (N.massActionVectorField κ) x₀ :=
    ((N.contDiff_massActionVectorField κ).differentiable (by simp)) x₀
  exact (hcomp.unique hd.hasFDerivAt)

/-- **Persistence of a nondegenerate steady state under adding a species.** -/
theorem eventually_steadyState_branch_addSpecies (N : Network S) (κ : N.RateConstants)
    (a b : N.R → ℕ) {x₀ : Concentration S} (hss : N.IsMassActionSteadyState κ x₀)
    (hnd : (fderiv ℝ (N.massActionVectorField κ) x₀).IsInvertible) :
    ∃ ψ : ℝ → (Option S → ℝ), ψ 0 = sliceOne x₀ ∧ ContinuousAt ψ 0 ∧
      ∀ᶠ ε in 𝓝 (0 : ℝ), addSpeciesG N κ a b (ε, ψ ε) = 0 := by
  classical
  set z₀ := sliceOne x₀ with hz₀
  set F₁ := (N.extNet a b).massActionVectorField (extRates κ a b) with hF₁
  set J₁ := (N.extNet a b).massActionJacobianCLM (extRates κ a b) z₀ with hJ₁
  set pn : (Option S → ℝ) →L[ℝ] ℝ := ContinuousLinearMap.proj (R := ℝ)
    (φ := fun _ : Option S => ℝ) none with hpn
  set e : Option S → ℝ := Pi.single none 1 with he
  set T : (Option S → ℝ) →L[ℝ] (Option S → ℝ) :=
    J₁ + (((-1 : ℝ) • (pn ∘L J₁)) - pn).smulRight e with hT
  have hcd : ContDiffAt ℝ 1 (addSpeciesG N κ a b) (0, z₀) :=
    ((contDiff_addSpeciesG N κ a b).of_le (by simp)).contDiffAt
  -- the partial derivative
  have hpart : fderiv ℝ (addSpeciesG N κ a b) (0, z₀) ∘L ContinuousLinearMap.inr ℝ ℝ _ = T := by
    have hdiff : DifferentiableAt ℝ (addSpeciesG N κ a b) (0, z₀) := hcd.differentiableAt (by simp)
    have hcomp : HasFDerivAt (fun z => addSpeciesG N κ a b (0, z))
        (fderiv ℝ (addSpeciesG N κ a b) (0, z₀) ∘L ContinuousLinearMap.inr ℝ ℝ _) z₀ :=
      hdiff.hasFDerivAt.comp z₀ (hasFDerivAt_prodMk_right (0 : ℝ) z₀)
    have hF : HasFDerivAt F₁ J₁ z₀ := (N.extNet a b).massActionVectorField_hasFDerivAt _ z₀
    have hFn : HasFDerivAt (fun z => F₁ z none) (pn ∘L J₁) z₀ := pn.hasFDerivAt.comp z₀ hF
    have hq : HasFDerivAt (fun z => (0 - 1) * F₁ z none + (1 - z none))
        ((-1 : ℝ) • (pn ∘L J₁) - pn) z₀ := by
      have h1 := (hFn.const_mul (0 - 1 : ℝ)).add ((hasFDerivAt_const (1 : ℝ) z₀).sub pn.hasFDerivAt)
      convert h1 using 1
      · funext z; simp [hpn]
      · ext v; simp [hpn]; ring
    have htot := hF.add (hq.smul_const e)
    have heq : (fun z => addSpeciesG N κ a b (0, z)) =
        fun z => F₁ z + ((0 - 1) * F₁ z none + (1 - z none)) • e := by
      funext z; simp [addSpeciesG, hF₁, he]
    rw [heq] at hcomp
    exact hcomp.unique htot
  -- injectivity
  have hinjN := hnd.injective
  have hslice := restrict_extJacobian_slice N κ a b x₀
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro u hu
    have hnone : u none = 0 := by
      have := congrFun hu none
      simp [hT, he, hpn] at this
      linarith
    have hsome : ∀ s, J₁ u (some s) = 0 := by
      intro s
      have := congrFun hu (some s)
      simpa [hT, he, Pi.single_eq_of_ne (Option.some_ne_none s)] using this
    have hu' : u = sliceLin (restrictSome u) := by
      funext o; cases o
      · simp [sliceLin, hnone]
      · simp [sliceLin, restrictSome]
    have hzero : fderiv ℝ (N.massActionVectorField κ) x₀ (restrictSome u) = 0 := by
      rw [← hslice, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, ← hu']
      funext s
      simp only [restrictSome, ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply,
        Pi.zero_apply]
      exact hsome s
    have hr : restrictSome u = 0 := hinjN (by rw [hzero, map_zero])
    rw [hu', hr, map_zero]
  have hinv : (fderiv ℝ (addSpeciesG N κ a b) (0, z₀) ∘L ContinuousLinearMap.inr ℝ ℝ _).IsInvertible := by
    rw [hpart]
    let eqv : (Option S → ℝ) ≃ₗ[ℝ] (Option S → ℝ) :=
      LinearEquiv.ofInjectiveEndo (T : (Option S → ℝ) →ₗ[ℝ] (Option S → ℝ)) hinj
    exact ⟨eqv.toContinuousLinearEquiv, by ext v; rfl⟩
  refine ⟨hcd.implicitFunction one_ne_zero hinv, hcd.implicitFunction_apply_self one_ne_zero hinv,
    (hcd.contDiffAt_implicitFunction one_ne_zero hinv).continuousAt, ?_⟩
  have h0 : addSpeciesG N κ a b (0, z₀) = 0 := by
    funext o
    cases o with
    | none => simp [addSpeciesG, hz₀, sliceOne]
    | some s =>
      have h1 := N.extNet_field_some κ a b x₀ s
      simp only [addSpeciesG, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_eq_of_ne (Option.some_ne_none s), mul_zero, add_zero, Pi.zero_apply]
      rw [hz₀]; unfold sliceOne; rw [h1]; exact hss s
  filter_upwards [hcd.eventually_apply_implicitFunction one_ne_zero hinv] with ε hε
  rw [hε, h0]

/-- If `N` has full stoichiometric rank, so does the extended network. -/
theorem addSpecies_stoichSubspace_eq_top (N : Network S) (a b : N.R → ℕ)
    (hS : N.stoichSubspace = ⊤) : (N.addSpecies a b).stoichSubspace = ⊤ := by
  classical
  refine eq_top_iff.mpr fun w _ => ?_
  have hv : (fun s => w (some s)) ∈ N.stoichSubspace := by rw [hS]; trivial
  unfold stoichSubspace reactionVectors at hv
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hv
  have hin : ∀ r, (N.addSpecies a b).reactionVector (Sum.inl r) =
      fun o => Option.elim o ((b r : ℝ) - a r) (N.reactionVector r) := by
    intro r; funext o; cases o <;> simp [reactionVector_apply, addSpecies, extC]
  have hflow : (N.addSpecies a b).reactionVector (Sum.inr 0) = Pi.single none 1 := by
    funext o; cases o <;> simp [reactionVector_apply, addSpecies, extC]
  have hw : w = ∑ r, c r • (N.addSpecies a b).reactionVector (Sum.inl r) +
      (w none - ∑ r, c r * ((b r : ℝ) - a r)) • (N.addSpecies a b).reactionVector (Sum.inr 0) := by
    funext o
    cases o with
    | none => simp [hin, hflow, Finset.sum_apply]
    | some s =>
      have := congrFun hc s
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      simp [hin, hflow, Finset.sum_apply, reactionVector_apply] at this ⊢
      linarith
  rw [hw]
  refine Submodule.add_mem _ (Submodule.sum_mem _ fun r _ => Submodule.smul_mem _ _ ?_)
    (Submodule.smul_mem _ _ ?_)
  · exact (N.addSpecies a b).reactionVector_mem_stoichSubspace (Sum.inl r)
  · exact (N.addSpecies a b).reactionVector_mem_stoichSubspace (Sum.inr 0)

/-- **Inheritance of multistationarity under adding a species (Joshi–Shiu 2013).** Let `N` have
full stoichiometric rank and two distinct positive steady states with invertible Jacobians. Add a
new species `Y` to its reactions (`a r` copies in sources, `b r` in targets) together with
`0 ⇌ Y` at rate `1/ε`. For all small `ε > 0` the extended system has two distinct positive steady
states in one stoichiometric class. -/
theorem multistationarity_inherited_addSpecies (N : Network S) (κ : N.RateConstants)
    (a b : N.R → ℕ) (hS : N.stoichSubspace = ⊤) {x₁ x₂ : Concentration S}
    (hx₁ : x₁.Positive) (hx₂ : x₂.Positive) (hne : x₁ ≠ x₂)
    (hss₁ : N.IsMassActionSteadyState κ x₁) (hss₂ : N.IsMassActionSteadyState κ x₂)
    (hnd₁ : (fderiv ℝ (N.massActionVectorField κ) x₁).IsInvertible)
    (hnd₂ : (fderiv ℝ (N.massActionVectorField κ) x₂).IsInvertible) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε (hε : 0 < ε), ε < ε₀ →
      ∃ z₁ z₂ : Concentration (Option S), z₁.Positive ∧ z₂.Positive ∧ z₁ ≠ z₂ ∧
        z₁ - z₂ ∈ (N.addSpecies a b).stoichSubspace ∧
        (N.addSpecies a b).IsMassActionSteadyState
          (addSpeciesRates κ a b (1 / ε) (by positivity)) z₁ ∧
        (N.addSpecies a b).IsMassActionSteadyState
          (addSpeciesRates κ a b (1 / ε) (by positivity)) z₂ := by
  obtain ⟨ψ₁, h₁0, h₁c, h₁e⟩ := eventually_steadyState_branch_addSpecies N κ a b hss₁ hnd₁
  obtain ⟨ψ₂, h₂0, h₂c, h₂e⟩ := eventually_steadyState_branch_addSpecies N κ a b hss₂ hnd₂
  have hopen : IsOpen {z : Option S → ℝ | ∀ o, 0 < z o} := by
    have : {z : Option S → ℝ | ∀ o, 0 < z o} = ⋂ o, {z : Option S → ℝ | 0 < z o} := by ext; simp
    rw [this]
    exact isOpen_iInter_of_finite fun o => isOpen_lt continuous_const (continuous_apply o)
  have hslpos : ∀ {x : Concentration S}, x.Positive → ∀ o, 0 < sliceOne x o := by
    intro x hx o; cases o
    · simp [sliceOne]
    · exact hx _
  have hpos₁ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ o, 0 < ψ₁ ε o :=
    h₁c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₁0]; exact hslpos hx₁))
  have hpos₂ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ o, 0 < ψ₂ ε o :=
    h₂c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₂0]; exact hslpos hx₂))
  have hsl_ne : sliceOne x₁ ≠ sliceOne x₂ := by
    intro h; apply hne; funext s; exact congrFun h (some s)
  have hsep : ∀ᶠ ε in 𝓝 (0 : ℝ), ψ₁ ε ≠ ψ₂ ε := by
    have hc : ContinuousAt (fun ε => (ψ₁ ε, ψ₂ ε)) 0 := h₁c.prodMk h₂c
    have hdiag : IsOpen {p : (Option S → ℝ) × (Option S → ℝ) | p.1 ≠ p.2} :=
      isOpen_ne_fun continuous_fst continuous_snd
    exact hc.preimage_mem_nhds (hdiag.mem_nhds (by simpa [h₁0, h₂0] using hsl_ne))
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff.mp (h₁e.and (h₂e.and (hpos₁.and (hpos₂.and hsep))))
  refine ⟨δ, hδ, fun ε hε hεδ => ?_⟩
  have hdist : dist ε 0 < δ := by rw [Real.dist_eq, sub_zero, abs_of_pos hε]; exact hεδ
  obtain ⟨e₁, e₂, p₁, p₂, sep⟩ := hball hdist
  refine ⟨ψ₁ ε, ψ₂ ε, p₁, p₂, sep, ?_, addSpecies_steadyState_of_G N κ a b hε e₁,
    addSpecies_steadyState_of_G N κ a b hε e₂⟩
  rw [addSpecies_stoichSubspace_eq_top N a b hS]; trivial

end Network
end CRNT
