import CRNT.Multistationarity.OneReactionNondegenerate
import CRNT.Multistationarity.OneReactionReversible
import CRNT.Multistationarity.OneReactionReversibleUnique
import CRNT.Multistationarity.InheritanceAddReactions

/-!
# Nondegenerate multistationarity of the fully open reversible pair `a ⇌ b`

The fully open network with the reversible non-flow reaction `a ⇌ b` is nondegenerately
multistationary iff `∑_{b_i > a_i} a_i > 1` or `∑_{a_i > b_i} b_i > 1`
(`revPair_nondegMultistationary_iff`), completing the nondegenerate form of Joshi's Theorem 4.1.

The two nondegenerate steady states of the irreversible network `a → b`
(`oneRxn_exists_two_nondegenerate_steadyStates`) persist when the reverse reaction `b → a` is
added with a small rate `ε` (implicit-function branches, `eventually_steadyState_branch`); the
Jacobian of the perturbed field at the branch depends continuously on `ε` and is invertible at
`ε = 0`, hence for small `ε` (`ContinuousLinearMap.isOpen_setOfPred_isInvertible`)
(`exists_nondegenerate_branches`). The fully open `a ⇌ b` field with forward rate `κ₀` and
backward rate `ε` is the perturbed field (`revPair_field_eq_perturbed`).
-/

open Finset Filter
open scoped Topology

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- An injective endomorphism of a finite-dimensional space is invertible. -/
theorem isInvertible_of_injective_endo (f : (S → ℝ) →L[ℝ] (S → ℝ)) (hf : Function.Injective f) :
    f.IsInvertible :=
  ⟨(LinearEquiv.ofInjectiveEndo f.toLinearMap hf).toContinuousLinearEquiv, by ext; rfl⟩

/-- The Jacobian is the derivative of the field. -/
theorem fderiv_eq_jacobian (N : Network S) (κ : N.RateConstants) (x : Concentration S) :
    fderiv ℝ (N.massActionVectorField κ) x = N.massActionJacobianCLM κ x :=
  (N.massActionVectorField_hasFDerivAt κ x).fderiv

/-- Nondegeneracy for a full-rank network is invertibility of the derivative. -/
theorem isInvertible_of_nondegenerate {N : Network S} (hS : N.stoichSubspace = ⊤)
    {κ : N.RateConstants} {x : Concentration S} (h : N.IsNondegenerateSteadyState κ x) :
    (fderiv ℝ (N.massActionVectorField κ) x).IsInvertible := by
  rw [fderiv_eq_jacobian]
  refine isInvertible_of_injective_endo _ fun u v huv => ?_
  have : u - v = 0 := h (u - v) (by rw [hS]; exact Submodule.mem_top) (by rw [map_sub, huv, sub_self])
  exact sub_eq_zero.mp this

theorem nondegenerate_of_isInvertible {N : Network S} {κ : N.RateConstants} {x : Concentration S}
    (h : (fderiv ℝ (N.massActionVectorField κ) x).IsInvertible) :
    N.IsNondegenerateSteadyState κ x := by
  intro u _ hu
  rw [← fderiv_eq_jacobian] at hu
  obtain ⟨A, hA⟩ := h
  have h1 : (A : Concentration S →L[ℝ] Concentration S) u =
      (A : Concentration S →L[ℝ] Concentration S) 0 := by rw [hA, hu, map_zero]
  exact A.injective (by simpa using h1)

/-- **Persistence of two nondegenerate steady states under a small perturbation.** -/
theorem exists_nondegenerate_branches (N M : Network S) (κ : N.RateConstants)
    (κM : M.RateConstants) {x z : Concentration S} (hx : x.Positive) (hz : z.Positive)
    (hne : x ≠ z) (hsx : N.IsMassActionSteadyState κ x) (hsz : N.IsMassActionSteadyState κ z)
    (hnx : (fderiv ℝ (N.massActionVectorField κ) x).IsInvertible)
    (hnz : (fderiv ℝ (N.massActionVectorField κ) z).IsInvertible) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ y₁ y₂ : Concentration S, y₁.Positive ∧ y₂.Positive ∧ y₁ ≠ y₂ ∧
      perturbedField N M κ κM (ε, y₁) = 0 ∧ perturbedField N M κ κM (ε, y₂) = 0 ∧
      (fderiv ℝ (fun y => perturbedField N M κ κM (ε, y)) y₁).IsInvertible ∧
      (fderiv ℝ (fun y => perturbedField N M κ κM (ε, y)) y₂).IsInvertible := by
  obtain ⟨ψ₁, h₁0, h₁c, h₁e⟩ := eventually_steadyState_branch N M κ κM hsx hnx
  obtain ⟨ψ₂, h₂0, h₂c, h₂e⟩ := eventually_steadyState_branch N M κ κM hsz hnz
  have hopen : IsOpen {y : S → ℝ | ∀ s, 0 < y s} := by
    simp only [Set.setOf_forall]
    exact isOpen_iInter_of_finite fun s => isOpen_lt continuous_const (continuous_apply s)
  have hpos₁ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < ψ₁ ε s :=
    h₁c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₁0]; exact hx))
  have hpos₂ : ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ s, 0 < ψ₂ ε s :=
    h₂c.preimage_mem_nhds (hopen.mem_nhds (by rw [h₂0]; exact hz))
  have hsep : ∀ᶠ ε in 𝓝 (0 : ℝ), ψ₁ ε ≠ ψ₂ ε := by
    have h := h₁c.prodMk h₂c
    have hmem : {p : (S → ℝ) × (S → ℝ) | p.1 ≠ p.2} ∈ 𝓝 (ψ₁ 0, ψ₂ 0) := by
      refine isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds ?_
      rw [h₁0, h₂0]; exact hne
    exact h.preimage_mem_nhds hmem
  -- the Jacobian of the perturbed field along the branches
  set D : ℝ × (S → ℝ) → (S → ℝ) →L[ℝ] (S → ℝ) := fun p =>
    fderiv ℝ (N.massActionVectorField κ) p.2 + p.1 • fderiv ℝ (M.massActionVectorField κM) p.2
    with hD
  have hDc : Continuous D := by
    have h1 := (N.contDiff_massActionVectorField κ).continuous_fderiv (by simp)
    have h2 := (M.contDiff_massActionVectorField κM).continuous_fderiv (by simp)
    exact (h1.comp continuous_snd).add (continuous_fst.smul (h2.comp continuous_snd))
  have hDeq : ∀ ε y, fderiv ℝ (fun y => perturbedField N M κ κM (ε, y)) y = D (ε, y) := by
    intro ε y
    have hN := ((N.contDiff_massActionVectorField κ).differentiable (by simp) y).hasFDerivAt
    have hM := ((M.contDiff_massActionVectorField κM).differentiable (by simp) y).hasFDerivAt
    exact (hN.add (hM.const_smul ε)).fderiv
  have hinv : ∀ (ψ : ℝ → S → ℝ) (x₀ : S → ℝ), ψ 0 = x₀ → ContinuousAt ψ 0 →
      (fderiv ℝ (N.massActionVectorField κ) x₀).IsInvertible →
      ∀ᶠ ε in 𝓝 (0 : ℝ), (D (ε, ψ ε)).IsInvertible := by
    intro ψ x₀ hψ0 hψc hx₀
    have hc : ContinuousAt (fun ε => D (ε, ψ ε)) 0 :=
      hDc.continuousAt.comp (continuousAt_id.prodMk hψc)
    have h0 : D (0, ψ 0) = fderiv ℝ (N.massActionVectorField κ) x₀ := by
      simp [hD, hψ0]
    have hmem : {T : (S → ℝ) →L[ℝ] (S → ℝ) | T.IsInvertible} ∈ 𝓝 (D (0, ψ 0)) := by
      rw [h0]; exact ContinuousLinearMap.isOpen_setOfPred_isInvertible.mem_nhds hx₀
    exact hc.preimage_mem_nhds hmem
  have hall := ((((h₁e.and h₂e).and (hpos₁.and hpos₂)).and hsep).and
    ((hinv ψ₁ x h₁0 h₁c hnx).and (hinv ψ₂ z h₂0 h₂c hnz)))
  obtain ⟨ε, ⟨⟨⟨⟨e₁, e₂⟩, p₁, p₂⟩, hs⟩, i₁, i₂⟩, hε⟩ :=
    ((hall.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)))).exists
  refine ⟨ε, hε, ψ₁ ε, ψ₂ ε, p₁, p₂, hs, e₁, e₂, ?_, ?_⟩
  · rw [hDeq]; exact i₁
  · rw [hDeq]; exact i₂

/-- The field of the (closed) one-reaction network. -/
theorem oneRxn_field (a b : Complex S) (κ : (oneRxn a b).RateConstants) (y : Concentration S)
    (s : S) :
    (oneRxn a b).massActionVectorField κ y s = κ.k () * a.massActionMonomial y * ((b s : ℝ) - a s) := by
  rw [massActionVectorField_apply, Fintype.sum_unique]
  erw [reactionVector_apply]
  rfl

/-- The unit rate on a one-reaction network. -/
def oneRxnUnitRate (a b : Complex S) : (oneRxn a b).RateConstants := ⟨fun _ => 1, fun _ => one_pos⟩

/-- **Transfer from a perturbed one-reaction field to the reversible pair.** -/
theorem revPair_nondeg_of_branch (a b : Complex S) {κf κr : ℝ} (hf : 0 < κf) (hr : 0 < κr)
    (kin l : S → ℝ) (hkin : ∀ s, 0 < kin s) (hl : ∀ s, 0 < l s) {y₁ y₂ : Concentration S}
    (hy₁ : y₁.Positive) (hy₂ : y₂.Positive) (hne : y₁ ≠ y₂) (F : Concentration S → Concentration S)
    (hF : ∀ y s, F y s = κf * a.massActionMonomial y * ((b s : ℝ) - a s) +
      κr * b.massActionMonomial y * ((a s : ℝ) - b s) + kin s - l s * y s)
    (h₁ : F y₁ = 0) (h₂ : F y₂ = 0) (hi₁ : (fderiv ℝ F y₁).IsInvertible)
    (hi₂ : (fderiv ℝ F y₂).IsInvertible) :
    (revPair a b).fullyOpen.HasNondegenerateMultistationarity := by
  let κR : (revPair a b).fullyOpen.RateConstants :=
    ⟨Sum.elim (fun i => if i = 0 then κf else κr) (Sum.elim kin l), by
      rintro (i | s | s)
      · show 0 < (if i = 0 then κf else κr); split_ifs <;> assumption
      · exact hkin s
      · exact hl s⟩
  have hfield : (revPair a b).fullyOpen.massActionVectorField κR = F := by
    funext y s
    rw [revPair_fullyOpen_field, hF]
    rfl
  have htop := stoichSubspace_fullyOpen_eq_top (revPair a b)
  refine ⟨κR, y₁, y₁, y₂, ⟨?_, hy₁⟩, ⟨?_, hy₂⟩, fun s => ?_, fun s => ?_, hne, ?_, ?_⟩
  · show y₁ - y₁ ∈ (revPair a b).fullyOpen.stoichSubspace
    rw [htop]; exact Submodule.mem_top
  · show y₂ - y₁ ∈ (revPair a b).fullyOpen.stoichSubspace
    rw [htop]; exact Submodule.mem_top
  · rw [hfield, h₁]; rfl
  · rw [hfield, h₂]; rfl
  · exact nondegenerate_of_isInvertible (by rw [hfield]; exact hi₁)
  · exact nondegenerate_of_isInvertible (by rw [hfield]; exact hi₂)

/-- The perturbation of `a → b` (fully open) by `b → a` at rate `ε`, as a reversible-pair field. -/
theorem revPair_nondeg_of_forward (a b : Complex S)
    (hA : 1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s) :
    (revPair a b).fullyOpen.HasNondegenerateMultistationarity := by
  obtain ⟨κ, x, z, hx, hz, hne, hsx, hsz, hnx, hnz⟩ :=
    oneRxn_exists_two_nondegenerate_steadyStates a b hA
  have htop := stoichSubspace_fullyOpen_eq_top (oneRxn a b)
  obtain ⟨ε, hε, y₁, y₂, p₁, p₂, hne', e₁, e₂, i₁, i₂⟩ :=
    exists_nondegenerate_branches (oneRxn a b).fullyOpen (oneRxn b a) κ (oneRxnUnitRate b a)
      hx hz hne hsx hsz (isInvertible_of_nondegenerate htop hnx)
      (isInvertible_of_nondegenerate htop hnz)
  refine revPair_nondeg_of_branch a b (κ.positive (Sum.inl ())) hε
    (fun s => κ.k (Sum.inr (Sum.inl s))) (fun s => κ.k (Sum.inr (Sum.inr s)))
    (fun s => κ.positive _) (fun s => κ.positive _) p₁ p₂ hne'
    (fun y => perturbedField (oneRxn a b).fullyOpen (oneRxn b a) κ (oneRxnUnitRate b a) (ε, y))
    (fun y s => ?_) e₁ e₂ i₁ i₂
  simp only [perturbedField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [oneRxn_fullyOpen_field, oneRxn_field]
  simp only [oneRxnUnitRate]
  ring

/-- The perturbation of `b → a` (fully open) by `a → b` at rate `ε`. -/
theorem revPair_nondeg_of_backward (a b : Complex S)
    (hB : 1 < ∑ s ∈ univ.filter (fun s => b s < a s), b s) :
    (revPair a b).fullyOpen.HasNondegenerateMultistationarity := by
  obtain ⟨κ, x, z, hx, hz, hne, hsx, hsz, hnx, hnz⟩ :=
    oneRxn_exists_two_nondegenerate_steadyStates b a hB
  have htop := stoichSubspace_fullyOpen_eq_top (oneRxn b a)
  obtain ⟨ε, hε, y₁, y₂, p₁, p₂, hne', e₁, e₂, i₁, i₂⟩ :=
    exists_nondegenerate_branches (oneRxn b a).fullyOpen (oneRxn a b) κ (oneRxnUnitRate a b)
      hx hz hne hsx hsz (isInvertible_of_nondegenerate htop hnx)
      (isInvertible_of_nondegenerate htop hnz)
  refine revPair_nondeg_of_branch a b hε (κ.positive (Sum.inl ()))
    (fun s => κ.k (Sum.inr (Sum.inl s))) (fun s => κ.k (Sum.inr (Sum.inr s)))
    (fun s => κ.positive _) (fun s => κ.positive _) p₁ p₂ hne'
    (fun y => perturbedField (oneRxn b a).fullyOpen (oneRxn a b) κ (oneRxnUnitRate a b) (ε, y))
    (fun y s => ?_) e₁ e₂ i₁ i₂
  simp only [perturbedField, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [oneRxn_fullyOpen_field, oneRxn_field]
  simp only [oneRxnUnitRate]
  ring

/-- **Joshi 2013, Theorem 4.1(2), nondegenerate form.** The fully open network with the reversible
non-flow reaction `a ⇌ b` is nondegenerately multistationary iff `∑_{b_i > a_i} a_i > 1` or
`∑_{a_i > b_i} b_i > 1`. -/
theorem revPair_nondegMultistationary_iff (a b : Complex S) :
    (revPair a b).fullyOpen.HasNondegenerateMultistationarity ↔
      (1 < ∑ s ∈ univ.filter (fun s => a s < b s), a s ∨
        1 < ∑ s ∈ univ.filter (fun s => b s < a s), b s) := by
  constructor
  · intro h
    obtain ⟨κ, x₀, x, y, hx, hy, hsx, hsy, hne⟩ := h.capacity
    exact (revPair_multistationary_iff a b).mp ⟨κ, x, y, hx.2, hy.2, hne, hsx, hsy⟩
  · rintro (h | h)
    · exact revPair_nondeg_of_forward a b h
    · exact revPair_nondeg_of_backward a b h

/-- **Joshi–Shiu 2013, Theorem 3.1 (nondegenerate form).** If a full-rank network has two distinct
nondegenerate positive steady states, then adding any reactions with small rates gives a network
that is nondegenerately multistationary. -/
theorem nondegMultistationarity_inherited_union (N M : Network S) (hS : N.stoichSubspace = ⊤)
    (κ : N.RateConstants) (κM : M.RateConstants) {x z : Concentration S} (hx : x.Positive)
    (hz : z.Positive) (hne : x ≠ z) (hsx : N.IsMassActionSteadyState κ x)
    (hsz : N.IsMassActionSteadyState κ z) (hnx : N.IsNondegenerateSteadyState κ x)
    (hnz : N.IsNondegenerateSteadyState κ z) :
    (N.union M).HasNondegenerateMultistationarity := by
  obtain ⟨ε, hε, y₁, y₂, p₁, p₂, hne', e₁, e₂, i₁, i₂⟩ :=
    exists_nondegenerate_branches N M κ κM hx hz hne hsx hsz (isInvertible_of_nondegenerate hS hnx)
      (isInvertible_of_nondegenerate hS hnz)
  have hfield : (N.union M).massActionVectorField (unionRates κ κM ε hε) =
      fun y => perturbedField N M κ κM (ε, y) := by
    funext y
    rw [massActionVectorField_union]
    rfl
  have htop : (N.union M).stoichSubspace = ⊤ := eq_top_iff.mpr (hS ▸ stoichSubspace_le_union N M)
  refine ⟨unionRates κ κM ε hε, y₁, y₁, y₂, ⟨?_, p₁⟩, ⟨?_, p₂⟩, fun s => ?_, fun s => ?_, hne',
    ?_, ?_⟩
  · show y₁ - y₁ ∈ (N.union M).stoichSubspace
    rw [htop]; exact Submodule.mem_top
  · show y₂ - y₁ ∈ (N.union M).stoichSubspace
    rw [htop]; exact Submodule.mem_top
  · rw [hfield]; exact congrFun e₁ s
  · rw [hfield]; exact congrFun e₂ s
  · exact nondegenerate_of_isInvertible (by rw [hfield]; exact i₁)
  · exact nondegenerate_of_isInvertible (by rw [hfield]; exact i₂)

end Network
end CRNT
