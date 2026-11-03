import CRNT.Flux.Cone
import Mathlib.Data.Finset.Card

/-!
# Elementary flux modes and T-invariants

An elementary flux mode (EFM) is a nonzero nonnegative steady flux whose support is
inclusion-minimal among nonzero nonnegative steady fluxes.  This support-minimal
formulation is independent of normalization and is the standard CRNT/metabolic-network
notion relevant to the extreme combinatorics of the steady-flux cone.
-/

namespace CRNT

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Support of a finite reaction vector. -/
noncomputable def fluxSupport (N : Network S) (v : N.R → ℝ) : Finset N.R :=
  Finset.univ.filter fun r => v r ≠ 0

@[simp] theorem mem_fluxSupport_iff (N : Network S) (v : N.R → ℝ) (r : N.R) :
    r ∈ N.fluxSupport v ↔ v r ≠ 0 := by
  simp [fluxSupport]

/-- A real T-invariant is simply a stationary reaction vector.  The nonnegative
T-invariants are exactly the points of the flux cone. -/
def IsTInvariant (N : Network S) (v : N.R → ℝ) : Prop :=
  N.IsStationaryFlux v

/-- Nonnegative T-invariant. -/
def IsNonnegativeTInvariant (N : Network S) (v : N.R → ℝ) : Prop :=
  v ∈ N.FluxCone

/-- Support-minimal nonzero nonnegative steady flux. -/
def IsElementaryFluxMode (N : Network S) (v : N.R → ℝ) : Prop :=
  v ∈ N.FluxCone ∧ v ≠ 0 ∧
    ∀ w : N.R → ℝ, w ∈ N.FluxCone → w ≠ 0 →
      N.fluxSupport w ⊆ N.fluxSupport v →
      N.fluxSupport v ⊆ N.fluxSupport w

/-- EFM minimality can be read as equality of supports whenever another nonzero cone
point has support contained in the EFM support. -/
theorem elementaryFluxMode_support_eq_of_subset (N : Network S) {v w : N.R → ℝ}
    (hv : N.IsElementaryFluxMode v) (hw : w ∈ N.FluxCone) (hw0 : w ≠ 0)
    (hsub : N.fluxSupport w ⊆ N.fluxSupport v) :
    N.fluxSupport w = N.fluxSupport v := by
  apply Finset.Subset.antisymm hsub
  exact hv.2.2 w hw hw0 hsub

/-- Positive rescaling does not change support. -/
theorem fluxSupport_pos_smul (N : Network S) (v : N.R → ℝ) {a : ℝ} (ha : 0 < a) :
    N.fluxSupport (a • v) = N.fluxSupport v := by
  ext r
  simp [fluxSupport, Pi.smul_apply, smul_eq_mul, ha.ne']

/-- Positive rescaling preserves elementary flux modes. -/
theorem elementaryFluxMode_pos_smul (N : Network S) {v : N.R → ℝ}
    (hv : N.IsElementaryFluxMode v) {a : ℝ} (ha : 0 < a) :
    N.IsElementaryFluxMode (a • v) := by
  refine ⟨N.fluxCone_smul_mem hv.1 ha.le, ?_, ?_⟩
  · intro hzero
    have : v = 0 := by
      funext r
      have hr := congrFun hzero r
      simp only [Pi.smul_apply, smul_eq_mul] at hr
      exact (mul_eq_zero.mp hr).resolve_left ha.ne'
    exact hv.2.1 this
  · intro w hw hw0 hsub
    rw [N.fluxSupport_pos_smul v ha] at hsub ⊢
    exact hv.2.2 w hw hw0 hsub

/-- Every EFM is a nonnegative T-invariant. -/
theorem elementaryFluxMode_isNonnegativeTInvariant (N : Network S) {v : N.R → ℝ}
    (hv : N.IsElementaryFluxMode v) : N.IsNonnegativeTInvariant v :=
  hv.1

/-- Every EFM is nonzero. -/
theorem elementaryFluxMode_ne_zero (N : Network S) {v : N.R → ℝ}
    (hv : N.IsElementaryFluxMode v) : v ≠ 0 :=
  hv.2.1

/-- A one-reaction support cone point is automatically elementary. -/
theorem elementaryFluxMode_of_support_singleton (N : Network S) {v : N.R → ℝ}
    (hv : v ∈ N.FluxCone) (hv0 : v ≠ 0) {r : N.R}
    (hsupp : N.fluxSupport v = {r}) : N.IsElementaryFluxMode v := by
  refine ⟨hv, hv0, ?_⟩
  intro w hw hw0 hsub
  have hwne : N.fluxSupport w ≠ ∅ := by
    intro h
    apply hw0
    funext q
    by_contra hq
    have hmem : q ∈ N.fluxSupport w := (N.mem_fluxSupport_iff w q).2 hq
    simpa [h] using hmem
  rw [hsupp] at hsub ⊢
  have hr : r ∈ N.fluxSupport w := by
    by_contra hnr
    have hempty : N.fluxSupport w = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have hqr : q = r := Finset.mem_singleton.1 (hsub hq)
      subst hqr
      exact hnr hq
    exact hwne hempty
  simpa using hr

/-- Support minimality is normalization-free: an EFM can be rescaled to any prescribed
positive value at a reaction in its support. -/
noncomputable def normalizeFluxAt (N : Network S) (v : N.R → ℝ) (r : N.R) : N.R → ℝ :=
  (v r)⁻¹ • v

/-- Normalization gives value one whenever the chosen coordinate is nonzero. -/
theorem normalizeFluxAt_apply_self (N : Network S) (v : N.R → ℝ) (r : N.R)
    (hr : v r ≠ 0) : N.normalizeFluxAt v r r = 1 := by
  simp [normalizeFluxAt, Pi.smul_apply, smul_eq_mul, hr]

end Network

end CRNT
