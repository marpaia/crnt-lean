import CRNT.Flux.ExtremeRay
import CRNT.LinearAlgebra.OrientedMatroid

/-!
# Stoichiometric circuits and elementary flux modes

The signed circuits of the reaction-space stoichiometric kernel are the support-minimal
nonzero steady reaction vectors.  Elementary flux modes are precisely those circuits that
can be oriented into the nonnegative orthant.  This is the oriented-matroid bridge between
CRNT flux-cone geometry and classical circuit theory.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Signed support of a reaction vector. -/
noncomputable def reactionSignVector {N : Network S} (v : N.R → ℝ) : N.R → SignType :=
  fun r => SignType.sign (v r)

/-- A stoichiometric circuit is a support-minimal nonzero vector in `ker S`, with no
nonnegativity requirement. -/
def IsStoichiometricCircuit (N : Network S) (v : N.R → ℝ) : Prop :=
  v ∈ LinearMap.ker N.stoichMap ∧ v ≠ 0 ∧
  ∀ w : N.R → ℝ, w ∈ LinearMap.ker N.stoichMap → w ≠ 0 →
    N.fluxSupport w ⊆ N.fluxSupport v →
    N.fluxSupport w = N.fluxSupport v

/-- Stoichiometric circuits are exactly elementary vectors of the linear flux space. -/
theorem elementary_fluxSpace_iff_stoichiometricCircuit (N : Network S) (v : N.R → ℝ) :
    Elementary N.fluxSpace v ↔ N.IsStoichiometricCircuit v := by
  constructor
  · intro he
    refine ⟨he.1, he.2.1, ?_⟩
    intro w hw hw0 hsub
    have hsub' : support w ⊆ support v := by
      simpa [support, Network.fluxSupport] using hsub
    have hEq : support w = support v := by
      by_contra hneq
      exact he.2.2 w hw hw0 (Finset.ssubset_iff_subset_ne.mpr ⟨hsub', hneq⟩)
    simpa [support, Network.fluxSupport] using hEq
  · intro hc
    refine ⟨hc.1, hc.2.1, ?_⟩
    intro w hw hw0 hstrict
    have hsub : N.fluxSupport w ⊆ N.fluxSupport v := by
      simpa [support, Network.fluxSupport] using hstrict.subset
    have hEq := hc.2.2 w hw hw0 hsub
    have hEq' : support w = support v := by
      simpa [support, Network.fluxSupport] using hEq
    exact hstrict.ne hEq'

/-- Positive rescaling preserves stoichiometric circuits. -/
theorem IsStoichiometricCircuit.smul_pos
    {N : Network S} {v : N.R → ℝ} (hv : N.IsStoichiometricCircuit v)
    {a : ℝ} (ha : 0 < a) : N.IsStoichiometricCircuit (a • v) := by
  refine ⟨(LinearMap.ker N.stoichMap).smul_mem a hv.1, ?_, ?_⟩
  · intro hzero
    apply hv.2.1
    funext r
    have hr := congrFun hzero r
    simp only [Pi.smul_apply, smul_eq_mul] at hr
    exact (mul_eq_zero.mp hr).resolve_left ha.ne'
  · intro w hw hw0 hsub
    rw [N.fluxSupport_pos_smul v ha] at hsub ⊢
    exact hv.2.2 w hw hw0 hsub

/-- Every EFM is a nonnegative stoichiometric circuit. -/
theorem elementaryFluxMode_isStoichiometricCircuit
    (N : Network S) {v : N.R → ℝ} (hv : N.IsElementaryFluxMode v) :
    N.IsStoichiometricCircuit v := by
  have hne : NonnegElementary N.fluxSpace v :=
    (N.nonnegElementary_fluxSpace_iff_EFM v).2 hv
  exact (N.elementary_fluxSpace_iff_stoichiometricCircuit v).1 hne.elementary

/-- A nonnegative stoichiometric circuit is an EFM. -/
theorem stoichiometricCircuit_isElementary_of_nonnegative
    (N : Network S) {v : N.R → ℝ}
    (hc : N.IsStoichiometricCircuit v) (hnn : ∀ r, 0 ≤ v r) :
    N.IsElementaryFluxMode v := by
  refine ⟨⟨hnn, LinearMap.mem_ker.mp hc.1⟩, hc.2.1, ?_⟩
  intro w hw hw0 hsupp
  have heq := hc.2.2 w (LinearMap.mem_ker.mpr hw.2) hw0 hsupp
  simpa [heq]

/-- EFM = nonnegative circuit. -/
theorem elementaryFluxMode_iff_nonnegativeCircuit
    (N : Network S) (v : N.R → ℝ) :
    N.IsElementaryFluxMode v ↔
      N.IsStoichiometricCircuit v ∧ ∀ r, 0 ≤ v r := by
  exact ⟨fun h => ⟨N.elementaryFluxMode_isStoichiometricCircuit h, h.1.1⟩,
    fun h => N.stoichiometricCircuit_isElementary_of_nonnegative h.1 h.2⟩

/-- Every stoichiometric circuit has a canonical signed oriented-matroid circuit. -/
noncomputable def stoichiometricCircuitSign (N : Network S) (v : N.R → ℝ) : N.R → SignType :=
  reactionSignVector v

/-- Circuit signs are realizable sign vectors of the stoichiometric kernel. -/
theorem stoichiometricCircuitSign_realizable
    (N : Network S) {v : N.R → ℝ} (hv : N.IsStoichiometricCircuit v) :
    ∃ w ∈ LinearMap.ker N.stoichMap,
      w ≠ 0 ∧ reactionSignVector w = N.stoichiometricCircuitSign v := by
  exact ⟨v, hv.1, hv.2.1, rfl⟩

/-- Every kernel vector admits a finite conformal decomposition into stoichiometric
circuits.  Unlike the EFM theorem this is valid in every orthant. -/
theorem kernelVector_conformalCircuitDecomposition
    (N : Network S) {v : N.R → ℝ}
    (hv : v ∈ LinearMap.ker N.stoichMap) (hv0 : v ≠ 0) :
    ∃ (m : ℕ) (c : Fin m → (N.R → ℝ)) (a : Fin m → ℝ),
      (∀ i, N.IsStoichiometricCircuit (c i)) ∧
      (∀ i, 0 < a i) ∧
      (∀ i r, c i r ≠ 0 → SignType.sign (c i r) = SignType.sign (v r)) ∧
      v = ∑ i, a i • c i := by
  classical
  obtain ⟨L, hsum, hL⟩ :=
    exists_elementaryConformalSum (S := N.fluxSpace) hv hv0
  let c : Fin L.length → (N.R → ℝ) := fun i => L.get i
  let a : Fin L.length → ℝ := fun _ => 1
  refine ⟨L.length, c, a, ?_, ?_, ?_, ?_⟩
  · intro i
    exact (N.elementary_fluxSpace_iff_stoichiometricCircuit (c i)).1
      (hL (c i) (List.get_mem L i)).1
  · intro i
    exact one_pos
  · intro i r hcir
    have hcd := (hL (c i) (List.get_mem L i)).2
    have hvr : v r ≠ 0 := by
      have hrmem : r ∈ support (c i) := mem_support.mpr hcir
      exact mem_support.mp (hcd.2.2.2 hrmem)
    have hpne : v r * c i r ≠ 0 := mul_ne_zero hvr hcir
    have hp : 0 < v r * c i r := lt_of_le_of_ne (hcd.2.2.1 r) (Ne.symm hpne)
    rcases lt_or_gt_of_ne hcir with hcneg | hcpos
    · have hvneg : v r < 0 := by
        rcases lt_or_gt_of_ne hvr with hvneg | hvpos
        · exact hvneg
        · nlinarith
      rw [sign_neg hcneg, sign_neg hvneg]
    · have hvpos : 0 < v r := by
        rcases lt_or_gt_of_ne hvr with hvneg | hvpos
        · nlinarith
        · exact hvpos
      rw [sign_pos hcpos, sign_pos hvpos]
  · calc
      v = L.sum := hsum.symm
      _ = ∑ i : Fin L.length, L.get i := (sum_get_eq_list_sum L).symm
      _ = ∑ i : Fin L.length, a i • c i := by simp [a, c]

end Network
end CRNT
