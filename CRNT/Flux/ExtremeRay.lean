import CRNT.Flux.Elementary
import CRNT.Flux.ConformalDecomposition

/-!
# Extreme rays of the steady-flux cone

For an s-cone `ker S ∩ ℝ_{≥0}^R`, support-minimal nonzero vectors are exactly the
extreme-ray generators. This identifies elementary flux modes with the one-dimensional
faces of the steady-flux cone and gives the geometric form of the standard EFM
conformal-decomposition theorem.
-/

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Two nonzero reaction vectors generate the same positive ray. -/
def SamePositiveRay {N : Network S} (v w : N.R → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ w = a • v

/-- `v` generates an extreme ray of the nonnegative steady-flux cone, in the *strong*
(conjunctive) form: **both** summands must be proportional to `v`.

NOTE: `Flux/ConformalDecomposition.lean:90` already declares `IsExtremeFluxRay` with a
*disjunctive* condition (`∃ α ≥ 0, a = α • v` **or** the same for `b`).  Those are different
statements, and this file imports that one, so re-using the name was a genuine collision
rather than a duplicate. Renamed here to keep both available. -/
def IsExtremeFluxRayStrong (N : Network S) (v : N.R → ℝ) : Prop :=
  v ∈ N.FluxCone ∧ v ≠ 0 ∧
    ∀ u w : N.R → ℝ,
      u ∈ N.FluxCone → w ∈ N.FluxCone → v = u + w →
      (u = 0 ∨ N.SamePositiveRay v u) ∧
      (w = 0 ∨ N.SamePositiveRay v w)

/-- Elementary flux modes generate extreme rays. -/
theorem elementaryFluxMode_isExtremeRay (N : Network S) {v : N.R → ℝ}
    (hv : N.IsElementaryFluxMode v) : N.IsExtremeFluxRayStrong v := by
  refine ⟨hv.1, hv.2.1, ?_⟩
  intro u w hu hw hvsum
  have hve : CRNT.NonnegElementary N.fluxSpace v :=
    (N.nonnegElementary_fluxSpace_iff_EFM v).2 hv
  have hsub_u : CRNT.support u ⊆ CRNT.support v := by
    intro r hr
    rw [CRNT.mem_support] at hr ⊢
    intro hvr
    have hcoord := congrFun hvsum r
    have hun := hu.1 r
    have hwn := hw.1 r
    have hz : u r + w r = 0 := by simpa [hvr] using hcoord.symm
    have hur : u r = 0 := by nlinarith
    exact hr hur
  have hsub_w : CRNT.support w ⊆ CRNT.support v := by
    intro r hr
    rw [CRNT.mem_support] at hr ⊢
    intro hvr
    have hcoord := congrFun hvsum r
    have hun := hu.1 r
    have hwn := hw.1 r
    have hz : u r + w r = 0 := by simpa [hvr] using hcoord.symm
    have hwr : w r = 0 := by nlinarith
    exact hr hwr
  constructor
  · by_cases hu0 : u = 0
    · exact Or.inl hu0
    · right
      obtain ⟨t, ht, htu⟩ :=
        hve.eq_pos_smul_of_support_subset hu.2 hu0 hu.1 hsub_u
      refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
      rw [htu]
      ext r
      simp [Pi.smul_apply, smul_eq_mul, ht.ne']
  · by_cases hw0 : w = 0
    · exact Or.inl hw0
    · right
      obtain ⟨t, ht, htw⟩ :=
        hve.eq_pos_smul_of_support_subset hw.2 hw0 hw.1 hsub_w
      refine ⟨t⁻¹, inv_pos.mpr ht, ?_⟩
      rw [htw]
      ext r
      simp [Pi.smul_apply, smul_eq_mul, ht.ne']

/-- Extreme rays of the flux cone are support-minimal, hence elementary flux modes. -/
theorem extremeRay_isElementaryFluxMode (N : Network S) {v : N.R → ℝ}
    (hv : N.IsExtremeFluxRayStrong v) : N.IsElementaryFluxMode v := by
  apply N.elementary_of_extremeFluxRay
  refine ⟨hv.1, hv.2.1, ?_⟩
  intro a b ha hb hab
  rcases hv.2.2 a b ha hb hab with ⟨hua, _⟩
  rcases hua with hzero | ⟨α, hα, hscale⟩
  · left
    exact ⟨0, le_rfl, by simpa [hzero]⟩
  · left
    exact ⟨α, hα.le, hscale⟩

/-- Geometric characterization of EFMs. -/
theorem elementaryFluxMode_iff_extremeRay (N : Network S) (v : N.R → ℝ) :
    N.IsElementaryFluxMode v ↔ N.IsExtremeFluxRayStrong v := by
  exact ⟨N.elementaryFluxMode_isExtremeRay, N.extremeRay_isElementaryFluxMode⟩

/-- Every nonzero steady nonnegative flux is a finite nonnegative combination of EFMs. -/
theorem fluxCone_generated_by_elementaryFluxModes (N : Network S)
    {v : N.R → ℝ} (hv : v ∈ N.FluxCone) :
    ∃ (m : ℕ) (e : Fin m → (N.R → ℝ)) (a : Fin m → ℝ),
      (∀ i, N.IsElementaryFluxMode (e i)) ∧
      (∀ i, 0 ≤ a i) ∧
      v = ∑ i, a i • e i := by
  exact (N.fluxCone_generated_by_EFMs v).1 hv

/-- A strictly positive stationary flux exists iff EFM supports collectively cover all
reactions. This is the EFM form of network consistency. -/
theorem isConsistent_iff_EFM_support_cover (N : Network S) :
    N.IsConsistent ↔
      ∀ r : N.R, ∃ e : N.R → ℝ,
        N.IsElementaryFluxMode e ∧ r ∈ N.fluxSupport e := by
  constructor
  · intro hcon
    rcases (N.consistent_iff_EFM_support_cover).1 hcon with ⟨n, e, he, hcover⟩
    intro r
    rcases hcover r with ⟨i, hi⟩
    exact ⟨e i, he i, hi⟩
  · intro hcover
    classical
    choose e helem hsupp using hcover
    apply (N.isConsistent_iff_exists_positive_fluxCone).2
    let v : N.R → ℝ := ∑ q : N.R, e q
    refine ⟨v, ?_, ?_⟩
    · dsimp [v]
      refine Finset.sum_induction (fun q : N.R => e q)
        (fun z => z ∈ N.FluxCone) ?_ (N.zero_mem_fluxCone) ?_
      · intro a b ha hb
        exact N.fluxCone_add_mem ha hb
      · intro q _
        exact (helem q).1
    · intro r
      have hrne : e r r ≠ 0 := (N.mem_fluxSupport_iff _ _).1 (hsupp r)
      have hrpos : 0 < e r r := lt_of_le_of_ne ((helem r).1.1 r) (Ne.symm hrne)
      dsimp [v]
      simp only [Finset.sum_apply]
      apply Finset.sum_pos'
      · intro q _
        exact (helem q).1.1 r
      · exact ⟨r, Finset.mem_univ r, hrpos⟩

end Network
end CRNT
