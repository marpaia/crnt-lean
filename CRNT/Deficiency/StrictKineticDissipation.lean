import CRNT.Theorems.DeficiencyZero.Dissipation
import CRNT.Deficiency.PositiveKineticFamily
namespace CRNT.Network
open scoped BigOperators Classical
open Matrix
variable {S : Type} [DecidableEq S] [Fintype S]

theorem kineticMap_logRatio_neg_of_ne_zero
    (N : Network S) (κ : N.RateConstants)
    {v w : N.ComplexIdx → ℝ} (hv : ∀ c, 0 < v c) (hw : ∀ c, 0 < w c)
    (hwker : N.kineticMap κ w = 0) (hvker : N.kineticMap κ v ≠ 0) :
    (∑ c, N.kineticMap κ v c * (Real.log (v c) - Real.log (w c))) < 0 := by
  have hle := N.kineticMap_logRatio_nonpos κ hv hw hwker
  apply lt_of_le_of_ne hle
  intro heq
  have hzero : (∑ c, N.kineticMap κ v c * (Real.log (v c) - Real.log (w c))) = 0 := heq
  have hratio := N.kineticMap_logRatio_ratio_eq κ hv hw hwker hzero
  let phi : N.ComplexIdx → ℝ := fun c => v c / w c
  have hedge : ∀ r, phi (N.targetIdx r) = phi (N.sourceIdx r) := hratio
  have hkerT : phi ∈ LinearMap.ker N.incidenceMatrixᵀ.mulVecLin := by
    rw [LinearMap.mem_ker]
    funext r
    rw [N.incidenceTranspose_apply, Pi.zero_apply]
    exact sub_eq_zero.mpr (hedge r)
  rw [N.ker_incidenceTranspose] at hkerT
  obtain ⟨mu, hmu⟩ := hkerT
  have hvscale : v = fun c => mu (N.classOf c) * w c := by
    funext c
    have hc := congrFun hmu c
    rw [N.linkageLift_apply] at hc
    dsimp [phi] at hc
    exact (div_eq_iff (hw c).ne').mp hc.symm
  apply hvker
  rw [hvscale]
  have hdecomp : (fun c => mu (N.classOf c) * w c) =
      ∑ q, mu q • N.restrictToClass q w := by
    funext c
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single (N.classOf c)]
    · rw [N.restrictToClass_apply_of_eq _ rfl]
    · intro q _ hq
      rw [N.restrictToClass_apply_of_ne]
      · ring
      · exact fun hc => hq hc.symm
    · exact fun h => (h (Finset.mem_univ _)).elim
  rw [hdecomp, map_sum]
  apply Finset.sum_eq_zero
  intro q _
  rw [map_smul, N.kineticMap_restrictToClass, hwker]
  funext c
  simp [restrictToClass]
end CRNT.Network

namespace CRNT.Network

open scoped BigOperators Classical

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Along a nonzero positive deficiency fibre, the deficiency logarithmic pairing lies strictly
on the side of its value at any positive kinetic-kernel reference dictated by the sign of the
fibre coordinate. -/
theorem deficiencyLogObstruction_strict_side_of_kernel
    (N : Network S) (κ : N.RateConstants)
    {g v w : N.ComplexIdx → ℝ} (hg0 : g ≠ 0)
    {a : ℝ} (ha : a ≠ 0) (hAv : N.kineticMap κ v = a • g)
    (hv : ∀ c, 0 < v c) (hw : ∀ c, 0 < w c) (hwker : N.kineticMap κ w = 0) :
    (a > 0 → (∑ c, g c * Real.log (v c)) < ∑ c, g c * Real.log (w c)) ∧
    (a < 0 → (∑ c, g c * Real.log (w c)) < ∑ c, g c * Real.log (v c)) := by
  have hAv0 : N.kineticMap κ v ≠ 0 := by
    rw [hAv]
    exact smul_ne_zero ha hg0
  have hdiss := N.kineticMap_logRatio_neg_of_ne_zero κ hv hw hwker hAv0
  have hrewrite :
      (∑ c, N.kineticMap κ v c * (Real.log (v c) - Real.log (w c))) =
        a * ((∑ c, g c * Real.log (v c)) - ∑ c, g c * Real.log (w c)) := by
    rw [hAv]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro c _
    ring
  rw [hrewrite] at hdiss
  constructor
  · intro hapos
    have := (mul_neg_iff.mp hdiss)
    rcases this with h | h
    · linarith [h.2]
    · exact False.elim (not_lt_of_ge hapos.le h.1)
  · intro haneg
    have := (mul_neg_iff.mp hdiss)
    rcases this with h | h
    · exact False.elim (not_lt_of_ge haneg.le h.1)
    · linarith [h.2]

end CRNT.Network
