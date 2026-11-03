import CRNT.Kinetics.General

/-!
# Hill and Michaelis–Menten kinetics

A **Hill rate law** gives reaction `r` the rate
`v_r(x) = V_r · ∏_{s ∈ supp(y_r)} x_s ^ n_{rs} / (K_{rs} ^ n_{rs} + x_s ^ n_{rs})`,
with maximal rate `V_r > 0`, half-saturation constants `K_{rs} > 0` and Hill coefficients
`n_{rs} ≥ 1`, the product running over the species of the source complex `y_r`. The case
`n ≡ 1` is Michaelis–Menten (Briggs–Haldane) kinetics `V x / (K + x)`.

The main result is that Hill kinetics is an admissible `Kinetics` in the sense of
`CRNT.Kinetics.General` (nonnegative, vanishing on absent source species, dependent on the
source support only, weakly monotone), so every kinetics-agnostic theorem of the library
(boundary non-attraction, conservation, the concordance/injectivity theory) applies to it.
We also record saturation `v_r ≤ V_r` and positivity on the positive orthant.

Main declarations:
* `CRNT.hillFactor`, `CRNT.hillFactor_monotoneOn`, `CRNT.hillFactor_lt_one`.
* `CRNT.Network.hillKinetics`, `CRNT.Network.hillKinetics_rate_le`,
  `CRNT.Network.hillKinetics_rate_pos`.
* `CRNT.Network.michaelisMentenKinetics`, `CRNT.Network.michaelisMentenKinetics_rate`.
-/

namespace CRNT

open scoped BigOperators

/-- The Hill function `x ^ n / (K ^ n + x ^ n)`. -/
noncomputable def hillFactor (K : ℝ) (n : ℕ) (x : ℝ) : ℝ := x ^ n / (K ^ n + x ^ n)

theorem hillFactor_denom_pos {K : ℝ} (hK : 0 < K) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 < K ^ n + x ^ n :=
  add_pos_of_pos_of_nonneg (pow_pos hK n) (pow_nonneg hx n)

theorem hillFactor_nonneg {K : ℝ} (hK : 0 < K) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ hillFactor K n x :=
  div_nonneg (pow_nonneg hx n) (hillFactor_denom_pos hK n hx).le

theorem hillFactor_pos {K : ℝ} (hK : 0 < K) (n : ℕ) {x : ℝ} (hx : 0 < x) :
    0 < hillFactor K n x :=
  div_pos (pow_pos hx n) (hillFactor_denom_pos hK n hx.le)

theorem hillFactor_zero {K : ℝ} {n : ℕ} (hn : n ≠ 0) : hillFactor K n 0 = 0 := by
  simp [hillFactor, zero_pow hn]

/-- The Hill function saturates strictly below one. -/
theorem hillFactor_lt_one {K : ℝ} (hK : 0 < K) (n : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    hillFactor K n x < 1 := by
  rw [hillFactor, div_lt_one (hillFactor_denom_pos hK n hx)]
  linarith [pow_pos hK n]

/-- The Hill function is nondecreasing on `[0, ∞)`. -/
theorem hillFactor_monotoneOn {K : ℝ} (hK : 0 < K) (n : ℕ) :
    MonotoneOn (hillFactor K n) (Set.Ici 0) := by
  intro x hx y _ hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := le_trans hx0 hxy
  rw [hillFactor, hillFactor, div_le_div_iff₀ (hillFactor_denom_pos hK n hx0)
    (hillFactor_denom_pos hK n hy0)]
  have hp : x ^ n ≤ y ^ n := pow_le_pow_left₀ hx0 hxy n
  nlinarith [pow_pos hK n]

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- Parameters of a Hill rate law: maximal rates, half-saturation constants and Hill
coefficients (one per reaction–species pair; only source species are used). -/
structure HillParameters (N : Network S) where
  /-- Maximal rate of each reaction. -/
  V : N.R → ℝ
  V_pos : ∀ r, 0 < V r
  /-- Half-saturation constant of species `s` in reaction `r`. -/
  K : N.R → S → ℝ
  K_pos : ∀ r s, 0 < K r s
  /-- Hill coefficient of species `s` in reaction `r`. -/
  n : N.R → S → ℕ
  n_pos : ∀ r s, 0 < n r s

/-- The Hill factor of species `s` in reaction `r` (equal to `1` for species not in the
source complex). -/
noncomputable def hillSpeciesFactor (N : Network S) (P : HillParameters N) (r : N.R) (s : S)
    (x : Concentration S) : ℝ :=
  if (N.reaction r).source s = 0 then 1 else hillFactor (P.K r s) (P.n r s) (x s)

/-- The Hill rate `V_r ∏_s h_{rs}(x_s)`. -/
noncomputable def hillRate (N : Network S) (P : HillParameters N) (r : N.R)
    (x : Concentration S) : ℝ :=
  P.V r * ∏ s, N.hillSpeciesFactor P r s x

theorem hillSpeciesFactor_nonneg (N : Network S) (P : HillParameters N) (r : N.R) (s : S)
    {x : Concentration S} (hx : x.Nonnegative) : 0 ≤ N.hillSpeciesFactor P r s x := by
  unfold hillSpeciesFactor
  split_ifs
  · exact zero_le_one
  · exact hillFactor_nonneg (P.K_pos r s) _ (hx s)

theorem hillSpeciesFactor_le_one (N : Network S) (P : HillParameters N) (r : N.R) (s : S)
    {x : Concentration S} (hx : x.Nonnegative) : N.hillSpeciesFactor P r s x ≤ 1 := by
  unfold hillSpeciesFactor
  split_ifs
  · exact le_rfl
  · exact (hillFactor_lt_one (P.K_pos r s) _ (hx s)).le

/-- **Hill kinetics is an admissible kinetics.** -/
noncomputable def hillKinetics (N : Network S) (P : HillParameters N) : Kinetics N where
  rate := N.hillRate P
  rate_nonneg := by
    intro r x hx
    exact mul_nonneg (P.V_pos r).le
      (Finset.prod_nonneg fun s _ => N.hillSpeciesFactor_nonneg P r s hx)
  rate_vanishing := by
    intro r x s hsrc hs
    unfold hillRate
    rw [Finset.prod_eq_zero (Finset.mem_univ s), mul_zero]
    simp only [hillSpeciesFactor, hsrc, ite_false, hs]
    exact hillFactor_zero (P.n_pos r s).ne'
  rate_supportDep := by
    intro r x y hxy
    unfold hillRate
    congr 1
    refine Finset.prod_congr rfl fun s _ => ?_
    unfold hillSpeciesFactor
    split_ifs with h
    · rfl
    · rw [hxy s h]
  rate_mono := by
    intro r x hx y hy hxy
    unfold hillRate
    refine mul_le_mul_of_nonneg_left ?_ (P.V_pos r).le
    refine Finset.prod_le_prod₀ (fun s _ => N.hillSpeciesFactor_nonneg P r s hx)
      (fun s _ => ?_)
    unfold hillSpeciesFactor
    split_ifs
    · exact le_rfl
    · exact hillFactor_monotoneOn (P.K_pos r s) _ (Set.mem_Ici.mpr (hx s))
        (Set.mem_Ici.mpr (hy s)) (hxy s)

theorem hillKinetics_rate (N : Network S) (P : HillParameters N) (r : N.R)
    (x : Concentration S) : (N.hillKinetics P).rate r x = N.hillRate P r x := rfl

/-- **Saturation.** On the nonnegative orthant every Hill rate is at most its maximal rate. -/
theorem hillKinetics_rate_le (N : Network S) (P : HillParameters N) (r : N.R)
    {x : Concentration S} (hx : x.Nonnegative) : (N.hillKinetics P).rate r x ≤ P.V r := by
  rw [hillKinetics_rate, hillRate]
  have : ∏ s, N.hillSpeciesFactor P r s x ≤ 1 :=
    Finset.prod_le_one₀ (fun s _ => N.hillSpeciesFactor_nonneg P r s hx)
      (fun s _ => N.hillSpeciesFactor_le_one P r s hx)
  nlinarith [P.V_pos r]

/-- On the positive orthant every Hill rate is strictly positive. -/
theorem hillKinetics_rate_pos (N : Network S) (P : HillParameters N) (r : N.R)
    {x : Concentration S} (hx : x.Positive) : 0 < (N.hillKinetics P).rate r x := by
  rw [hillKinetics_rate, hillRate]
  refine mul_pos (P.V_pos r) (Finset.prod_pos fun s _ => ?_)
  unfold hillSpeciesFactor
  split_ifs
  · exact zero_lt_one
  · exact hillFactor_pos (P.K_pos r s) _ (hx s)

/-- Michaelis–Menten parameters: maximal rates and Michaelis constants. -/
structure MichaelisMentenParameters (N : Network S) where
  V : N.R → ℝ
  V_pos : ∀ r, 0 < V r
  Km : N.R → S → ℝ
  Km_pos : ∀ r s, 0 < Km r s

/-- Michaelis–Menten kinetics: the Hill kinetics with all Hill coefficients equal to one. -/
noncomputable def michaelisMentenKinetics (N : Network S) (P : MichaelisMentenParameters N) :
    Kinetics N :=
  N.hillKinetics ⟨P.V, P.V_pos, P.Km, P.Km_pos, fun _ _ => 1, fun _ _ => Nat.one_pos⟩

/-- The Michaelis–Menten rate is `V_r ∏_{s ∈ supp y_r} x_s / (K_{rs} + x_s)`. -/
theorem michaelisMentenKinetics_rate (N : Network S) (P : MichaelisMentenParameters N)
    (r : N.R) (x : Concentration S) :
    (N.michaelisMentenKinetics P).rate r x =
      P.V r * ∏ s, if (N.reaction r).source s = 0 then 1 else x s / (P.Km r s + x s) := by
  show P.V r * ∏ s, N.hillSpeciesFactor _ r s x = _
  congr 1
  refine Finset.prod_congr rfl fun s _ => ?_
  simp [hillSpeciesFactor, hillFactor]

end Network

end CRNT
