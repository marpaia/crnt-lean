import CRNT.Analysis.BorosProjectionDecomposition
import CRNT.Deficiency.BorosBirchGraph
import CRNT.Deficiency.BorosSingleLinkageEstimate
import CRNT.Deficiency.ClassConservation
import CRNT.Geometry.EndotacticGlobal
import CRNT.Theorems.DeficiencyZero.Dissipation

/-!
# Uniform boundary estimates for Boros's nested domain

This file supplies the finite classwise estimates used to make the Birch-projected kinetic field
strictly inward on every active Boros face.
-/

namespace CRNT
namespace Network

open scoped BigOperators
open scoped InnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The Birch parameter space is contained in the incidence space because its defining map
ends with the orthogonal projection onto that space. -/
theorem borosBirchParameterSpace_le_borosIncidenceEuclidSpace (N : Network S) :
    N.borosBirchParameterSpace ≤ N.borosIncidenceEuclidSpace := by
  rintro z ⟨p, rfl⟩
  change N.borosIncidenceEuclidSpace.starProjection
      (toEuclid (N.complexTransposeMap p)) ∈ N.borosIncidenceEuclidSpace
  exact N.borosIncidenceEuclidSpace.starProjection_apply_mem _

/-- The kinetic pairing against a complex potential is the reaction flux weighted by its
target-minus-source increment. -/
theorem inner_toEuclid_kineticMap_eq_edgeSum (N : Network S)
    (κ : N.RateConstants) (m u : N.ComplexIdx → ℝ) :
    ⟪toEuclid (N.kineticMap κ m), toEuclid u⟫_ℝ =
      ∑ r : N.R, κ.k r * m (N.sourceIdx r) *
        (u (N.targetIdx r) - u (N.sourceIdx r)) := by
  rw [inner_toEuclid]
  simp only [N.kineticMap_apply]
  calc
    _ = ∑ c : N.ComplexIdx, ∑ r : N.R,
        (κ.k r * m (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) -
            (if N.sourceIdx r = c then 1 else 0))) * u c := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finset.sum_mul]
    _ = ∑ r : N.R, ∑ c : N.ComplexIdx,
        (κ.k r * m (N.sourceIdx r) *
          ((if N.targetIdx r = c then (1 : ℝ) else 0) -
            (if N.sourceIdx r = c then 1 else 0))) * u c := Finset.sum_comm
    _ = _ := by
          apply Finset.sum_congr rfl
          intro r _
          let flux := κ.k r * m (N.sourceIdx r)
          have hsplit :
              (∑ c : N.ComplexIdx,
                ((if N.targetIdx r = c then (1 : ℝ) else 0) -
                  (if N.sourceIdx r = c then 1 else 0)) * u c) =
                u (N.targetIdx r) - u (N.sourceIdx r) := by
            calc
              _ = ∑ c : N.ComplexIdx,
                  ((if N.targetIdx r = c then (1 : ℝ) else 0) * u c -
                    (if N.sourceIdx r = c then 1 else 0) * u c) := by
                      apply Finset.sum_congr rfl
                      intro c _
                      ring
              _ = _ := by rw [Finset.sum_sub_distrib, N.sum_ite_one_mul,
                N.sum_ite_one_mul]
          calc
            _ = flux * ∑ c : N.ComplexIdx,
                ((if N.targetIdx r = c then (1 : ℝ) else 0) -
                  (if N.sourceIdx r = c then 1 else 0)) * u c := by
                    rw [Finset.mul_sum]
                    apply Finset.sum_congr rfl
                    intro c _
                    dsimp [flux]
                    ring
            _ = _ := by rw [hsplit]

/-- Every linkage class contains the source of at least one reaction in a weakly reversible
network. A complex appears as a reaction source or target; in the target case weak reversibility
returns it as a source. -/
theorem borosClassReaction_nonempty (N : Network S) (hwr : N.WeaklyReversible)
    (q : Quotient N.linkedSetoid) : Nonempty (N.BorosClassReaction q) := by
  classical
  obtain ⟨c, hc⟩ := Quotient.exists_rep q
  have hclass : N.classOf c = q := by simpa [classOf] using hc
  rcases Finset.mem_union.mp c.property with hsrc | htgt
  · obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hsrc
    have hsource : N.sourceIdx r = c := Subtype.ext hr
    refine ⟨⟨r, ?_⟩⟩
    change N.classOf (N.sourceIdx r) = q
    rw [hsource]
    exact hclass
  · obtain ⟨r, _, hr⟩ := Finset.mem_image.mp htgt
    obtain ⟨r', hr'⟩ := hwr.exists_source_eq_target r
    have hsource : N.sourceIdx r' = c := Subtype.ext (hr'.trans hr)
    refine ⟨⟨r', ?_⟩⟩
    change N.classOf (N.sourceIdx r') = q
    rw [hsource]
    exact hclass

/-- A finite weakly reversible network has global positive lower and finite upper bounds on its
reaction rate constants. -/
theorem exists_borosUniformRateBounds (N : Network S)
    [Nonempty (Quotient N.linkedSetoid)] (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) :
    ∃ kmin kmax : ℝ, 0 < kmin ∧ (∀ r, kmin ≤ κ.k r) ∧
      0 < kmax ∧ (∀ r, κ.k r ≤ kmax) := by
  classical
  obtain ⟨q⟩ := ‹Nonempty (Quotient N.linkedSetoid)›
  obtain ⟨r₀⟩ := N.borosClassReaction_nonempty hwr q
  letI : Nonempty N.R := ⟨r₀.val⟩
  let values : Finset ℝ := Finset.univ.image κ.k
  have hv : values.Nonempty := by
    exact ⟨κ.k r₀.val, Finset.mem_image.mpr ⟨r₀.val, Finset.mem_univ _, rfl⟩⟩
  let kmin := values.min' hv
  let kmax := values.max' hv
  have hminmem : kmin ∈ values := Finset.min'_mem values hv
  have hmaxmem : kmax ∈ values := Finset.max'_mem values hv
  obtain ⟨rmin, _, hrmin⟩ := Finset.mem_image.mp hminmem
  obtain ⟨rmax, _, hrmax⟩ := Finset.mem_image.mp hmaxmem
  refine ⟨kmin, kmax, ?_, ?_, ?_, ?_⟩
  · simpa [kmin, hrmin] using κ.positive rmin
  · intro r
    exact Finset.min'_le values (κ.k r)
      (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)
  · simpa [kmax, hrmax] using κ.positive rmax
  · intro r
    exact Finset.le_max' values (κ.k r)
      (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, rfl⟩)

/-- The number of reactions whose source lies in a fixed linkage class is bounded by the total
number of reactions. -/
theorem borosClassReaction_card_le (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)] (q : Quotient N.linkedSetoid) :
    Fintype.card (N.BorosClassReaction q) ≤ Fintype.card N.R :=
  Fintype.card_le_of_injective Subtype.val (fun _ _ h => Subtype.ext h)

/-- The source-rate budget used for every linkage class when the orthogonal residual is bounded
by `rho`. -/
noncomputable def borosClassBudget (N : Network S) (kmin kmax rho : ℝ) : ℝ :=
  ((Fintype.card N.R : ℝ) + 1) * (kmax * Real.exp rho) /
    (kmin * Real.exp (-rho))

theorem borosClassBudget_pos (N : Network S) {kmin kmax rho : ℝ}
    (hkmin : 0 < kmin) (hkmax : 0 < kmax) :
    0 < N.borosClassBudget kmin kmax rho := by
  unfold borosClassBudget
  positivity

theorem borosClassBudget_dominates_each_class (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    (q : Quotient N.linkedSetoid) {kmin kmax rho : ℝ}
    (hkminpos : 0 < kmin) (hkmaxpos : 0 < kmax) :
    (Fintype.card (N.BorosClassReaction q) : ℝ) * (kmax * Real.exp rho) <
      (kmin * Real.exp (-rho)) * N.borosClassBudget kmin kmax rho := by
  have hrate : 0 < kmax * Real.exp rho := mul_pos hkmaxpos (Real.exp_pos _)
  have hcardNat := N.borosClassReaction_card_le q
  have hcard : (Fintype.card (N.BorosClassReaction q) : ℝ) <
      (Fintype.card N.R : ℝ) + 1 := by
    have h := Nat.lt_succ_of_le hcardNat
    exact_mod_cast h
  have hleft :
      (Fintype.card (N.BorosClassReaction q) : ℝ) * (kmax * Real.exp rho) <
        ((Fintype.card N.R : ℝ) + 1) * (kmax * Real.exp rho) :=
    mul_lt_mul_of_pos_right hcard hrate
  have hden : 0 < kmin * Real.exp (-rho) := mul_pos hkminpos (Real.exp_pos _)
  calc
    _ < ((Fintype.card N.R : ℝ) + 1) * (kmax * Real.exp rho) := hleft
    _ = (kmin * Real.exp (-rho)) * N.borosClassBudget kmin kmax rho := by
      rw [borosClassBudget]
      field_simp [ne_of_gt hden]

/-- Norm threshold for the single-class zero-sum estimate when the selector residual is bounded
by `rho`. -/
noncomputable def borosBoundaryThreshold (N : Network S) (kmin kmax rho : ℝ) : ℝ :=
  (Fintype.card N.ComplexIdx : ℝ) * (Fintype.card N.ComplexIdx : ℝ) *
    (Analysis.borosWeightedPathBound
      (N.borosClassBudget kmin kmax rho) N.borosUniformReactionPathLength + 1)

private theorem borosWeightedPathBound_nonneg {b : ℝ} (hb : 0 ≤ b) :
    ∀ n, 0 ≤ Analysis.borosWeightedPathBound b n := by
  intro n
  induction n with
  | zero => simp [Analysis.borosWeightedPathBound]
  | succ n ih =>
      simp only [Analysis.borosWeightedPathBound]
      exact mul_nonneg hb (Real.exp_pos _).le

theorem borosBoundaryThreshold_pos (N : Network S)
    [Nonempty (Quotient N.linkedSetoid)] (hwr : N.WeaklyReversible)
    {kmin kmax rho : ℝ} (hkmin : 0 < kmin) (hkmax : 0 < kmax) :
    0 < N.borosBoundaryThreshold kmin kmax rho := by
  have hcomplex : Nonempty N.ComplexIdx := by
    obtain ⟨q⟩ := ‹Nonempty (Quotient N.linkedSetoid)›
    obtain ⟨r⟩ := N.borosClassReaction_nonempty hwr q
    exact ⟨N.sourceIdx r.val⟩
  have hC : 0 < (Fintype.card N.ComplexIdx : ℝ) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr hcomplex)
  have hb : 0 ≤ N.borosClassBudget kmin kmax rho :=
    (N.borosClassBudget_pos hkmin hkmax).le
  have hpath := borosWeightedPathBound_nonneg hb N.borosUniformReactionPathLength
  unfold borosBoundaryThreshold
  exact mul_pos (mul_pos hC hC) (by linarith)

/-- One positive projection lower bound works for every nonempty subset of classes and every
singleton block inside it. The index family is finite, so the minimum of the individual positive
constants remains positive. -/
theorem exists_uniform_borosSingletonResidual_lower_bound
    {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Analysis.BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ Q : Analysis.BorosSubsetIndex I, ∀ i ∈ Q.1, ∀ y,
        y ∈ Analysis.borosResidualSubspace P H Q.1 {i} →
          ε * ‖y‖ ≤ ‖P.project {i} y‖ := by
  classical
  let J := {p : Analysis.BorosSubsetIndex I × I // p.2 ∈ p.1.1}
  let pairEpsilon : J → ℝ := fun p =>
    Classical.choose (Analysis.exists_positive_norm_lower_bound_borosResidual P H
      (Finset.singleton_subset_iff.mpr p.property))
  have hpairEpsilon (p : J) : 0 < pairEpsilon p ∧
      ∀ y, y ∈ Analysis.borosResidualSubspace P H p.1.1.1 {p.1.2} →
        pairEpsilon p * ‖y‖ ≤ ‖P.project {p.1.2} y‖ := by
    simpa [pairEpsilon] using
      (Classical.choose_spec (Analysis.exists_positive_norm_lower_bound_borosResidual P H
        (Finset.singleton_subset_iff.mpr p.property)))
  have hJ : Nonempty J := by
    obtain ⟨i⟩ := ‹Nonempty I›
    let Q : Analysis.BorosSubsetIndex I := ⟨{i}, by simp⟩
    exact ⟨⟨(Q, i), by simp [Q]⟩⟩
  let values : Finset ℝ := Finset.univ.image pairEpsilon
  have hvalues : values.Nonempty := by
    obtain ⟨p⟩ := hJ
    exact ⟨pairEpsilon p,
      Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩⟩
  let ε₀ : ℝ := values.min' hvalues
  have hε₀pos : 0 < ε₀ := by
    obtain ⟨p, _, hp⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
    simpa [ε₀, hp] using (hpairEpsilon p).1
  refine ⟨min ε₀ 1, lt_min hε₀pos zero_lt_one, min_le_right _ _, ?_⟩
  intro Q i hi y hy
  let p : J := ⟨(Q, i), hi⟩
  have hmin : ε₀ ≤ pairEpsilon p :=
    Finset.min'_le values (pairEpsilon p)
      (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)
  exact (mul_le_mul_of_nonneg_right
    (le_trans (min_le_left _ _) hmin) (norm_nonneg _)).trans
    ((hpairEpsilon p).2 y (by simpa [p] using hy))

/-- A recursively chosen increasing radius sequence can dominate any sequence of nonnegative
thresholds by the Boros square-root gap. -/
theorem exists_boros_radii_of_thresholds {ε : ℝ} (hε : 0 < ε)
    (T : ℕ → ℝ) (hT : ∀ n, 0 ≤ T n) :
    ∃ r : ℕ → ℝ, r 0 = 0 ∧ Monotone r ∧ (∀ n, 0 ≤ r n) ∧
      ∀ n, T n < ε * Real.sqrt ((r (n + 1) ^ 2 - r n ^ 2) / 2) := by
  let r : ℕ → ℝ := Nat.rec 0 (fun n a => a + 4 * (T n + 1) / ε)
  have hrzero : r 0 = 0 := rfl
  have hrnonneg : ∀ n, 0 ≤ r n := by
    intro n
    induction n with
    | zero => simp [r]
    | succ n ih =>
        simp [r]
        have hinc : 0 ≤ 4 * (T n + 1) / ε :=
          div_nonneg (mul_nonneg (by norm_num) (add_nonneg (hT n) (by norm_num))) hε.le
        linarith
  have hrmono : Monotone r := by
    apply monotone_nat_of_le_succ
    intro n
    simp [r]
    have hinc : 0 ≤ 4 * (T n + 1) / ε :=
      div_nonneg (mul_nonneg (by norm_num) (add_nonneg (hT n) (by norm_num))) hε.le
    linarith
  refine ⟨r, hrzero, hrmono, hrnonneg, ?_⟩
  intro n
  let d : ℝ := 4 * (T n + 1) / ε
  have hd : 0 < d := by
    dsimp [d]
    have hTpos : 0 < T n + 1 := by linarith [hT n]
    exact div_pos (mul_pos (by norm_num) hTpos) hε
  have hstep : r (n + 1) = r n + d := by simp [r, d]
  have hrad : (d / 2) ^ 2 ≤ (r (n + 1) ^ 2 - r n ^ 2) / 2 := by
    rw [hstep]
    have hbase := hrnonneg n
    nlinarith [sq_nonneg (r n), sq_nonneg d]
  have hsqrt : d / 2 ≤ Real.sqrt ((r (n + 1) ^ 2 - r n ^ 2) / 2) :=
    Real.le_sqrt_of_sq_le hrad
  have htarget : T n < ε * (d / 2) := by
    dsimp [d]
    field_simp [ne_of_gt hε]
    nlinarith [hT n]
  exact lt_of_lt_of_le htarget (mul_le_mul_of_nonneg_left hsqrt hε.le)

/-- Stateful form of the radius recursion: the next threshold may depend on the current radius.
This is the form needed because the admissible rate budget grows with the residual bound. -/
theorem exists_boros_radii_of_stateful_threshold {ε : ℝ} (hε : 0 < ε)
    (T : ℝ → ℝ) (hT : ∀ a, 0 ≤ T a) :
    ∃ r : ℕ → ℝ, r 0 = 0 ∧ Monotone r ∧ (∀ n, 0 ≤ r n) ∧
      ∀ n, T (r n) < ε * Real.sqrt ((r (n + 1) ^ 2 - r n ^ 2) / 2) := by
  let r : ℕ → ℝ := Nat.rec 0 (fun n a => a + 4 * (T a + 1) / ε)
  have hrzero : r 0 = 0 := rfl
  have hrnonneg : ∀ n, 0 ≤ r n := by
    intro n
    induction n with
    | zero => simp [r]
    | succ n ih =>
        simp [r]
        have hinc : 0 ≤ 4 * (T (r n) + 1) / ε :=
          div_nonneg (mul_nonneg (by norm_num) (add_nonneg (hT _) (by norm_num))) hε.le
        linarith
  have hrmono : Monotone r := by
    apply monotone_nat_of_le_succ
    intro n
    simp [r]
    have hinc : 0 ≤ 4 * (T (r n) + 1) / ε :=
      div_nonneg (mul_nonneg (by norm_num) (add_nonneg (hT _) (by norm_num))) hε.le
    linarith
  refine ⟨r, hrzero, hrmono, hrnonneg, ?_⟩
  intro n
  let d : ℝ := 4 * (T (r n) + 1) / ε
  have hd : 0 < d := by
    dsimp [d]
    have hTpos : 0 < T (r n) + 1 := by linarith [hT (r n)]
    exact div_pos (mul_pos (by norm_num) hTpos) hε
  have hstep : r (n + 1) = r n + d := by simp [r, d]
  have hrad : (d / 2) ^ 2 ≤ (r (n + 1) ^ 2 - r n ^ 2) / 2 := by
    rw [hstep]
    have hbase := hrnonneg n
    nlinarith [sq_nonneg (r n), sq_nonneg d]
  have hsqrt : d / 2 ≤ Real.sqrt ((r (n + 1) ^ 2 - r n ^ 2) / 2) :=
    Real.le_sqrt_of_sq_le hrad
  have htarget : T (r n) < ε * (d / 2) := by
    dsimp [d]
    field_simp [ne_of_gt hε]
    nlinarith [hT (r n)]
  exact lt_of_lt_of_le htarget (mul_le_mul_of_nonneg_left hsqrt hε.le)

/-- Choose rate bounds, a uniform residual projection constant, and an increasing radius sequence
whose next square-root gap exceeds the single-class norm threshold at the current residual radius.
This is the quantitative schedule used by the inward-face proof. -/
theorem exists_borosActiveRadiusSchedule (N : Network S)
    [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)] (hwr : N.WeaklyReversible)
    (κ : N.RateConstants) :
    ∃ kmin kmax ε : ℝ, ∃ r : ℕ → ℝ,
      0 < kmin ∧ (∀ r₀, kmin ≤ κ.k r₀) ∧
      0 < kmax ∧ (∀ r₀, κ.k r₀ ≤ kmax) ∧
      0 < ε ∧ ε ≤ 1 ∧ r 0 = 0 ∧ Monotone r ∧ (∀ n, 0 ≤ r n) ∧
      (∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid), ∀ i ∈ Q.1,
        ∀ y, y ∈ Analysis.borosResidualSubspace N.borosLinkageProjectionSystem
          N.borosBirchParameterSpace Q.1 {i} →
          ε * ‖y‖ ≤ ‖N.borosLinkageProjectionSystem.project {i} y‖) ∧
      ∀ n, N.borosBoundaryThreshold kmin kmax (r n) <
        ε * Real.sqrt ((r (n + 1) ^ 2 - r n ^ 2) / 2) := by
  obtain ⟨kmin, kmax, hkmin, hkminall, hkmax, hkmaxall⟩ :=
    N.exists_borosUniformRateBounds hwr κ
  obtain ⟨ε, hε, hεone, hεres⟩ :=
    exists_uniform_borosSingletonResidual_lower_bound
      N.borosLinkageProjectionSystem N.borosBirchParameterSpace
  have hT : ∀ rho, 0 ≤ N.borosBoundaryThreshold kmin kmax rho := by
    intro rho
    exact (N.borosBoundaryThreshold_pos hwr hkmin hkmax).le
  obtain ⟨r, hrzero, hrmono, hrnonneg, hrstep⟩ :=
    exists_boros_radii_of_stateful_threshold hε
      (N.borosBoundaryThreshold kmin kmax) hT
  exact ⟨kmin, kmax, ε, r, hkmin, hkminall, hkmax, hkmaxall,
    hε, hεone, hrzero, hrmono, hrnonneg, hεres, hrstep⟩

/-- On an active face, the singleton coordinate belonging to any selected block has a
quantitative lower bound. The full-set constraint supplies the outer radius, while removing one
block exposes the next radius in the schedule. -/
theorem borosActiveFaceSingletonProjection_lower
    {I E : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (P : Analysis.BorosBlockProjectionSystem (I := I) (E := E))
    (H : Submodule ℝ E) (r : ℕ → ℝ) (hr0 : r 0 = 0)
    (hrmono : Monotone r) (hrnonneg : ∀ n, 0 ≤ r n)
    (Q : Analysis.BorosSubsetIndex I) (i : I) (hi : i ∈ Q.1) (z : H)
    (hz : z ∈ Analysis.borosWithinSubspaceNestedDomain P H r)
    (hactive : ‖Analysis.borosWithinSubspaceProjectionFamily P H Q z‖ =
      Analysis.borosProjectionRadius r Q)
    {ε : ℝ} (hε : 0 < ε) (hεone : ε ≤ 1)
    (hres : ∀ y, y ∈ Analysis.borosResidualSubspace P H Q.1 {i} →
      ε * ‖y‖ ≤ ‖P.project {i} y‖) :
    ε * Real.sqrt
      ((r (Fintype.card I - Q.1.card + 1) ^ 2 -
        r (Fintype.card I - Q.1.card) ^ 2) / 2) ≤
      ‖P.project {i}
        ((Analysis.borosLinkageSliceWithin P H Q.1).starProjection z).1‖ := by
  classical
  let ell := Fintype.card I
  let j := ell - Q.1.card
  let R := r ell
  let pQ := (Analysis.borosLinkageSliceWithin P H Q.1).starProjection z
  let D := Q.1 \ {i}
  let pD := (Analysis.borosLinkageSliceWithin P H D).starProjection z
  let Qtop : Analysis.BorosSubsetIndex I := ⟨Finset.univ, by simp⟩
  have hQcard : Q.1.card ≤ ell := by
    dsimp [ell]
    exact Finset.card_le_card (Finset.subset_univ _)
  have hQpos : 0 < Q.1.card := Finset.card_pos.mpr Q.2
  have htopid : Analysis.borosWithinSubspaceProjectionFamily P H Qtop =
      ContinuousLinearMap.id ℝ H := by
    simpa [Qtop] using Analysis.borosWithinSubspaceProjectionFamily_univ P H
  have htopradius : Analysis.borosProjectionRadius r Qtop = R := by
    simpa [Qtop, R, ell] using
      Analysis.borosProjectionRadius_univ r hr0 (hrnonneg ell)
  have hzconstraints := hz
  change ∀ B : Analysis.BorosSubsetIndex I,
    ‖Analysis.borosWithinSubspaceProjectionFamily P H B z‖ ≤
      Analysis.borosProjectionRadius r B at hzconstraints
  have houter : ‖z‖ ≤ R := by
    have h := hzconstraints Qtop
    rw [htopid, ContinuousLinearMap.id_apply, htopradius] at h
    exact h
  have hactive' : ‖pQ‖ = Analysis.borosProjectionRadius r Q := by
    simpa [pQ, Analysis.borosWithinSubspaceProjectionFamily] using hactive
  have hradQ : 0 ≤ R ^ 2 - (r j) ^ 2 := by
    simpa [Analysis.borosProjectionRadius, ell, j, R] using
      Analysis.borosProjectionRadius_radicand_nonneg r hrmono hrnonneg Q
  have hactiveSq : ‖pQ‖ ^ 2 = R ^ 2 - (r j) ^ 2 := by
    calc
      ‖pQ‖ ^ 2 = Analysis.borosProjectionRadius r Q ^ 2 := by rw [hactive']
      _ = R ^ 2 - (r j) ^ 2 := by
        simpa [Analysis.borosProjectionRadius, ell, j, R] using Real.sq_sqrt hradQ
  have hDj : ell - D.card = j + 1 := by
    have hDcard : D.card = Q.1.card - 1 := by
      simpa [D] using
        (Finset.card_sdiff_of_subset (Finset.singleton_subset_iff.mpr hi))
    dsimp [ell, j]
    omega
  have hrestSq : ‖pD‖ ^ 2 ≤ R ^ 2 - (r (j + 1)) ^ 2 := by
    by_cases hD : D.Nonempty
    · let QD : Analysis.BorosSubsetIndex I := ⟨D, hD⟩
      have hDbound : ‖pD‖ ≤ Analysis.borosProjectionRadius r QD := by
        have h := hzconstraints QD
        simpa [pD, QD, Analysis.borosWithinSubspaceProjectionFamily] using h
      have hDnonneg := Analysis.borosProjectionRadius_nonneg r QD
      have hDsq := (sq_le_sq₀ (norm_nonneg _) hDnonneg).2 hDbound
      have hDelt : 0 ≤ r ell ^ 2 - r (j + 1) ^ 2 := by
        have hindex : j + 1 ≤ ell := by
          dsimp [ell, j]
          omega
        have hrad := Analysis.borosProjectionRadius_radicand_nonneg r hrmono hrnonneg QD
        simpa [Analysis.borosProjectionRadius, QD, ell, hDj] using hrad
      have hDsq' : Analysis.borosProjectionRadius r QD ^ 2 =
          R ^ 2 - (r (j + 1)) ^ 2 := by
        simpa [Analysis.borosProjectionRadius, QD, ell, R, hDj] using
          Real.sq_sqrt hDelt
      simpa [R] using hDsq.trans_eq hDsq'
    · have hDempty : D = ∅ := Finset.not_nonempty_iff_eq_empty.mp hD
      have hDproj : Analysis.borosLinkageSliceWithin P H D = ⊥ := by
        rw [hDempty]
        exact Analysis.borosLinkageSliceWithin_empty P H
      have hpDzero : pD = 0 := by
        simp [pD, hDproj]
      have hindex : j + 1 ≤ ell := by
        dsimp [ell, j]
        omega
      have hrorder : r (j + 1) ≤ r ell := hrmono hindex
      have hrsq : r (j + 1) ^ 2 ≤ r ell ^ 2 :=
        (sq_le_sq₀ (hrnonneg _) (hrnonneg _)).2 hrorder
      rw [hpDzero]
      simp only [norm_zero, zero_pow, R]
      nlinarith [hrsq]
  have hgap : 0 ≤ r (j + 1) ^ 2 - r j ^ 2 := by
    have horder : r j ≤ r (j + 1) := hrmono (Nat.le_succ j)
    have hsum : 0 ≤ r j + r (j + 1) := add_nonneg (hrnonneg _) (hrnonneg _)
    nlinarith [mul_nonneg (sub_nonneg.mpr horder) hsum]
  have hactiveForProjection : ‖pQ‖ ^ 2 = R ^ 2 - (r j) ^ 2 := by
    simpa [pQ, R, j] using hactiveSq
  have hrestForProjection : ‖pD‖ ^ 2 ≤ R ^ 2 - (r (j + 1)) ^ 2 := by
    simpa [pD, R, j] using hrestSq
  simpa [j, ell, pQ] using
    Analysis.borosWithinProjection_singleton_component_norm_lower P H i hi z
      hactiveForProjection hrestForProjection hgap hε hεone hres

/-- If every active linkage class has a large zero-mean component and every inactive class is
annihilated by the potential, the full mass-action kinetic pairing is strictly negative. -/
theorem borosKineticPairing_neg_of_activeClasses
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (A : Finset (Quotient N.linkedSetoid)) (hAnonempty : A.Nonempty)
    {kmin kmax rho b threshold : ℝ}
    (hkminpos : 0 < kmin) (hkmin : ∀ r, kmin ≤ κ.k r)
    (hkmaxpos : 0 < kmax) (hkmax : ∀ r, κ.k r ≤ kmax)
    (hb : 0 ≤ b)
    (hbudget : ∀ q,
      (Fintype.card (N.BorosClassReaction q) : ℝ) * (kmax * Real.exp rho) <
        (kmin * Real.exp (-rho)) * b)
    (u w : N.ComplexIdx → ℝ) (alpha : Quotient N.linkedSetoid → ℝ)
    (m : N.ComplexIdx → ℝ)
    (hwbound : ∀ c, |w c| ≤ rho)
    (huzero : ∀ c, N.classOf c ∉ A → u c = 0)
    (hzero : ∀ q, q ∈ A →
      ∑ c : {c : N.ComplexIdx // N.classOf c = q}, u c.val = 0)
    (hnorm : ∀ q, q ∈ A →
      (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) ^ 2 * threshold <
        ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => u c.val)‖)
    (hmonomial : ∀ q, q ∈ A → ∀ c, N.classOf c = q →
      m c = Real.exp (u c + w c + alpha q))
    (hthreshold : Analysis.borosWeightedPathBound b N.borosUniformReactionPathLength <
      threshold) :
    ⟪toEuclid (N.kineticMap κ m), toEuclid u⟫_ℝ < 0 := by
  classical
  have hclassPair : ∀ q, q ∈ A →
      ∑ r : N.BorosClassReaction q,
        κ.k r.val * Real.exp (u (N.sourceIdx r.val) + w (N.sourceIdx r.val) + alpha q) *
          (u (N.targetIdx r.val) - u (N.sourceIdx r.val)) < 0 := by
    intro q hq
    obtain ⟨r⟩ := N.borosClassReaction_nonempty hwr q
    have hclassNonempty : ∃ c, N.classOf c = q :=
      ⟨N.sourceIdx r.val, r.property⟩
    have hnorm' :
        (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) *
          (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) * threshold <
            ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => u c.val)‖ := by
      simpa [pow_two] using hnorm q hq
    exact WeaklyReversible.boros_classPairing_neg_of_zeroSum_norm_large_classShift
      N hwr κ q u w alpha hclassNonempty (hzero q hq) hnorm'
      (fun c _ => hwbound c) hb hkminpos
      (fun r _ => hkmin r) (fun r _ => hkmax r) (hbudget q) hthreshold
  have hclassZero : ∀ q, q ∉ A →
      ∑ r : N.BorosClassReaction q,
        κ.k r.val * m (N.sourceIdx r.val) *
          (u (N.targetIdx r.val) - u (N.sourceIdx r.val)) = 0 := by
    intro q hq
    apply Finset.sum_eq_zero
    intro r _
    have hsrc : N.classOf (N.sourceIdx r.val) ∉ A := by
      simpa [r.property] using hq
    have htgt : N.classOf (N.targetIdx r.val) ∉ A := by
      rw [← N.classOf_sourceIdx_eq_targetIdx]
      exact hsrc
    rw [huzero _ hsrc, huzero _ htgt]
    ring
  have hclassActual : ∀ q, q ∈ A →
      ∑ r : N.BorosClassReaction q,
        κ.k r.val * m (N.sourceIdx r.val) *
          (u (N.targetIdx r.val) - u (N.sourceIdx r.val)) < 0 := by
    intro q hq
    calc
      _ = ∑ r : N.BorosClassReaction q,
          κ.k r.val * Real.exp
            (u (N.sourceIdx r.val) + w (N.sourceIdx r.val) + alpha q) *
            (u (N.targetIdx r.val) - u (N.sourceIdx r.val)) := by
              apply Finset.sum_congr rfl
              intro r _
              rw [hmonomial q hq (N.sourceIdx r.val) r.property]
      _ < 0 := hclassPair q hq
  let term : N.R → ℝ := fun r => κ.k r * m (N.sourceIdx r) *
    (u (N.targetIdx r) - u (N.sourceIdx r))
  let fiberEquiv := Equiv.sigmaFiberEquiv
    (fun r : N.R => N.classOf (N.sourceIdx r))
  have hpartition :
      (∑ r : N.R, term r) =
        ∑ q, ∑ r : N.BorosClassReaction q, term r.val := by
    calc
      _ = ∑ s : Σ q, N.BorosClassReaction q, term (fiberEquiv s) :=
        (Equiv.sum_comp fiberEquiv term).symm
      _ = _ := by
        rw [Fintype.sum_sigma]
        simp [fiberEquiv, Equiv.sigmaFiberEquiv, term]
  have hsum :
      (∑ q, ∑ r : N.BorosClassReaction q, term r.val) < 0 := by
    have hsum' :
        (∑ q, ∑ r : N.BorosClassReaction q, term r.val) <
          (∑ q : Quotient N.linkedSetoid, (0 : ℝ)) := by
      apply Finset.sum_lt_sum
      · intro q _
        by_cases hq : q ∈ A
        · exact (hclassActual q hq).le
        · rw [hclassZero q hq]
      · obtain ⟨q, hq⟩ := hAnonempty
        exact ⟨q, Finset.mem_univ _, hclassActual q hq⟩
    simpa using hsum'
  rw [N.inner_toEuclid_kineticMap_eq_edgeSum, hpartition]
  exact hsum

/-- The Birch-projected mass-action field points strictly inward on every active face of the
scheduled nested domain. -/
theorem borosBirchKineticProjectionField_strict_inward
    (N : Network S) [DecidableEq (Quotient N.linkedSetoid)]
    [Nonempty (Quotient N.linkedSetoid)]
    (hwr : N.WeaklyReversible) (κ : N.RateConstants)
    (x : N.borosBirchParameterSpace → Concentration S)
    (hxpos : ∀ z s, 0 < x z s)
    (hgraph : ∀ z,
      toEuclid (N.complexTransposeMap (fun s => Real.log (x z s))) - z.1 ∈
        N.borosIncidenceEuclidSpace.orthogonal)
    (kmin kmax ε : ℝ) (r : ℕ → ℝ)
    (hkminpos : 0 < kmin) (hkmin : ∀ a, kmin ≤ κ.k a)
    (hkmaxpos : 0 < kmax) (hkmax : ∀ a, κ.k a ≤ kmax)
    (hε : 0 < ε) (hεone : ε ≤ 1) (hr0 : r 0 = 0)
    (hrmono : Monotone r) (hrnonneg : ∀ n, 0 ≤ r n)
    (hεres : ∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
      ∀ i ∈ Q.1, ∀ y,
        y ∈ Analysis.borosResidualSubspace N.borosLinkageProjectionSystem
          N.borosBirchParameterSpace Q.1 {i} →
          ε * ‖y‖ ≤ ‖N.borosLinkageProjectionSystem.project {i} y‖)
    (hrstep : ∀ n, N.borosBoundaryThreshold kmin kmax (r n) <
      ε * Real.sqrt ((r (n + 1) ^ 2 - r n ^ 2) / 2)) :
    ∀ z ∈ Analysis.borosWithinSubspaceNestedDomain
        N.borosLinkageProjectionSystem N.borosBirchParameterSpace r,
      ∀ Q : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
        ‖Analysis.borosWithinSubspaceProjectionFamily
            N.borosLinkageProjectionSystem N.borosBirchParameterSpace Q z‖ =
          Analysis.borosProjectionRadius r Q →
        0 < inner ℝ (N.borosBirchKineticProjectionField κ x z)
          (Analysis.borosWithinSubspaceProjectionFamily
            N.borosLinkageProjectionSystem N.borosBirchParameterSpace Q z) := by
  classical
  let P := N.borosLinkageProjectionSystem
  let H := N.borosBirchParameterSpace
  intro z hz Q hboundary
  let A := Q.1
  let ell := Fintype.card (Quotient N.linkedSetoid)
  let j := ell - A.card
  let pQ := (Analysis.borosLinkageSliceWithin P H A).starProjection z
  let C := Finset.univ \ A
  let pC := (Analysis.borosLinkageSliceWithin P H C).starProjection z
  have hsingleton : ∀ i ∈ A,
      ε * Real.sqrt ((r (j + 1) ^ 2 - r j ^ 2) / 2) ≤
        ‖P.project {i} pQ.1‖ := by
    intro i hi
    simpa [P, H, A, ell, j, pQ] using
      borosActiveFaceSingletonProjection_lower P H r hr0 hrmono hrnonneg Q i hi z hz
        hboundary hε hεone (hεres Q i hi)
  let Qtop : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid) :=
    ⟨Finset.univ, by simp⟩
  have htopmap : Analysis.borosWithinSubspaceProjectionFamily P H Qtop =
      ContinuousLinearMap.id ℝ H := by
    simpa [Qtop] using Analysis.borosWithinSubspaceProjectionFamily_univ P H
  have htopradius : Analysis.borosProjectionRadius r Qtop = r ell := by
    simpa [Qtop, ell] using
      Analysis.borosProjectionRadius_univ r hr0 (hrnonneg ell)
  have hzconstraints := hz
  change ∀ B : Analysis.BorosSubsetIndex (Quotient N.linkedSetoid),
    ‖Analysis.borosWithinSubspaceProjectionFamily P H B z‖ ≤
      Analysis.borosProjectionRadius r B at hzconstraints
  have houter : ‖z.1‖ ≤ r ell := by
    have h := hzconstraints Qtop
    rw [htopmap, ContinuousLinearMap.id_apply, htopradius] at h
    simpa using h
  have hactive : ‖pQ‖ = Analysis.borosProjectionRadius r Q := by
    simpa [pQ, P, H, A, Analysis.borosWithinSubspaceProjectionFamily] using hboundary
  have hradQ := Analysis.borosProjectionRadius_radicand_nonneg r hrmono hrnonneg Q
  have hactiveSq : ‖pQ.1‖ ^ 2 = (r ell) ^ 2 - (r j) ^ 2 := by
    calc
      ‖pQ.1‖ ^ 2 = ‖pQ‖ ^ 2 := by simp
      _ = Analysis.borosProjectionRadius r Q ^ 2 := congrArg (fun v : ℝ => v ^ 2) hactive
      _ = (r ell) ^ 2 - (r j) ^ 2 := by
        simpa [Analysis.borosProjectionRadius, ell, j] using Real.sq_sqrt hradQ
  obtain ⟨y, hdecomp, hyres, horthQ, horthC, hcross⟩ :=
    Analysis.borosWithinProjection_decompose P H (Finset.subset_univ A) z
  have htop :
      (Analysis.borosLinkageSliceWithin P H Finset.univ).starProjection z = z := by
    change Analysis.borosWithinSubspaceProjectionFamily P H Qtop z = z
    rw [htopmap, ContinuousLinearMap.id_apply]
  have hdecompSubtype : z = pQ + pC + y := by
    calc
      z = (Analysis.borosLinkageSliceWithin P H Finset.univ).starProjection z := htop.symm
      _ = pQ + pC + y := by simpa [pQ, pC, P, H, A, C] using hdecomp
  have hdecompAmbient : z.1 = pQ.1 + pC.1 + y.1 := by
    exact congrArg Subtype.val hdecompSubtype
  have hcross' : inner ℝ pQ.1 pC.1 = 0 := by
    simpa [pQ, pC, P, H, A, C] using hcross
  have horthQ' : inner ℝ pQ.1 y.1 = 0 := by
    simpa [pQ, P, H, A] using horthQ
  have horthC' : inner ℝ pC.1 y.1 = 0 := by
    simpa [pC, P, H, C] using horthC
  have hsumOrth : inner ℝ (pQ.1 + pC.1) y.1 = 0 := by
    rw [inner_add_left, horthQ', horthC', zero_add]
  have hnormDecomp :
      ‖z.1‖ ^ 2 = ‖pQ.1‖ ^ 2 + ‖pC.1‖ ^ 2 + ‖y.1‖ ^ 2 := by
    rw [hdecompAmbient, norm_add_sq_real, hsumOrth, norm_add_sq_real, hcross']
    ring
  have houterSq : ‖z.1‖ ^ 2 ≤ (r ell) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (hrnonneg ell)).2 (by simpa using houter)
  have hySq : ‖y.1‖ ^ 2 ≤ (r j) ^ 2 := by
    nlinarith [hnormDecomp, houterSq, hactiveSq, sq_nonneg ‖pC.1‖]
  have hybound : ‖y.1‖ ≤ r j :=
    (sq_le_sq₀ (norm_nonneg _) (hrnonneg j)).mp hySq
  let u : N.ComplexIdx → ℝ := toEuclid.symm pQ.1
  let w : N.ComplexIdx → ℝ := toEuclid.symm y.1
  have hwp : toEuclid w = y.1 := by simp [w]
  have hwbound : ∀ c, |w c| ≤ r j := by
    intro c
    have hcoord : ‖w c‖ ≤ ‖y.1‖ := by
      calc
        ‖w c‖ = ‖(toEuclid w) c‖ := by simp
        _ = ‖y.1 c‖ := by rw [hwp]
        _ ≤ ‖y.1‖ := PiLp.norm_apply_le y.1 c
    have hcoord' : |w c| ≤ ‖y.1‖ := by simpa [Real.norm_eq_abs] using hcoord
    exact hcoord'.trans hybound
  have hpQslice : pQ.1 ∈ Analysis.borosLinkageSlice P H A := by
    change pQ.1 ∈ Analysis.borosLinkageSlice P H A
    exact (Analysis.borosLinkageSliceWithin P H A).starProjection_apply_mem z
  have hpCslice : pC.1 ∈ Analysis.borosLinkageSlice P H C := by
    change pC.1 ∈ Analysis.borosLinkageSlice P H C
    exact (Analysis.borosLinkageSliceWithin P H C).starProjection_apply_mem z
  have hpQfix : P.project A pQ.1 = pQ.1 :=
    P.project_eq_self_of_mem_supported hpQslice.2
  have hpCfix : P.project C pC.1 = pC.1 :=
    P.project_eq_self_of_mem_supported hpCslice.2
  have huzero : ∀ c, N.classOf c ∉ A → u c = 0 := by
    intro c hc
    have hc0 : pQ.1 c = 0 := by
      have heq := congrArg (fun v : EuclideanSpace ℝ N.ComplexIdx => v c) hpQfix
      rw [N.borosLinkageProjectionSystem_apply] at heq
      simpa [hc] using heq.symm
    change (toEuclid.symm pQ.1) c = 0
    simpa [toEuclid] using hc0
  have hpCzero : ∀ c, N.classOf c ∈ A → pC.1 c = 0 := by
    intro c hc
    have hnot : N.classOf c ∉ C := by simp [C, hc]
    have hc0 : pC.1 c = 0 := by
      have heq := congrArg (fun v : EuclideanSpace ℝ N.ComplexIdx => v c) hpCfix
      rw [N.borosLinkageProjectionSystem_apply] at heq
      simpa [hnot] using heq.symm
    exact hc0
  have huIncEuclid : toEuclid u ∈ N.borosIncidenceEuclidSpace := by
    rw [show toEuclid u = pQ.1 by simp [u]]
    exact N.borosBirchParameterSpace_le_borosIncidenceEuclidSpace pQ.2
  have huInc : u ∈ LinearMap.range N.incidenceMap := by
    rcases LinearMap.mem_range.mp huIncEuclid with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    apply toEuclid.injective
    change toEuclid (N.incidenceMap v) = toEuclid u at hv
    exact hv
  have hzero : ∀ q, q ∈ A →
      ∑ c : {c : N.ComplexIdx // N.classOf c = q}, u c.val = 0 := by
    intro q hq
    rw [N.sum_classCoordinates_eq_sum_restrictToClass]
    exact N.sum_restrictToClass_eq_zero_of_mem_range_incidenceMap huInc q
  let monomial := N.complexMonomialVector (x z)
  let logField := N.complexTransposeMap (fun s => Real.log (x z s))
  let f : N.ComplexIdx → ℝ := fun c => logField c - z.1 c
  have hforth : toEuclid f ∈ N.borosIncidenceEuclidSpace.orthogonal := by
    have h := hgraph z
    change toEuclid f ∈ N.borosIncidenceEuclidSpace.orthogonal
    convert h using 1
    apply PiLp.ext
    intro c
    simp [f, logField]
  let representative : ∀ q : Quotient N.linkedSetoid, N.BorosClassReaction q :=
    fun q => Classical.choice (N.borosClassReaction_nonempty hwr q)
  let alpha : Quotient N.linkedSetoid → ℝ := fun q =>
    f (N.sourceIdx (representative q).val)
  have hfspec : ∀ c, f c = alpha (N.classOf c) := by
    intro c
    dsimp [alpha]
    exact N.borosIncidenceOrthogonal_eq_on_linkageClass hforth
      (representative (N.classOf c)).property.symm
  have hdecompCoord : ∀ c,
      z.1 c = pQ.1 c + pC.1 c + y.1 c := by
    intro c
    exact congrArg (fun v : EuclideanSpace ℝ N.ComplexIdx => v c)
      hdecompAmbient
  have hmonomial : ∀ q, q ∈ A → ∀ c, N.classOf c = q →
      monomial c = Real.exp (u c + w c + alpha q) := by
    intro q hq c hc
    change N.complexMonomialVector (x z) c = Real.exp (u c + w c + alpha q)
    rw [N.complexMonomialVector_eq_exp_complexTranspose_log (hxpos z)]
    change Real.exp (logField c) = Real.exp (u c + w c + alpha q)
    rw [show logField c = z.1 c + f c by dsimp [f, logField]; ring, hfspec c, hc]
    have hpC := hpCzero c (by rw [hc]; exact hq)
    have hu : u c = pQ.1 c := by rfl
    have hw : w c = y.1 c := by rfl
    rw [hdecompCoord c, hpC, hu, hw]
    congr 1
    ring
  have hrho : 0 ≤ r j := hrnonneg j
  let budget := N.borosClassBudget kmin kmax (r j)
  let threshold := Analysis.borosWeightedPathBound budget
    N.borosUniformReactionPathLength + 1
  have hbudgetPos : 0 < budget :=
    N.borosClassBudget_pos hkminpos hkmaxpos
  have hpathNonneg := borosWeightedPathBound_nonneg hbudgetPos.le
    N.borosUniformReactionPathLength
  have hthresholdPos : 0 < threshold := by
    dsimp [threshold]
    linarith
  have hthreshold : Analysis.borosWeightedPathBound budget
      N.borosUniformReactionPathLength < threshold := by
    dsimp [threshold]
    linarith
  have hactiveNormLarge : ∀ q, q ∈ A →
      N.borosBoundaryThreshold kmin kmax (r j) <
        ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => u c.val)‖ := by
    intro q hq
    have hcomponent := hsingleton q hq
    have hrlarge := hrstep j
    have huEuclid : toEuclid u = pQ.1 := by simp [u]
    have hnormEq := N.norm_toEuclid_classCoordinates_eq_projection_norm q u
    rw [huEuclid] at hnormEq
    calc
      N.borosBoundaryThreshold kmin kmax (r j) <
          ε * Real.sqrt ((r (j + 1) ^ 2 - r j ^ 2) / 2) := hrlarge
      _ ≤ ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => u c.val)‖ := by
        rw [hnormEq]
        exact hcomponent
  have hnorm : ∀ q, q ∈ A →
      (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) ^ 2 * threshold <
        ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => u c.val)‖ := by
    intro q hq
    have hlarge := hactiveNormLarge q hq
    have hNlarge :
        (Fintype.card N.ComplexIdx : ℝ) ^ 2 * threshold <
          ‖toEuclid (fun c : {c : N.ComplexIdx // N.classOf c = q} => u c.val)‖ := by
      have hthresholdEq : N.borosBoundaryThreshold kmin kmax (r j) =
          (Fintype.card N.ComplexIdx : ℝ) ^ 2 * threshold := by
        simp [borosBoundaryThreshold, threshold, budget, pow_two]
      rw [hthresholdEq] at hlarge
      exact hlarge
    have hcardNat : Fintype.card {c : N.ComplexIdx // N.classOf c = q} ≤
        Fintype.card N.ComplexIdx :=
      Fintype.card_le_of_injective Subtype.val (fun _ _ h => Subtype.ext h)
    have hcard : (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) ≤
        (Fintype.card N.ComplexIdx : ℝ) := by exact_mod_cast hcardNat
    have hcard0 : 0 ≤ (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) := by positivity
    have hn0 : 0 ≤ (Fintype.card N.ComplexIdx : ℝ) := by positivity
    have hcardsq :
        (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) ^ 2 ≤
          (Fintype.card N.ComplexIdx : ℝ) ^ 2 := by
      have hmul := mul_le_mul hcard hcard hcard0 hn0
      simpa only [pow_two] using hmul
    have hle := mul_le_mul_of_nonneg_right hcardsq hthresholdPos.le
    have hle' :
        (Fintype.card {c : N.ComplexIdx // N.classOf c = q} : ℝ) ^ 2 * threshold ≤
          (Fintype.card N.ComplexIdx : ℝ) ^ 2 * threshold := by
      simpa only [pow_two] using hle
    exact lt_of_le_of_lt hle' hNlarge
  have hclassBudget : ∀ q,
      (Fintype.card (N.BorosClassReaction q) : ℝ) *
          (kmax * Real.exp (r j)) <
        (kmin * Real.exp (-r j)) * budget := by
    intro q
    exact N.borosClassBudget_dominates_each_class q hkminpos hkmaxpos
  have hkineticPairing := N.borosKineticPairing_neg_of_activeClasses
    hwr κ A Q.2 hkminpos hkmin hkmaxpos hkmax hbudgetPos.le hclassBudget u w alpha monomial
    hwbound huzero hzero hnorm hmonomial hthreshold
  let K := toEuclid (N.kineticMap κ monomial)
  have hprojectPair :
      inner ℝ (H.orthogonalProjectionOnto K) pQ = inner ℝ K pQ.1 :=
    H.inner_orthogonalProjectionOnto_eq_of_mem_right pQ K
  have hKnegative : inner ℝ K pQ.1 < 0 := by
    simpa [K, u] using hkineticPairing
  change 0 < inner ℝ (-H.orthogonalProjectionOnto K) pQ
  rw [inner_neg_left, hprojectPair]
  exact neg_pos.mpr hKnegative

end Network
end CRNT
