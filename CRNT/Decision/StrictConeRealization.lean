import CRNT.Dynamics.SiphonAutocatalysis
import CRNT.Decision.CriticalSiphonDecide
import CRNT.LinearAlgebra.RationalDenominator
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Ring.Rat

/-!
# Strict rational/integer realization of CRNT flux cones

The drainable/self-replicable definitions are combinatorial: they ask for a finite reaction
pathway.  Linear-algebra proofs naturally produce a nonnegative real reaction flux.  This module
closes that representation gap for finite CRNs with integer stoichiometry.

The proof deliberately reuses `RationalFarkas.feasibleℝ_iff_feasible`, already proved in the
critical-siphon decision layer:

1. a strict real witness is rescaled so every requested signed output has margin at least `1`;
2. nonnegativity and those margin inequalities form a rational **non-strict** system;
3. real feasibility therefore gives a rational nonnegative flux with the same unit margin;
4. multiplying by the product of all rational denominators gives natural reaction
   multiplicities; and
5. `isSelfReplicable_iff_naturalFlux` / `isDrainable_iff_naturalFlux` turn those multiplicities
   into executable finite pathways.

Thus `Network.FluxSignRealizable` is not an additional CRNT hypothesis.
-/

open scoped BigOperators

namespace CRNT
namespace RationalFarkas

/-- Rational left-hand value of an encoded row, reindexed through the finite equivalence. -/
theorem lhs_encodeRow {A : Type} [DecidableEq A] [Fintype A]
    (e : A ≃ Fin (Fintype.card A)) (c : A → ℚ) (b : ℚ)
    (x : Fin (Fintype.card A) → ℚ) :
    (Network.encodeRow e c b).lhs x = ∑ a : A, c a * x (e a) := by
  rw [Ineq.lhs, Network.encodeRow]
  rw [← Equiv.sum_comp e (fun i => c (e.symm i) * x i)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Equiv.symm_apply_apply]

end RationalFarkas

namespace Network

open RationalFarkas

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## Rational feasibility systems for signed reaction fluxes -/

/-- Nonnegative rational reaction flux with unit *positive* output margin on `P`. -/
noncomputable def positiveFluxSystem (N : Network S) (eR : N.R ≃ Fin (Fintype.card N.R))
    (P : Finset S) : List (Ineq (Fintype.card N.R)) :=
  ((enumOfEquiv eR).map fun r : N.R =>
      encodeRow eR (fun q => if q = r then -1 else 0) 0) ++
  P.toList.map (fun s =>
      encodeRow eR (fun r => -(N.reactionCoeffQ r s)) (-1))

/-- Nonnegative rational reaction flux with unit *negative* output margin on `P`. -/
noncomputable def negativeFluxSystem (N : Network S) (eR : N.R ≃ Fin (Fintype.card N.R))
    (P : Finset S) : List (Ineq (Fintype.card N.R)) :=
  ((enumOfEquiv eR).map fun r : N.R =>
      encodeRow eR (fun q => if q = r then -1 else 0) 0) ++
  P.toList.map (fun s =>
      encodeRow eR (fun r => N.reactionCoeffQ r s) (-1))

/-- Computable positive-margin encoding with explicit species and reaction enumerations. -/
def positiveFluxSystemOfEquiv (N : Network S) (eS : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) : List (Ineq (Fintype.card N.R)) :=
  ((enumOfEquiv eR).map fun r : N.R =>
      encodeRow eR (fun q => if q = r then -1 else 0) 0) ++
  ((enumOfEquiv eS).filter (fun s => decide (s ∈ P))).map (fun s =>
      encodeRow eR (fun r => -(N.reactionCoeffQ r s)) (-1))

/-- Computable negative-margin encoding with explicit species and reaction enumerations. -/
def negativeFluxSystemOfEquiv (N : Network S) (eS : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) : List (Ineq (Fintype.card N.R)) :=
  ((enumOfEquiv eR).map fun r : N.R =>
      encodeRow eR (fun q => if q = r then -1 else 0) 0) ++
  ((enumOfEquiv eS).filter (fun s => decide (s ∈ P))).map (fun s =>
      encodeRow eR (fun r => N.reactionCoeffQ r s) (-1))

theorem mem_positiveFluxSystemOfEquiv (N : Network S) (eS : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) (I : Ineq (Fintype.card N.R)) :
    I ∈ N.positiveFluxSystemOfEquiv eS eR P ↔ I ∈ N.positiveFluxSystem eR P := by
  simp only [positiveFluxSystemOfEquiv, positiveFluxSystem, List.mem_append, List.mem_map,
    List.mem_filter, mem_enumOfEquiv, decide_eq_true_eq, true_and, Finset.mem_toList]

theorem mem_negativeFluxSystemOfEquiv (N : Network S) (eS : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) (I : Ineq (Fintype.card N.R)) :
    I ∈ N.negativeFluxSystemOfEquiv eS eR P ↔ I ∈ N.negativeFluxSystem eR P := by
  simp only [negativeFluxSystemOfEquiv, negativeFluxSystem, List.mem_append, List.mem_map,
    List.mem_filter, mem_enumOfEquiv, decide_eq_true_eq, true_and, Finset.mem_toList]

theorem feasible_positiveFluxSystemOfEquiv_iff (N : Network S) (eS : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) :
    Feasible (N.positiveFluxSystemOfEquiv eS eR P) ↔ Feasible (N.positiveFluxSystem eR P) := by
  simp only [Feasible, Sat, mem_positiveFluxSystemOfEquiv]

theorem feasible_negativeFluxSystemOfEquiv_iff (N : Network S) (eS : S ≃ Fin (Fintype.card S))
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) :
    Feasible (N.negativeFluxSystemOfEquiv eS eR P) ↔ Feasible (N.negativeFluxSystem eR P) := by
  simp only [Feasible, Sat, mem_negativeFluxSystemOfEquiv]

/-- Scaling a strict positive flux witness gives a real solution of the unit-margin rational
system. -/
theorem feasibleReal_positiveFluxSystem_of_flux (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S)
    (h : N.IsFluxSelfReplicable P) : Feasibleℝ (N.positiveFluxSystem eR P) := by
  classical
  obtain ⟨v, hvnn, hvpos⟩ := h
  by_cases hP : P = ∅
  · subst P
    refine ⟨fun _ => 0, ?_⟩
    intro I hI
    rw [positiveFluxSystem, List.mem_append] at hI
    rcases hI with hI | hI
    · rw [List.mem_map] at hI
      obtain ⟨r, _hr, rfl⟩ := hI
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      simp
    · simp at hI
  · have hPne : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP
    let C : ℝ := ∑ s ∈ P, (N.fluxNetChange v s)⁻¹
    have hCnonneg : 0 ≤ C := by
      dsimp [C]
      refine Finset.sum_nonneg fun s hs => ?_
      exact inv_nonneg.mpr (le_of_lt (hvpos s hs))
    have hmargin : ∀ s ∈ P, 1 ≤ C * N.fluxNetChange v s := by
      intro s hs
      have hspos := hvpos s hs
      have hinvnonneg : ∀ z ∈ P, 0 ≤ (N.fluxNetChange v z)⁻¹ := by
        intro z hz
        exact (inv_nonneg.mpr (hvpos z hz).le)
      have hsingle : (N.fluxNetChange v s)⁻¹ ≤ C := by
        dsimp [C]
        exact Finset.single_le_sum (fun z hz => hinvnonneg z hz) hs
      have hmul := mul_le_mul_of_nonneg_right hsingle hspos.le
      rw [inv_mul_cancel₀ hspos.ne'] at hmul
      exact hmul
    let u : N.R → ℝ := fun r => C * v r
    have hunn : ∀ r, 0 ≤ u r := fun r => mul_nonneg hCnonneg (hvnn r)
    have hflux : ∀ s, N.fluxNetChange u s = C * N.fluxNetChange v s := by
      intro s
      simp only [fluxNetChange, u, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    refine ⟨fun i => u (eR.symm i), ?_⟩
    intro I hI
    rw [positiveFluxSystem, List.mem_append] at hI
    rcases hI with hI | hI
    · rw [List.mem_map] at hI
      obtain ⟨r, _hr, rfl⟩ := hI
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      simp only [Equiv.symm_apply_apply, encodeRow]
      -- the row is the indicator `-1` at `r`, so the sum collapses to `-u r`
      have key : (∑ x : N.R, ((if x = r then (-1 : ℚ) else 0 : ℚ) : ℝ) * u x) = -u r := by
        rw [Finset.sum_eq_single r]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; simp at h
      rw [key]
      simpa using hunn r
    · rw [List.mem_map] at hI
      obtain ⟨s, hs, rfl⟩ := hI
      have hsP : s ∈ P := by simpa using hs
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      simp only [Equiv.symm_apply_apply, encodeRow, Rat.cast_neg]
      have hsum :
          (∑ r : N.R, (-(N.reactionCoeffQ r s) : ℝ) * u r) =
            -(N.fluxNetChange u s) := by
        rw [fluxNetChange]
        simp_rw [N.cast_reactionCoeffQ]
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hsum, hflux]
      have hm := hmargin s hsP
      norm_num
      linarith

/-- Scaling a strict negative flux witness gives a real solution of the unit negative-margin system. -/
theorem feasibleReal_negativeFluxSystem_of_flux (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S)
    (h : N.IsFluxDrainable P) : Feasibleℝ (N.negativeFluxSystem eR P) := by
  classical
  obtain ⟨v, hvnn, hvneg⟩ := h
  by_cases hP : P = ∅
  · subst P
    refine ⟨fun _ => 0, ?_⟩
    intro I hI
    rw [negativeFluxSystem, List.mem_append] at hI
    rcases hI with hI | hI
    · rw [List.mem_map] at hI
      obtain ⟨r, _hr, rfl⟩ := hI
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      simp
    · simp at hI
  · let C : ℝ := ∑ s ∈ P, (-N.fluxNetChange v s)⁻¹
    have hCnonneg : 0 ≤ C := by
      dsimp [C]
      apply Finset.sum_nonneg
      intro s hs
      exact inv_nonneg.mpr (neg_nonneg.mpr (hvneg s hs).le)
    have hmargin : ∀ s ∈ P, 1 ≤ C * (-N.fluxNetChange v s) := by
      intro s hs
      have hspos : 0 < -N.fluxNetChange v s := neg_pos.mpr (hvneg s hs)
      have hinvnonneg : ∀ z ∈ P, 0 ≤ (-N.fluxNetChange v z)⁻¹ := by
        intro z hz
        exact inv_nonneg.mpr (neg_nonneg.mpr (hvneg z hz).le)
      have hsingle : (-N.fluxNetChange v s)⁻¹ ≤ C := by
        dsimp [C]
        exact Finset.single_le_sum (fun z hz => hinvnonneg z hz) hs
      have hmul := mul_le_mul_of_nonneg_right hsingle hspos.le
      rw [inv_mul_cancel₀ hspos.ne'] at hmul
      exact hmul
    let u : N.R → ℝ := fun r => C * v r
    have hunn : ∀ r, 0 ≤ u r := fun r => mul_nonneg hCnonneg (hvnn r)
    have hflux : ∀ s, N.fluxNetChange u s = C * N.fluxNetChange v s := by
      intro s
      simp only [fluxNetChange, u, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      ring
    refine ⟨fun i => u (eR.symm i), ?_⟩
    intro I hI
    rw [negativeFluxSystem, List.mem_append] at hI
    rcases hI with hI | hI
    · rw [List.mem_map] at hI
      obtain ⟨r, _hr, rfl⟩ := hI
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      simp only [Equiv.symm_apply_apply, encodeRow]
      have key : (∑ x : N.R, ((if x = r then (-1 : ℚ) else 0 : ℚ) : ℝ) * u x) = -u r := by
        rw [Finset.sum_eq_single r]
        · simp
        · intro b _ hb; simp [hb]
        · intro h; simp at h
      rw [key]
      simpa using hunn r
    · rw [List.mem_map] at hI
      obtain ⟨s, hs, rfl⟩ := hI
      have hsP : s ∈ P := by simpa using hs
      rw [Ineq.holdsℝ, lhsℝ_encodeRow]
      simp only [Equiv.symm_apply_apply, encodeRow]
      have hsum :
          (∑ r : N.R, (N.reactionCoeffQ r s : ℝ) * u r) =
            N.fluxNetChange u s := by
        rw [fluxNetChange]
        simp_rw [N.cast_reactionCoeffQ]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hsum, hflux]
      have hm := hmargin s hsP
      norm_num
      linarith

/-- A rational solution of the positive unit-margin system gives natural reaction multiplicities
with strictly positive net change on `P`. -/
theorem naturalFluxSelfReplicable_of_feasible_positive (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S)
    (hQ : Feasible (N.positiveFluxSystem eR P)) : N.IsNaturalFluxSelfReplicable P := by
  classical
  obtain ⟨x, hx⟩ := hQ
  let q : N.R → ℚ := fun r => x (eR r)
  have hqnn : ∀ r, 0 ≤ q r := by
    intro r
    have hrow := hx (encodeRow eR (fun z => if z = r then -1 else 0) 0) (by
      rw [positiveFluxSystem, List.mem_append]
      left
      exact List.mem_map.mpr ⟨r, mem_enumOfEquiv eR r, rfl⟩)
    rw [Ineq.holds, lhs_encodeRow] at hrow
    simpa [q] using hrow
  have hout : ∀ s ∈ P, (1 : ℚ) ≤ ∑ r : N.R, q r * N.reactionCoeffQ r s := by
    intro s hs
    have hrow := hx (encodeRow eR (fun r => -(N.reactionCoeffQ r s)) (-1)) (by
      rw [positiveFluxSystem, List.mem_append]
      right
      exact List.mem_map.mpr ⟨s, by simpa using hs, rfl⟩)
    rw [Ineq.holds, lhs_encodeRow, encodeRow_bound] at hrow
    have : -(∑ r : N.R, q r * N.reactionCoeffQ r s) ≤ (-1 : ℚ) := by
      convert hrow using 1
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro r _
      ring
    linarith
  let D := rationalCommonDenominator q
  let m : N.R → ℕ := clearRationalToNat q
  have hDpos : 0 < D := rationalCommonDenominator_pos q
  refine ⟨m, ?_⟩
  intro s hs
  have houtR : (1 : ℝ) ≤ ∑ r : N.R, (q r : ℝ) * N.reactionVector r s := by
    have hc := hout s hs
    have hcR : (1 : ℝ) ≤
        ∑ r : N.R, ((q r * N.reactionCoeffQ r s : ℚ) : ℝ) := by
      exact_mod_cast hc
    simpa only [Rat.cast_mul, N.cast_reactionCoeffQ] using hcR
  have hscale : N.naturalFluxNetChange m s = (D : ℝ) *
      (∑ r : N.R, (q r : ℝ) * N.reactionVector r s) := by
    rw [naturalFluxNetChange, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hclr := cast_clearRationalToNat q hqnn r
    have hclrR : ((m r : ℕ) : ℝ) = (D : ℝ) * (q r : ℝ) := by
      exact_mod_cast hclr
    rw [hclrR]
    ring
  rw [hscale]
  have hDreal : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  nlinarith

/-- Rational negative unit-margin feasibility analog. -/
theorem naturalFluxDrainable_of_feasible_negative (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S)
    (hQ : Feasible (N.negativeFluxSystem eR P)) : N.IsNaturalFluxDrainable P := by
  classical
  obtain ⟨x, hx⟩ := hQ
  let q : N.R → ℚ := fun r => x (eR r)
  have hqnn : ∀ r, 0 ≤ q r := by
    intro r
    have hrow := hx (encodeRow eR (fun z => if z = r then -1 else 0) 0) (by
      rw [negativeFluxSystem, List.mem_append]
      left
      exact List.mem_map.mpr ⟨r, mem_enumOfEquiv eR r, rfl⟩)
    rw [Ineq.holds, lhs_encodeRow] at hrow
    simpa [q] using hrow
  have hout : ∀ s ∈ P, (∑ r : N.R, q r * N.reactionCoeffQ r s) ≤ (-1 : ℚ) := by
    intro s hs
    have hrow := hx (encodeRow eR (fun r => N.reactionCoeffQ r s) (-1)) (by
      rw [negativeFluxSystem, List.mem_append]
      right
      exact List.mem_map.mpr ⟨s, by simpa using hs, rfl⟩)
    rw [Ineq.holds, lhs_encodeRow, encodeRow_bound] at hrow
    simpa [mul_comm] using hrow
  let D := rationalCommonDenominator q
  let m : N.R → ℕ := clearRationalToNat q
  have hDpos : 0 < D := rationalCommonDenominator_pos q
  refine ⟨m, ?_⟩
  intro s hs
  have houtR : (∑ r : N.R, (q r : ℝ) * N.reactionVector r s) ≤ (-1 : ℝ) := by
    have hc := hout s hs
    have hcR : (∑ r : N.R, ((q r * N.reactionCoeffQ r s : ℚ) : ℝ)) ≤ (-1 : ℝ) := by
      exact_mod_cast hc
    simpa only [Rat.cast_mul, N.cast_reactionCoeffQ] using hcR
  have hscale : N.naturalFluxNetChange m s = (D : ℝ) *
      (∑ r : N.R, (q r : ℝ) * N.reactionVector r s) := by
    rw [naturalFluxNetChange, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    have hclr := cast_clearRationalToNat q hqnn r
    have hclrR : ((m r : ℕ) : ℝ) = (D : ℝ) * (q r : ℝ) := by
      exact_mod_cast hclr
    rw [hclrR]
    ring
  rw [hscale]
  have hDreal : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hDpos
  nlinarith

/-- **Strict real self-replication fluxes are always executable finite pathways.** -/
theorem isSelfReplicable_of_flux (N : Network S) (P : Finset S)
    (h : N.IsFluxSelfReplicable P) : N.IsSelfReplicable P := by
  classical
  let eR := Fintype.equivFin N.R
  have hR : Feasibleℝ (N.positiveFluxSystem eR P) :=
    N.feasibleReal_positiveFluxSystem_of_flux eR P h
  have hQ : Feasible (N.positiveFluxSystem eR P) :=
    (feasibleℝ_iff_feasible (N.positiveFluxSystem eR P)).mp hR
  exact (N.isSelfReplicable_iff_naturalFlux P).2
    (N.naturalFluxSelfReplicable_of_feasible_positive eR P hQ)

/-- **Strict real drainability fluxes are always executable finite pathways.** -/
theorem isDrainable_of_flux (N : Network S) (P : Finset S)
    (h : N.IsFluxDrainable P) : N.IsDrainable P := by
  classical
  let eR := Fintype.equivFin N.R
  have hR : Feasibleℝ (N.negativeFluxSystem eR P) :=
    N.feasibleReal_negativeFluxSystem_of_flux eR P h
  have hQ : Feasible (N.negativeFluxSystem eR P) :=
    (feasibleℝ_iff_feasible (N.negativeFluxSystem eR P)).mp hR
  exact (N.isDrainable_iff_naturalFlux P).2
    (N.naturalFluxDrainable_of_feasible_negative eR P hQ)

/-- **Flux-sign realization is unconditional for finite CRNs with natural complexes.** -/
theorem fluxSignRealizable (N : Network S) : N.FluxSignRealizable :=
  ⟨fun P => N.isSelfReplicable_of_flux P, fun P => N.isDrainable_of_flux P⟩

/-! ## Unconditional pathway-level consequences

The older structural lemmas in `SiphonAutocatalysis` keep `FluxSignRealizable` explicit so that
that lower-level module does not import the rational decision stack.  From this module upward the
realization theorem is discharged once and for all.
-/

/-- On any consistent finite CRN, self-replicability implies drainability with no extra
realization hypothesis. -/
theorem IsSelfReplicable.toDrainable_of_consistent' {N : Network S} {P : Finset S}
    (hcons : N.IsConsistent) (h : N.IsSelfReplicable P) : N.IsDrainable P :=
  h.toDrainable_of_consistent N.fluxSignRealizable hcons

/-- Weakly reversible specialization of unconditional sign reversal. -/
theorem IsSelfReplicable.toDrainable_of_weaklyReversible' {N : Network S} {P : Finset S}
    (hwr : N.WeaklyReversible) (h : N.IsSelfReplicable P) : N.IsDrainable P :=
  h.toDrainable_of_weaklyReversible N.fluxSignRealizable hwr

/-- Drainability and self-replicability coincide on consistent finite CRNs. -/
theorem selfReplicable_iff_drainable_of_consistent' (N : Network S)
    (hcons : N.IsConsistent) (P : Finset S) :
    N.IsSelfReplicable P ↔ N.IsDrainable P :=
  N.selfReplicable_iff_drainable_of_consistent N.fluxSignRealizable hcons P

/-- Drainability and self-replicability coincide on weakly reversible finite CRNs. -/
theorem selfReplicable_iff_drainable_of_weaklyReversible' (N : Network S)
    (hwr : N.WeaklyReversible) (P : Finset S) :
    N.IsSelfReplicable P ↔ N.IsDrainable P :=
  N.selfReplicable_iff_drainable_of_weaklyReversible N.fluxSignRealizable hwr P

/-- Non-autocatalytic siphons in a weakly reversible finite CRN imply absence of drainable
siphons, with strict-flux realization discharged internally. -/
theorem hasNoDrainableSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon'
    (N : Network S) (hwr : N.WeaklyReversible)
    (hnosr : N.HasNoSelfReplicableSiphon) : N.HasNoDrainableSiphon :=
  N.hasNoDrainableSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon
    N.fluxSignRealizable hwr hnosr

/-- Minimal-critical dichotomy + weak reversibility + no drainable siphon excludes all critical
siphons, with rational/integer realization now automatic. -/
theorem hasNoCriticalSiphon_of_weaklyReversible_noDrainable_of_minimalCriticalDichotomy'
    (N : Network S) (hwr : N.WeaklyReversible)
    (hdich : N.MinimalCriticalSiphonDichotomy) (hnd : N.HasNoDrainableSiphon) :
    N.HasNoCriticalSiphon :=
  N.hasNoCriticalSiphon_of_weaklyReversible_noDrainable_of_minimalCriticalDichotomy
    N.fluxSignRealizable hwr hdich hnd

/-- Minimal-critical dichotomy + weak reversibility + non-autocatalyticity excludes all critical
siphons unconditionally at the flux-realization layer. -/
theorem hasNoCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon'
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) :
    N.HasNoCriticalSiphon :=
  N.hasNoCriticalSiphon_of_weaklyReversible_hasNoSelfReplicableSiphon
    N.fluxSignRealizable hdich hwr hnosr

/-- Dual no-drainable version. -/
theorem hasNoCriticalSiphon_of_weaklyReversible_hasNoDrainableSiphon'
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnd : N.HasNoDrainableSiphon) :
    N.HasNoCriticalSiphon :=
  N.hasNoCriticalSiphon_of_weaklyReversible_hasNoDrainableSiphon
    N.fluxSignRealizable hdich hwr hnd

/-- Global omega-limit boundary exclusion for the non-autocatalytic weakly reversible class,
conditional only on the genuine minimal-critical-siphon dichotomy. -/
theorem structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoSelfReplicableSiphon'
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnosr : N.HasNoSelfReplicableSiphon) :
    N.StructurallyBoundaryOmegaExcluded :=
  N.structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoSelfReplicableSiphon
    N.fluxSignRealizable hdich hwr hnosr

/-- Dual no-drainable omega-exclusion theorem. -/
theorem structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoDrainableSiphon'
    (N : Network S) (hdich : N.MinimalCriticalSiphonDichotomy)
    (hwr : N.WeaklyReversible) (hnd : N.HasNoDrainableSiphon) :
    N.StructurallyBoundaryOmegaExcluded :=
  N.structurallyBoundaryOmegaExcluded_of_weaklyReversible_hasNoDrainableSiphon
    N.fluxSignRealizable hdich hwr hnd

/-! ## Exact decidability of pathway sign properties

The same rational systems now give an exact decision procedure for the *combinatorial* pathway
notions, not merely the real-flux relaxations.  This is useful independently of the universal
minimal-critical-siphon theorem: a concrete finite network can mechanically prove that every one
of its minimal critical siphons satisfies the drainable/self-replicable alternative.
-/

/-- Self-replicability is exactly rational feasibility of the positive unit-margin flux system. -/
theorem isSelfReplicable_iff_feasible_positiveFluxSystem (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) :
    N.IsSelfReplicable P ↔ Feasible (N.positiveFluxSystem eR P) := by
  constructor
  · intro h
    have hR : Feasibleℝ (N.positiveFluxSystem eR P) :=
      N.feasibleReal_positiveFluxSystem_of_flux eR P h.toFlux
    exact (feasibleℝ_iff_feasible (N.positiveFluxSystem eR P)).mp hR
  · intro hQ
    exact (N.isSelfReplicable_iff_naturalFlux P).2
      (N.naturalFluxSelfReplicable_of_feasible_positive eR P hQ)

/-- Drainability is exactly rational feasibility of the negative unit-margin flux system. -/
theorem isDrainable_iff_feasible_negativeFluxSystem (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) :
    N.IsDrainable P ↔ Feasible (N.negativeFluxSystem eR P) := by
  constructor
  · intro h
    have hR : Feasibleℝ (N.negativeFluxSystem eR P) :=
      N.feasibleReal_negativeFluxSystem_of_flux eR P h.toFlux
    exact (feasibleℝ_iff_feasible (N.negativeFluxSystem eR P)).mp hR
  · intro hQ
    exact (N.isDrainable_iff_naturalFlux P).2
      (N.naturalFluxDrainable_of_feasible_negative eR P hQ)

/-- Exact self-replicability decision using an explicit reaction enumeration. -/
def decidableIsSelfReplicableOfEquiv (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) : Decidable (N.IsSelfReplicable P) :=
  Trunc.recOnSubsingleton (Fintype.truncEquivFin S) fun eS =>
    decidable_of_iff (Feasible (N.positiveFluxSystemOfEquiv eS eR P))
      ((N.feasible_positiveFluxSystemOfEquiv_iff eS eR P).trans
        (N.isSelfReplicable_iff_feasible_positiveFluxSystem eR P).symm)

/-- Exact drainability decision using an explicit reaction enumeration. -/
def decidableIsDrainableOfEquiv (N : Network S)
    (eR : N.R ≃ Fin (Fintype.card N.R)) (P : Finset S) : Decidable (N.IsDrainable P) :=
  Trunc.recOnSubsingleton (Fintype.truncEquivFin S) fun eS =>
    decidable_of_iff (Feasible (N.negativeFluxSystemOfEquiv eS eR P))
      ((N.feasible_negativeFluxSystemOfEquiv_iff eS eR P).trans
        (N.isDrainable_iff_feasible_negativeFluxSystem eR P).symm)

/-- Finite pathway self-replicability is decidable. -/
instance decidableIsSelfReplicable (N : Network S) (P : Finset S) :
    Decidable (N.IsSelfReplicable P) :=
  Trunc.recOnSubsingleton (Fintype.truncEquivFin N.R) fun eR =>
    N.decidableIsSelfReplicableOfEquiv eR P

/-- Finite pathway drainability is decidable. -/
instance decidableIsDrainable (N : Network S) (P : Finset S) :
    Decidable (N.IsDrainable P) :=
  Trunc.recOnSubsingleton (Fintype.truncEquivFin N.R) fun eR =>
    N.decidableIsDrainableOfEquiv eR P

instance decidableIsSelfReplicableSiphon (N : Network S) (P : Finset S) :
    Decidable (N.IsSelfReplicableSiphon P) := by
  unfold IsSelfReplicableSiphon
  infer_instance

instance decidableIsDrainableSiphon (N : Network S) (P : Finset S) :
    Decidable (N.IsDrainableSiphon P) := by
  unfold IsDrainableSiphon
  infer_instance

instance decidableHasNoSelfReplicableSiphon (N : Network S) :
    Decidable (N.HasNoSelfReplicableSiphon) := by
  unfold HasNoSelfReplicableSiphon
  infer_instance

instance decidableHasNoDrainableSiphon (N : Network S) :
    Decidable (N.HasNoDrainableSiphon) := by
  unfold HasNoDrainableSiphon
  infer_instance

instance decidableIsMinimalCriticalSiphon (N : Network S) (P : Finset S) :
    Decidable (N.IsMinimalCriticalSiphon P) := by
  unfold IsMinimalCriticalSiphon
  infer_instance

/-- The Deshpande--Gopalkrishnan alternative is a decidable finite proposition on each concrete
network even before its universal theorem is formalized. -/
instance decidableMinimalCriticalSiphonDichotomy (N : Network S) :
    Decidable (N.MinimalCriticalSiphonDichotomy) := by
  unfold MinimalCriticalSiphonDichotomy
  infer_instance

/-- Flux-form minimal-critical dichotomy is likewise decidable. -/
instance decidableMinimalCriticalSiphonFluxDichotomy (N : Network S) :
    Decidable (N.MinimalCriticalSiphonFluxDichotomy) := by
  -- Use the already equivalent finite pathway proposition instead of attempting to decide
  -- existential real functions directly.
  exact decidable_of_iff (N.MinimalCriticalSiphonDichotomy)
    ⟨fun h P hmin => by
        rcases h P hmin with hd | hs
        · exact Or.inl hd.toFlux
        · exact Or.inr hs.toFlux,
      fun h P hmin => by
        rcases h P hmin with hd | hs
        · exact Or.inl (N.isDrainable_of_flux P hd)
        · exact Or.inr (N.isSelfReplicable_of_flux P hs)⟩

end Network
end CRNT
