import CRNT.Oscillation.GlobalHopfContinuation
import CRNT.Oscillation.SpectralOpenness

/-!
# Spectral-crossing decomposition of the global-Hopf frontier

A smooth equilibrium continuation whose Jacobian starts Hurwitz stable, ends with an eigenvalue in
the open right half-plane, and is nonsingular throughout cannot lose stability through a zero real
eigenvalue.  The finite-dimensional spectral-continuation part of global Hopf should therefore
produce a parameter carrying a nonzero purely imaginary conjugate pair.

This file makes that matrix-theoretic step explicit.  The subsequent global-bifurcation theorem is
kept separate: a spectral crossing is local linear data; a periodic orbit still requires a Hopf or
global-continuation theorem.
-/

namespace CRNT

/-- A nonzero purely imaginary eigenvalue witness for a real continuation Jacobian. -/
structure ImaginarySpectrumWitness
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Type where
  parameter : ℝ
  omega : ℝ
  omega_ne_zero : omega ≠ 0
  isEigenvalue :
    Module.End.HasEigenvalue
      (Matrix.toLin' ((C.jacobian parameter).map (algebraMap ℝ ℂ)))
      (Complex.I * omega)

/-- Purely finite-dimensional spectral frontier: stability changes without a zero eigenvalue force
some nonzero imaginary-axis spectrum along the path. -/
def StabilityChangeImaginaryCrossingTarget : Prop :=
  ∀ (I : Type) [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I),
    Nonempty (ImaginarySpectrumWitness C)

/-- Local-Hopf data obtained after the spectral crossing has been found.  Transversality and the
usual nondegeneracy coefficient are deliberately explicit: neither follows from the existence of a
purely imaginary pair alone. -/
structure LocalHopfContinuationWitness
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) extends ImaginarySpectrumWitness C where
  /-- The selected pair crosses the imaginary axis rather than merely touching it. -/
  transverseCrossing : Prop
  /-- Nonzero first Lyapunov coefficient / equivalent local Hopf nondegeneracy datum. -/
  nonlinearNondegenerate : Prop
  transverseCrossing_proof : transverseCrossing
  nonlinearNondegenerate_proof : nonlinearNondegenerate

/-- The remaining local nonlinear theorem after spectral crossing and nondegeneracy have been
certified.  It returns a periodic trajectory of the same continuation near the crossing. -/
def LocalHopfContinuationTarget : Prop :=
  ∀ (I : Type) [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I)
    (H : LocalHopfContinuationWitness C),
    Nonempty (PositiveContinuationPeriodicWitness C)

/-- Decomposition of the generic global-Hopf target into (i) a spectral crossing theorem, (ii)
problem-specific crossing/nonlinear nondegeneracy certification, and (iii) local Hopf.  This record
is useful when a concrete CRN has enough symbolic information to avoid the full global theorem. -/
structure CertifiedLocalHopfRoute
    {I : Type} [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) : Type where
  witness : LocalHopfContinuationWitness C

/-- Consume a certified local-Hopf route. -/
theorem CertifiedLocalHopfRoute.periodicWitness
    {I : Type} [DecidableEq I] [Fintype I]
    {C : SmoothEquilibriumContinuation I}
    (hHopf : LocalHopfContinuationTarget)
    (H : CertifiedLocalHopfRoute C) :
    Nonempty (PositiveContinuationPeriodicWitness C) :=
  hHopf I C H.witness

end CRNT

namespace CRNT

open Set Filter Topology

namespace Matrix

variable {I : Type} [DecidableEq I] [Fintype I]

/-- If a nonempty real matrix is neither Hurwitz nor strictly unstable, it has spectrum on the
imaginary axis. -/
theorem exists_imaginary_axis_eigenvalue_of_not_hurwitz_not_unstable
    (M : Matrix I I ℝ)
    (_hne : Nonempty I)
    (hnotH : ¬ M.IsHurwitzReal)
    (hnotU : ¬ M.HasUnstableEigenvalue) :
    ∃ z : ℂ,
      z ∈ (M.map (algebraMap ℝ ℂ)).charpoly.roots ∧ z.re = 0 := by
  classical
  by_contra haxis
  push_neg at haxis
  apply hnotH
  intro z hz
  have hzle : z.re ≤ 0 := by
    apply le_of_not_gt
    intro hzpos
    exact hnotU ⟨z, hz, hzpos⟩
  exact lt_of_le_of_ne hzle (haxis z hz)

end Matrix

namespace SmoothEquilibriumContinuation

variable {I : Type} [DecidableEq I] [Fintype I]

/-- Entrywise continuity of the continuation Jacobian. -/
theorem jacobian_entry_continuous (C : SmoothEquilibriumContinuation I) (i j : I) :
    Continuous (fun μ => C.jacobian μ i j) := by
  exact (continuous_apply j).comp ((continuous_apply i).comp C.jacobianContinuous)

/-- Strict Hurwitz stability is open along the continuation parameter. -/
theorem isOpen_hurwitzParameterSet (C : SmoothEquilibriumContinuation I) :
    IsOpen {μ : ℝ | (C.jacobian μ).IsHurwitzReal} := by
  rw [isOpen_iff_mem_nhds]
  intro μ hμ
  exact Matrix.eventually_isHurwitzReal_of_entrywise
    (fun i j => (C.jacobian_entry_continuous i j).continuousAt) hμ

/-- Strict right-half-plane instability is open along the continuation parameter. -/
theorem isOpen_unstableParameterSet (C : SmoothEquilibriumContinuation I) :
    IsOpen {μ : ℝ | (C.jacobian μ).HasUnstableEigenvalue} := by
  rw [isOpen_iff_mem_nhds]
  intro μ hμ
  exact Matrix.eventually_hasUnstableEigenvalue_of_entrywise
    (fun i j => (C.jacobian_entry_continuous i j).continuousAt) hμ

/-- Boundary parameter of the connected stable component containing zero, clipped to `[0,1]`. -/
noncomputable def stabilityBoundary (C : SmoothEquilibriumContinuation I) : ℝ :=
  sSup ({μ : ℝ | μ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ t ∈ Set.Icc (0 : ℝ) μ, (C.jacobian t).IsHurwitzReal})

/-- The stability boundary lies in the physical continuation interval. -/
theorem stabilityBoundary_mem (C : SmoothEquilibriumContinuation I) :
    C.stabilityBoundary ∈ Set.Icc (0 : ℝ) 1 := by
  have hnonempty : ({μ : ℝ | μ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) μ, (C.jacobian t).IsHurwitzReal}).Nonempty := by
    refine ⟨0, ⟨⟨le_rfl, zero_le_one⟩, ?_⟩⟩
    intro t ht
    have : t = 0 := by linarith [ht.1, ht.2]
    simpa [this] using C.stableAtZero
  have hub : BddAbove ({μ : ℝ | μ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∀ t ∈ Set.Icc (0 : ℝ) μ, (C.jacobian t).IsHurwitzReal}) := by
    refine ⟨1, ?_⟩
    intro μ hμ
    exact hμ.1.2
  constructor
  · exact le_csSup hub ⟨⟨le_rfl, zero_le_one⟩, by
      intro t ht
      have : t = 0 := by linarith [ht.1, ht.2]
      simpa [this] using C.stableAtZero⟩
  · exact csSup_le hnonempty (fun μ hμ => hμ.1.2)

/-- Every parameter strictly before the supremal stable prefix remains Hurwitz. -/
theorem stable_before_stabilityBoundary (C : SmoothEquilibriumContinuation I)
    {t : ℝ} (ht : t < C.stabilityBoundary) (ht0 : 0 ≤ t) :
    (C.jacobian t).IsHurwitzReal := by
  let S : Set ℝ := {μ | μ ∈ Set.Icc (0 : ℝ) 1 ∧
    ∀ u ∈ Set.Icc (0 : ℝ) μ, (C.jacobian u).IsHurwitzReal}
  have hS : S.Nonempty := by
    refine ⟨0, ⟨⟨le_rfl, zero_le_one⟩, ?_⟩⟩
    intro u hu
    have hu0 : u = 0 := by linarith [hu.1, hu.2]
    simpa [hu0] using C.stableAtZero
  have ht' : t < sSup S := by simpa only [stabilityBoundary, S] using ht
  obtain ⟨μ, hμ, htμ⟩ := exists_lt_of_lt_csSup hS ht'
  exact hμ.2 t ⟨ht0, htμ.le⟩

/-- At the boundary of the stable component the Jacobian is not strictly Hurwitz. -/
theorem not_hurwitz_stabilityBoundary (C : SmoothEquilibriumContinuation I) :
    ¬ (C.jacobian C.stabilityBoundary).IsHurwitzReal := by
  intro hH
  have hopen := C.isOpen_hurwitzParameterSet
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen _ hH
  have hb := C.stabilityBoundary_mem
  by_cases hb1 : C.stabilityBoundary = 1
  · rw [hb1] at hH
    exact (Matrix.not_isHurwitzReal_of_hasUnstableEigenvalue C.unstableAtOne) hH
  · let μ' := min 1 (C.stabilityBoundary + δ / 2)
    have hgt : C.stabilityBoundary < μ' := by
      dsimp [μ']
      have : C.stabilityBoundary < 1 := lt_of_le_of_ne hb.2 hb1
      exact lt_min this (by linarith)
    have hstableInterval : ∀ t ∈ Set.Icc (0 : ℝ) μ', (C.jacobian t).IsHurwitzReal := by
      intro t ht
      by_cases htb : t ≤ C.stabilityBoundary
      · by_cases hstrict : t < C.stabilityBoundary
        · exact C.stable_before_stabilityBoundary hstrict ht.1
        · have hteq : t = C.stabilityBoundary := le_antisymm htb (le_of_not_gt hstrict)
          simpa [hteq] using hH
      · have hdist : dist t C.stabilityBoundary < δ := by
          rw [Real.dist_eq]
          rw [abs_of_nonneg (by linarith [htb])]
          have htupper : t ≤ C.stabilityBoundary + δ / 2 :=
            le_trans ht.2 (min_le_right _ _)
          linarith
        exact hδ hdist
    have hmem : μ' ∈ {μ : ℝ | μ ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ t ∈ Set.Icc (0 : ℝ) μ, (C.jacobian t).IsHurwitzReal} := by
      exact ⟨⟨by linarith [hb.1], by simp [μ']⟩, hstableInterval⟩
    exact (not_lt_of_ge (le_csSup
      (show BddAbove ({μ : ℝ | μ ∈ Set.Icc (0 : ℝ) 1 ∧
        ∀ t ∈ Set.Icc (0 : ℝ) μ, (C.jacobian t).IsHurwitzReal}) from
        ⟨1, by intro x hx; exact hx.1.2⟩) hmem)) hgt

/-- The boundary Jacobian is not strictly unstable either; otherwise instability openness would
reach parameters strictly before the supremal stable boundary. -/
theorem not_unstable_stabilityBoundary (C : SmoothEquilibriumContinuation I) :
    ¬ (C.jacobian C.stabilityBoundary).HasUnstableEigenvalue := by
  intro hU
  have hopen := C.isOpen_unstableParameterSet
  obtain ⟨δ, hδpos, hδ⟩ := Metric.isOpen_iff.mp hopen _ hU
  have hb := C.stabilityBoundary_mem
  let μ := max 0 (C.stabilityBoundary - δ / 2)
  have hbpos : 0 < C.stabilityBoundary := by
    by_contra h
    have hbzero : C.stabilityBoundary = 0 := le_antisymm (le_of_not_gt h) hb.1
    rw [hbzero] at hU
    exact (Matrix.not_isHurwitzReal_of_hasUnstableEigenvalue hU) C.stableAtZero
  have hμlt : μ < C.stabilityBoundary := by
    dsimp [μ]
    exact max_lt hbpos (by linarith)
  have hμstable : (C.jacobian μ).IsHurwitzReal :=
    C.stable_before_stabilityBoundary hμlt (le_max_left _ _)
  have hdist : dist μ C.stabilityBoundary < δ := by
    rw [Real.dist_eq]
    dsimp [μ]
    by_cases hcase : 0 ≤ C.stabilityBoundary - δ / 2
    · rw [max_eq_right hcase, abs_of_nonpos]
      · linarith
      · linarith
    · rw [max_eq_left (le_of_not_ge hcase), abs_of_nonpos (by linarith [hb.1])]
      linarith
  obtain ⟨z, hz, hzpos⟩ := hδ hdist
  exact (not_lt_of_ge (le_of_lt (hμstable z hz))) hzpos

end SmoothEquilibriumContinuation

/-- **Spectral-boundary theorem.** Stability change along a continuous nonsingular real Jacobian
path forces a nonzero imaginary-axis eigenvalue. -/
theorem stabilityChangeImaginaryCrossing
    (I : Type) [DecidableEq I] [Fintype I]
    (C : SmoothEquilibriumContinuation I) :
    Nonempty (ImaginarySpectrumWitness C) := by
  classical
  haveI : Nonempty I := by
    by_contra h
    haveI : IsEmpty I := not_nonempty_iff.mp h
    rcases C.unstableAtOne with ⟨z, hz, _⟩
    simp [Matrix.charpoly_isEmpty] at hz
  let μ := C.stabilityBoundary
  have hnotH := C.not_hurwitz_stabilityBoundary
  have hnotU := C.not_unstable_stabilityBoundary
  obtain ⟨z, hz, hzre⟩ :=
    Matrix.exists_imaginary_axis_eigenvalue_of_not_hurwitz_not_unstable
      (C.jacobian μ) inferInstance hnotH hnotU
  have hzneq : z ≠ 0 := by
    intro hz0
    have hdetComplex : ((C.jacobian μ).map (algebraMap ℝ ℂ)).det = 0 := by
      rw [Matrix.det_eq_prod_roots_charpoly]
      exact Multiset.prod_eq_zero (by simpa [hz0] using hz)
    have hdet0 : (C.jacobian μ).det = 0 := by
      apply (FaithfulSMul.algebraMap_eq_zero_iff ℝ ℂ).mp
      rw [RingHom.map_det]
      exact hdetComplex
    exact C.nonsingular μ hdet0
  let ω : ℝ := z.im
  have hzform : z = Complex.I * ω := by
    apply Complex.ext
    · simp [hzre, ω]
    · simp [ω]
  have hω : ω ≠ 0 := by
    intro h0
    apply hzneq
    rw [hzform, h0]
    simp
  refine ⟨{
    parameter := μ
    omega := ω
    omega_ne_zero := hω
    isEigenvalue := ?_ }⟩
  rw [← hzform]
  apply (Module.End.hasEigenvalue_iff_isRoot_charpoly _ _).2
  rw [Matrix.charpoly_toLin']
  exact (Polynomial.mem_roots (Matrix.charpoly_monic _).ne_zero).mp hz

/-- The formerly exposed target is therefore discharged by the finite-dimensional spectral layer. -/
theorem stabilityChangeImaginaryCrossingTarget_proved :
    StabilityChangeImaginaryCrossingTarget := by
  intro I _ _ C
  exact stabilityChangeImaginaryCrossing I C

end CRNT
