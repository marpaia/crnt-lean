import CRNT.Oscillation.DHopf
import Mathlib.Analysis.Normed.Field.Approximation
import Mathlib.Analysis.Polynomial.CauchyBound
import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.FunProp

set_option maxHeartbeats 500000

/-!
# Openness of strict spectral half-plane conditions

This file closes the finite-dimensional perturbation fact used by the D-Hopf/child-selection
construction.  The proof route is deliberately elementary and auditable:

1. every coefficient of the characteristic polynomial is a polynomial in the matrix entries, hence
   depends continuously on an entrywise-continuous matrix family;
2. Mathlib's quantitative continuity-of-roots theorem for monic polynomials transports roots under
   sufficiently small coefficient perturbations;
3. a strict right-half-plane root has a positive real-part margin, so one nearby perturbed root is
   still strictly unstable;
4. a Hurwitz matrix has finitely many roots and therefore a uniform positive distance from the
   imaginary axis; every perturbed root is close to some original root, hence remains in the open
   left half-plane.

No eigenvalue enumeration is chosen.  Multiplicities are handled by the characteristic polynomial.
-/

namespace Matrix

open Polynomial Complex Filter Set Topology

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Complex characteristic polynomial of a real matrix. -/
noncomputable def complexCharpoly (M : Matrix n n ℝ) : Polynomial ℂ :=
  (M.map (algebraMap ℝ ℂ)).charpoly

@[simp] theorem complexCharpoly_monic (M : Matrix n n ℝ) :
    (complexCharpoly M).Monic :=
  Matrix.charpoly_monic _

@[simp] theorem complexCharpoly_natDegree (M : Matrix n n ℝ) :
    (complexCharpoly M).natDegree = Fintype.card n := by
  simp [complexCharpoly]

/-- Characteristic-polynomial coefficients vary continuously along an entrywise-continuous real
matrix path.  This is the only matrix-to-polynomial continuity fact used by the spectral openness
proofs below. -/
theorem continuousAt_complexCharpoly_coeff_of_entrywise
    {A : ℝ → Matrix n n ℝ} {t₀ : ℝ}
    (hA : ∀ i j, ContinuousAt (fun t => A t i j) t₀) (k : ℕ) :
    ContinuousAt (fun t => (complexCharpoly (A t)).coeff k) t₀ := by
  -- `charpoly.univ` expresses every coefficient as an `MvPolynomial` in the entries.
  -- Evaluation of an `MvPolynomial` is continuous, and the uncurrying map from a matrix to its
  -- `(row,column)`-indexed entries is continuous coordinatewise.
  let entry : ℝ → (n × n → ℂ) := fun t ij => (A t ij.1 ij.2 : ℂ)
  have hentry : ContinuousAt entry t₀ := by
    apply continuousAt_pi.mpr
    intro ij
    exact Complex.continuous_ofReal.continuousAt.comp (hA ij.1 ij.2)
  let q : MvPolynomial (n × n) ℂ := (Matrix.charpoly.univ ℂ n).coeff k
  have hq : Continuous (fun x : n × n → ℂ => MvPolynomial.eval x q) := by
    simpa [q] using q.continuous_eval
  have hcomp := hq.continuousAt.comp hentry
  convert hcomp using 1
  funext t
  change (Matrix.of (Function.curry (entry t))).charpoly.coeff k =
    MvPolynomial.eval (entry t) q
  exact (Matrix.charpoly.univ_coeff_eval₂Hom n (RingHom.id ℂ) (entry t) k).symm

/-- Simultaneous coefficient control for a finite-degree characteristic polynomial. -/
theorem eventually_complexCharpoly_coeff_close
    {A : ℝ → Matrix n n ℝ} {t₀ : ℝ}
    (hA : ∀ i j, ContinuousAt (fun t => A t i j) t₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 t₀, ∀ k : ℕ,
      ‖(complexCharpoly (A t)).coeff k - (complexCharpoly (A t₀)).coeff k‖ < ε := by
  let N := Fintype.card n
  have hfinite : ∀ᶠ t in 𝓝 t₀, ∀ k ∈ Finset.range (N + 1),
      ‖(complexCharpoly (A t)).coeff k - (complexCharpoly (A t₀)).coeff k‖ < ε := by
    have hall : ∀ k ∈ Finset.range (N + 1), ∀ᶠ t in 𝓝 t₀,
        (complexCharpoly (A t)).coeff k ∈ Metric.ball ((complexCharpoly (A t₀)).coeff k) ε :=
      fun k _ => (continuousAt_complexCharpoly_coeff_of_entrywise hA k).tendsto
        (Metric.ball_mem_nhds _ hε)
    filter_upwards [(Finset.eventually_all (Finset.range (N + 1))).mpr hall] with t ht k hk
    simpa only [Metric.mem_ball, dist_eq_norm] using ht k hk
  filter_upwards [hfinite] with t ht k
  by_cases hk : k ≤ N
  · exact ht k (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))
  · have hk' : N < k := Nat.lt_of_not_ge hk
    have hzero_t : (complexCharpoly (A t)).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa using hk'
    have hzero_0 : (complexCharpoly (A t₀)).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      simpa using hk'
    simp [hzero_t, hzero_0, hε]

/-- Quantitative root error bound from Mathlib's polynomial root approximation theorem. -/
noncomputable def rootErrorBound (N : ℕ) (ε : ℝ) (z : ℂ) : ℝ :=
  (((N : ℝ) + 1) * ε) ^ ((N : ℝ)⁻¹) * max ‖z‖ 1

/-- For positive degree, the quantitative root-error bound tends to zero with coefficient error. -/
theorem rootErrorBound_tendsto_zero {N : ℕ} (hN : 0 < N) (z : ℂ) :
    Tendsto (fun ε : ℝ => rootErrorBound N ε z) (𝓝[>] 0) (𝓝 0) := by
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hp : ((N : ℝ)⁻¹) ≠ 0 := by positivity
  have hlin : Tendsto (fun ε : ℝ => ((N : ℝ) + 1) * ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hcont : Continuous (fun ε : ℝ => ((N : ℝ) + 1) * ε) :=
      continuous_const.mul continuous_id
    have hAt : ContinuousAt (fun ε : ℝ => ((N : ℝ) + 1) * ε) 0 := hcont.continuousAt
    simpa using hAt.tendsto.mono_left nhdsWithin_le_nhds
  have hrpow : Tendsto (fun x : ℝ => x ^ ((N : ℝ)⁻¹)) (𝓝 (0 : ℝ)) (𝓝 0) := by
    have h := (Real.continuousAt_rpow_const (0 : ℝ) ((N : ℝ)⁻¹)
      (Or.inr (by positivity))).tendsto
    simpa [Real.zero_rpow hp] using h
  have hpow : Tendsto (fun ε : ℝ => (((N : ℝ) + 1) * ε) ^ ((N : ℝ)⁻¹))
      (𝓝[>] 0) (𝓝 0) := by
    simpa [Function.comp_def] using hrpow.comp hlin
  simpa [rootErrorBound] using hpow.mul_const (max ‖z‖ 1)

/-- Choose a coefficient tolerance forcing the quantitative root error below a prescribed radius. -/
theorem exists_coeff_tolerance_rootError_lt {N : ℕ} (hN : 0 < N)
    (z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∃ ε : ℝ, 0 < ε ∧ rootErrorBound N ε z < r := by
  have h := (rootErrorBound_tendsto_zero hN z).eventually (Metric.ball_mem_nhds 0 hr)
  obtain ⟨ε, hεbound, hεmem⟩ := (h.and self_mem_nhdsWithin).exists
  refine ⟨ε, ?_, ?_⟩
  · simpa using hεmem
  · have hεabs : |rootErrorBound N ε z| < r := by simpa using hεbound
    exact (abs_lt.mp hεabs).2

/-- A strict unstable root survives a sufficiently small entrywise-continuous matrix perturbation. -/
theorem eventually_hasUnstableEigenvalue_of_entrywise
    {A : ℝ → Matrix n n ℝ} {t₀ : ℝ}
    (hA : ∀ i j, ContinuousAt (fun t => A t i j) t₀)
    (hunst : (A t₀).HasUnstableEigenvalue) :
    ∀ᶠ t in 𝓝 t₀, (A t).HasUnstableEigenvalue := by
  obtain ⟨z, hzroot, hzpos⟩ := hunst
  have hN : 0 < Fintype.card n := by
    by_contra hzero
    have : Fintype.card n = 0 := Nat.eq_zero_of_not_pos hzero
    have hdeg : (complexCharpoly (A t₀)).natDegree = 0 := by simp [this]
    have hroots : (complexCharpoly (A t₀)).roots = 0 := by
      exact Multiset.card_eq_zero.mp (by
        exact le_antisymm (Polynomial.card_roots' _ |>.trans_eq hdeg) (Nat.zero_le _))
    have hzroot' : z ∈ (complexCharpoly (A t₀)).roots := by
      simpa [complexCharpoly] using hzroot
    rw [hroots] at hzroot'
    simpa using hzroot'
  let r : ℝ := z.re / 2
  have hr : 0 < r := by dsimp [r]; linarith
  obtain ⟨ε, hε, herr⟩ := exists_coeff_tolerance_rootError_lt hN z hr
  have hcoeff := eventually_complexCharpoly_coeff_close hA hε
  filter_upwards [hcoeff] with t ht
  let f := complexCharpoly (A t₀)
  let g := complexCharpoly (A t)
  have hz_eval : Polynomial.eval z f = 0 := by
    exact (Polynomial.mem_roots
      (by simpa [f] using (complexCharpoly_monic (A t₀)).ne_zero)).mp hzroot
  obtain ⟨w, hwroot, hzw⟩ :=
    Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
      hε hz_eval (complexCharpoly_monic (A t₀)) (complexCharpoly_monic (A t))
        (by simp [f, g]) ht (Complex.isAlgClosed.splits g)
  refine ⟨w, ?_, ?_⟩
  · simpa [g, complexCharpoly] using hwroot
  · have hre : |z.re - w.re| ≤ ‖z - w‖ := by
      simpa [Complex.norm_def] using Complex.abs_re_le_norm (z - w)
    have hdist : ‖z - w‖ < r := by
      calc
        ‖z - w‖ < rootErrorBound (Fintype.card n) ε z := by
          simpa [f, rootErrorBound, complexCharpoly_natDegree] using hzw
        _ < r := herr
    have habs : |z.re - w.re| < r := lt_of_le_of_lt hre hdist
    have hdiff : z.re - w.re < r := (abs_lt.mp habs).2
    have : z.re - r < w.re := by linarith
    dsimp [r] at this ⊢
    linarith

/-- A Hurwitz characteristic polynomial has a uniform strictly negative real-part margin. -/
noncomputable def hurwitzMargin (M : Matrix n n ℝ) : ℝ :=
  if h : (complexCharpoly M).roots = 0 then 1
  else Finset.min' ((complexCharpoly M).roots.toFinset.image (fun z : ℂ => -z.re))
    (by simpa [h])

/-- The Hurwitz margin is positive. -/
theorem hurwitzMargin_pos {M : Matrix n n ℝ} (hM : M.IsHurwitzReal) :
    0 < hurwitzMargin M := by
  classical
  unfold hurwitzMargin
  split_ifs with hroot
  · norm_num
  · rw [Finset.lt_min'_iff]
    intro a ha
    rcases Finset.mem_image.mp ha with ⟨z, hz, rfl⟩
    have hzroot : z ∈ (complexCharpoly M).roots := by
      simpa using hz
    have hzneg : z.re < 0 := hM z (by simpa [complexCharpoly] using hzroot)
    linarith

/-- Every root of a Hurwitz matrix lies at least `hurwitzMargin` to the left of the imaginary axis. -/
theorem root_re_le_neg_hurwitzMargin {M : Matrix n n ℝ} (hM : M.IsHurwitzReal)
    {z : ℂ} (hz : z ∈ (complexCharpoly M).roots) :
    z.re ≤ -hurwitzMargin M := by
  classical
  unfold hurwitzMargin
  split_ifs with hroot
  · simp [hroot] at hz
  · have hmem : -z.re ∈ (complexCharpoly M).roots.toFinset.image (fun w : ℂ => -w.re) := by
      exact Finset.mem_image.mpr ⟨z, by simpa using hz, rfl⟩
    have hmin := Finset.min'_le _ _ hmem
    linarith

/-- Hurwitz stability survives sufficiently small entrywise-continuous perturbations. -/
theorem eventually_isHurwitzReal_of_entrywise
    {A : ℝ → Matrix n n ℝ} {t₀ : ℝ}
    (hA : ∀ i j, ContinuousAt (fun t => A t i j) t₀)
    (hstable : (A t₀).IsHurwitzReal) :
    ∀ᶠ t in 𝓝 t₀, (A t).IsHurwitzReal := by
  classical
  by_cases hn : IsEmpty n
  · haveI := hn
    filter_upwards [] with t
    intro z hz
    simp [complexCharpoly] at hz
  · have hcard : 0 < Fintype.card n := by
      by_contra hcard
      apply hn
      exact Fintype.card_eq_zero_iff.mp (Nat.eq_zero_of_not_pos hcard)
    letI : Nonempty n := Fintype.card_pos_iff.mp hcard
    let N : ℕ := Fintype.card n
    set m : ℝ := hurwitzMargin (A t₀) with hmdef
    have hm : 0 < m := by
      rw [hmdef]
      exact hurwitzMargin_pos hstable
    let p₀ : Polynomial ℂ := complexCharpoly (A t₀)
    have hp₀monic : p₀.Monic := by
      simpa [p₀] using complexCharpoly_monic (A t₀)
    have hp₀degree : p₀.natDegree = N := by
      simp [p₀, N]
    let U : NNReal := ∑ i ∈ Finset.range N, (‖p₀.coeff i‖₊ + 1)
    let R : ℝ := (U : ℝ) + 2
    have hRge1 : 1 ≤ R := by
      dsimp [R]
      have hUnn : 0 ≤ (U : ℝ) := NNReal.coe_nonneg U
      linarith
    have hN : 0 < N := by simpa [N] using hcard
    obtain ⟨ε, hε, herr⟩ := exists_coeff_tolerance_rootError_lt hN (R : ℂ)
      (by linarith [hm] : 0 < m / 2)
    have hcoeffUnit := eventually_complexCharpoly_coeff_close hA (by norm_num : 0 < (1 : ℝ))
    have hcoeffε := eventually_complexCharpoly_coeff_close hA hε
    filter_upwards [hcoeffUnit, hcoeffε] with t htUnit htε
    intro z hz
    let p : Polynomial ℂ := complexCharpoly (A t)
    have hpmonic : p.Monic := by simpa [p] using complexCharpoly_monic (A t)
    have hpdegree : p.natDegree = N := by simp [p, N]
    have hcoeffBound (i : ℕ) (hi : i ∈ Finset.range N) :
        ‖p.coeff i‖₊ ≤ ‖p₀.coeff i‖₊ + 1 := by
      have hreal : ‖p.coeff i‖ ≤ ‖p₀.coeff i‖ + 1 := by
        have hclose : ‖p.coeff i - p₀.coeff i‖ < 1 := by
          simpa [p, p₀] using htUnit i
        calc
          ‖p.coeff i‖ = ‖p₀.coeff i + (p.coeff i - p₀.coeff i)‖ := by
            congr 1
            ring
          _ ≤ ‖p₀.coeff i‖ + ‖p.coeff i - p₀.coeff i‖ := norm_add_le _ _
          _ ≤ ‖p₀.coeff i‖ + 1 := by linarith
      exact_mod_cast hreal
    have hleading : ‖p.leadingCoeff‖₊ = 1 := by
      rw [hpmonic.leadingCoeff]
      norm_num
    have hcauchy : p.cauchyBound ≤ U + 1 := by
      have hsup : Finset.sup (Finset.range N) (fun i => ‖p.coeff i‖₊) ≤ U := by
        apply Finset.sup_le
        intro i hi
        exact (hcoeffBound i hi).trans <| Finset.single_le_sum
          (fun j hj =>
            add_nonneg
              (show (0 : NNReal) ≤ ‖p₀.coeff j‖₊ by positivity)
              (show (0 : NNReal) ≤ (1 : NNReal) by positivity)) hi
      calc
        p.cauchyBound = Finset.sup (Finset.range N) (fun i => ‖p.coeff i‖₊) + 1 := by
          simp [Polynomial.cauchyBound, hpdegree, hleading]
        _ ≤ U + 1 := by simpa [add_comm] using add_le_add_right hsup (1 : NNReal)
    have hzroot : z ∈ p.roots := by
      change z ∈ p.roots
      simpa [p, complexCharpoly] using hz
    have hzeval : p.IsRoot z := (Polynomial.mem_roots hpmonic.ne_zero).mp hzroot
    have hznorm : ‖z‖₊ < U + 1 := lt_of_lt_of_le
      (Polynomial.IsRoot.norm_lt_cauchyBound hpmonic.ne_zero hzeval) hcauchy
    have hznormReal : ‖z‖ < (U : ℝ) + 1 := by exact_mod_cast hznorm
    have hmaxz : max ‖z‖ 1 ≤ R := by
      apply max_le
      · dsimp [R]
        linarith
      · exact hRge1
    have hnormR : ‖(R : ℂ)‖ = R := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hRge1])]
    have hmaxR : max ‖(R : ℂ)‖ 1 = R := by
      rw [hnormR, max_eq_left hRge1]
    have hz_eval : Polynomial.eval z p = 0 := hzeval
    obtain ⟨w, hwroot, hzw⟩ :=
      Polynomial.exists_roots_norm_sub_lt_of_norm_coeff_sub_lt
        hε hz_eval hpmonic hp₀monic (by simp [p, p₀, N])
        (fun i => by
          rw [norm_sub_rev]
          exact htε i)
        (Complex.isAlgClosed.splits p₀)
    have hwroot' : w ∈ p₀.roots := by simpa [p₀] using hwroot
    have hw : w.re ≤ -m := by
      apply root_re_le_neg_hurwitzMargin hstable hwroot'
    have hzwBound : ‖z - w‖ < rootErrorBound N ε z := by
      simpa [rootErrorBound, hpdegree] using hzw
    have herrorMono : rootErrorBound N ε z ≤ rootErrorBound N ε (R : ℂ) := by
      unfold rootErrorBound
      rw [hmaxR]
      exact mul_le_mul_of_nonneg_left hmaxz (by positivity)
    have hdist : ‖z - w‖ < m / 2 := by
      exact lt_of_lt_of_le hzwBound (le_trans herrorMono (le_of_lt herr))
    have hre : |z.re - w.re| ≤ ‖z - w‖ := by
      simpa [sub_eq_add_neg] using Complex.abs_re_le_norm (z - w)
    have habs : |z.re - w.re| < m / 2 := lt_of_le_of_lt hre hdist
    have hdiff : z.re - w.re < m / 2 := (abs_lt.mp habs).2
    linarith

/-- The strict stable/unstable conditions in a strong D-Hopf witness persist under any
entrywise-continuous matrix path. -/
theorem strongDHopfWitness_eventually
    (M : Matrix n n ℝ) (W : StrongDHopfWitness M)
    (A : ℝ → Matrix n n ℝ)
    (hA0 : A 0 = M)
    (hcont : ∀ i j, ContinuousAt (fun ε => A ε i j) 0) :
    ∀ᶠ ε in 𝓝 0, Nonempty (StrongDHopfWitness (A ε)) := by
  let As : ℝ → Matrix n n ℝ := fun ε => A ε * Matrix.diagonal W.stableDiagonal
  let Au : ℝ → Matrix n n ℝ := fun ε => A ε * Matrix.diagonal W.unstableDiagonal
  have hAs : ∀ i j, ContinuousAt (fun ε => As ε i j) 0 := by
    intro i j
    simp only [As, Matrix.mul_apply, Matrix.diagonal_apply]
    fun_prop
  have hAu : ∀ i j, ContinuousAt (fun ε => Au ε i j) 0 := by
    intro i j
    simp only [Au, Matrix.mul_apply, Matrix.diagonal_apply]
    fun_prop
  have hs0 : (As 0).IsHurwitzReal := by simpa [As, hA0] using W.stable
  have hu0 : (Au 0).HasUnstableEigenvalue := by simpa [Au, hA0] using W.unstable
  have hs := eventually_isHurwitzReal_of_entrywise hAs hs0
  have hu := eventually_hasUnstableEigenvalue_of_entrywise hAu hu0
  have hdet : ∀ᶠ ε in 𝓝 0, (A ε).det ≠ 0 := by
    have hdetcont : ContinuousAt (fun ε => (A ε).det) 0 := by
      have hmat : ContinuousAt A 0 := by
        apply continuousAt_pi.mpr; intro i
        apply continuousAt_pi.mpr; intro j
        exact hcont i j
      exact (continuous_id.matrix_det).continuousAt.comp hmat
    have hdet0 : (A 0).det ≠ 0 := by simpa [hA0] using W.nonsingular
    exact hdetcont.eventually_ne (by simpa [hA0] using hdet0)
  filter_upwards [hs, hu, hdet] with ε hsε huε hdetε
  exact ⟨{
    nonsingular := hdetε
    stableDiagonal := W.stableDiagonal
    unstableDiagonal := W.unstableDiagonal
    stablePositive := W.stablePositive
    unstablePositive := W.unstablePositive
    stable := by simpa [As] using hsε
    unstable := by simpa [Au] using huε
  }⟩

/-- Quantified positive-radius form of spectral openness, ready to discharge the child-selection
D-Hopf perturbation target without importing that higher-level module here. -/
theorem strongDHopfPerturbation_exists
    (M : Matrix n n ℝ) (W : StrongDHopfWitness M)
    (A : ℝ → Matrix n n ℝ)
    (hA0 : A 0 = M)
    (hcont : ∀ i j, ContinuousAt (fun ε => A ε i j) 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ ε : ℝ, 0 < ε → ε < ε₀ → Nonempty (StrongDHopfWitness (A ε)) := by
  have hev := strongDHopfWitness_eventually M W A hA0 hcont
  rcases (mem_nhds_iff.mp hev) with ⟨U, hU, Uopen, h0U⟩
  obtain ⟨ε₀, hε₀pos, hball⟩ := Metric.isOpen_iff.mp Uopen 0 h0U
  refine ⟨ε₀, hε₀pos, ?_⟩
  intro ε hεpos hεlt
  apply hU
  apply hball
  simpa [Real.dist_eq] using (abs_lt.mpr ⟨by linarith, hεlt⟩)

end Matrix
