import CRNT.Extensions.ReactionDiffusion
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# The spectrum of the box Laplacian and the discrete Poincaré inequality

This module develops the **spectral theory of the discretisation** of a reaction–diffusion
system.  The semidiscrete (method of lines) system of `CRNT.Extensions.ReactionDiffusion` is

```
ẋ = D Δ_h x + f(x),      (Δ_h w)_i = ∑_j (w_j - w_i),
```

an ODE on the finite-dimensional space `ι → ℝ`, where `Δ_h` is the *box Laplacian on the
complete graph* and `laplacianMatrix` is its matrix.  What was missing from the library was
the linear algebra of that discretisation: the *spectrum* of the box Laplacian, the
*discrete Poincaré inequality* it entails, and the connection between the semidiscrete
linearization and the *symbol* `J - q D` used by the Turing criterion of `CRNT.Turing`.

## What is formalized

* **Structure of the box Laplacian matrix** (`laplacianMatrix`): the off-diagonal entries are
  `1` and nonnegative (`laplacianMatrix_nonneg_offDiag`), the matrix annihilates the
  constant vectors (`laplacianMatrix_mulVec_one`), the matrix is symmetric
  (`laplacianMatrix_isSymm`), and it is the complete-graph Laplacian `J - |ι| I`
  (`laplacianMatrix_eq_sub_scalar`).
* **The characteristic polynomial** (`laplacianMatrix_charpoly`): the box Laplacian on `n`
  sites has characteristic polynomial `X (X + n)^{n-1}`, i.e. the spectrum is `0` (once, on
  the constant vectors) and `-n` (with multiplicity `n - 1`, on the mean-zero subspace).
  This is the discrete analogue of the statement "the Laplacian of a connected graph has one
  zero eigenvalue and all others negative".
* **The spectral gap** (`laplacian_meanZero`, `laplacian_norm_meanZero`): on the mean-zero
  subspace the box Laplacian acts as `-n` times the identity, so the gap is `n`.
* **The discrete Poincaré inequality** (`laplacian_poincare`, `laplacian_poincare_scaled`):
  `‖w - (mean w) · 1‖ ≤ (1/n) ‖Δ_h w‖`, i.e. the mean-zero component of a field is
  controlled by the Laplacian, with the sharp constant `1/n`.  The quadratic form of the box
  Laplacian is nonpositive (`laplacian_quadratic_nonpos`) and vanishes exactly on the
  constant vectors (`laplacian_quadratic_nonpos_eq_iff`).
* **The Turing connection** (`semidiscreteLinearization_mean_zero`,
  `semidiscreteLinearization_mean_zero_modeMatrix`): the mean-zero spatial modes of the
  semidiscrete two-species linearization are governed by the Turing mode matrix
  `J - q D` at the wavenumber `q = |ι|`, and `modeMatrix_pos_eigenvalue_iff_det_neg` gives
  the *eigenvalue* formulation of the Turing criterion (a mode matrix of a reaction-stable
  system has a positive real eigenvalue exactly when its determinant is negative).

## Restrictions and what this module does **not** give

* Mathlib has **no PDE theory**: there are no weak or strong solutions of the continuous
  PDE `∂_t x = D Δ x + f(x)`, no Sobolev spaces, no parabolic maximal regularity, and hence
  no *pattern selection* results.  This module works on the *linear algebra of the
  discretisation* instead.
* The Laplacian used here is the **box Laplacian on the complete graph**.  It is *not* the
  **Dirichlet Laplacian on a one-dimensional grid**, whose spectrum is
  `4 sin²(k π / 2n)` (`k = 1, …, n`); that operator is a different object and is **not**
  formalized in this library.  Consequently the "wavenumber" of the mode matrix
  `J - q D` is realised here only at the single value `q = |ι|` (the box Laplacian has a
  two-point spectrum), not at a continuum of wavenumbers.
* The Turing statements are statements about the *linearized* system only; no nonlinear
  bifurcation or pattern-selection theory is claimed.
-/

namespace CRNT

namespace ReactionDiffusion

open Polynomial
open CRNT.Turing
open scoped BigOperators

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 800000

/-! ## 1. Elementary structure of the box Laplacian matrix -/

/-- The off-diagonal entries of the box Laplacian matrix are `1`, hence nonnegative. -/
theorem laplacianMatrix_nonneg_offDiag (i j : ι) (hne : i ≠ j) :
    0 ≤ laplacianMatrix i j := by
  simp [laplacianMatrix, hne]

/-- The diagonal entries of the box Laplacian matrix are `1 - |ι|`. -/
theorem laplacianMatrix_diag (i : ι) :
    laplacianMatrix i i = 1 - (Fintype.card ι : ℝ) := by
  simp [laplacianMatrix]

/-- **The box Laplacian matrix annihilates the constant vectors.** -/
theorem laplacianMatrix_mulVec_one :
    laplacianMatrix (ι := ι).mulVec (fun _ => (1 : ℝ)) = 0 := by
  funext i
  rw [laplacianMatrix_mulVec]
  exact laplacian_homogeneous _ (fun _ _ => rfl) i

/-- **The box Laplacian matrix is symmetric.** -/
theorem laplacianMatrix_isSymm : (laplacianMatrix (ι := ι)).IsSymm := by
  ext i j
  by_cases h : i = j
  · simp [laplacianMatrix, h]
  · simp [laplacianMatrix, h, Ne.symm h]

/-- **The box Laplacian matrix is the complete-graph Laplacian `J - |ι| I`.**  Here
`J` is the all-ones matrix (`vecMulVec` of the constant vector with itself) and `I` the
identity matrix (`Matrix.scalar`). -/
theorem laplacianMatrix_eq_sub_scalar :
    laplacianMatrix (ι := ι)
      = Matrix.vecMulVec (fun _ : ι => (1 : ℝ)) (fun _ : ι => (1 : ℝ))
        - Matrix.scalar ι (Fintype.card ι : ℝ) := by
  ext i j
  rw [Matrix.sub_apply, Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.vecMulVec_apply]
  by_cases h : i = j
  · simp [laplacianMatrix, h]
  · simp [laplacianMatrix, h]

/-! ## 2. The characteristic polynomial of the box Laplacian -/

/-- **A polynomial identity.**  For `N ≥ 1` and `c ∈ ℝ`,
`(X^N - c · X^{N-1}) ∘ (X + c) = X (X + c)^{N-1}`; this is the computation of the
characteristic polynomial of `J - N I` from that of `J`. -/
theorem comp_pow_sub (N : ℕ) (c : ℝ) (hN : 0 < N) :
    (Polynomial.X ^ N - Polynomial.C c * Polynomial.X ^ (N - 1)).comp
        (Polynomial.X + Polynomial.C c)
      = Polynomial.X * (Polynomial.X + Polynomial.C c) ^ (N - 1) := by
  show eval₂ Polynomial.C (Polynomial.X + Polynomial.C c)
      (Polynomial.X ^ N - Polynomial.C c * Polynomial.X ^ (N - 1))
    = Polynomial.X * (Polynomial.X + Polynomial.C c) ^ (N - 1)
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_C]
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 1 := ⟨N - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  rw [pow_succ]
  ring

/-- **The characteristic polynomial of the box Laplacian on `n` sites.**  The box Laplacian on
the complete graph is `n (J/n - I) = J - n I`, whose spectrum is `0` (once) and `-n` (with
multiplicity `n - 1`); hence its characteristic polynomial is `X (X + n)^{n-1}`.

The hypothesis `0 < n` is necessary: for the empty site set (`n = 0`) the characteristic
polynomial is `1` (`Matrix.charpoly_isEmpty`), not `X`. -/
theorem laplacianMatrix_charpoly {n : ℕ} (h : Fintype.card ι = n) (hn : 0 < n) :
    laplacianMatrix (ι := ι).charpoly
      = Polynomial.X * (Polynomial.X + Polynomial.C (n : ℝ)) ^ (n - 1) := by
  rw [laplacianMatrix_eq_sub_scalar, Matrix.charpoly_sub_scalar,
    Matrix.charpoly_vecMulVec]
  have hdot : (fun _ : ι => (1 : ℝ)) ⬝ᵥ (fun _ : ι => (1 : ℝ)) = (Fintype.card ι : ℝ) := by
    simp [dotProduct]
  rw [hdot, h]
  rw [Polynomial.smul_eq_C_mul]
  exact comp_pow_sub n (n : ℝ) hn

/-- **The characteristic polynomial of the box Laplacian, in terms of `|ι|`.** -/
theorem laplacianMatrix_charpoly_card [Nonempty ι] :
    (laplacianMatrix (ι := ι)).charpoly
      = Polynomial.X
        * (Polynomial.X + Polynomial.C (Fintype.card ι : ℝ)) ^ (Fintype.card ι - 1) := by
  have h0 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr (inferInstance)
  exact laplacianMatrix_charpoly (n := Fintype.card ι) rfl h0

/-- **The characteristic polynomial of the box Laplacian on the empty site set** is `1`. -/
theorem laplacianMatrix_charpoly_of_isEmpty [IsEmpty ι] :
    (laplacianMatrix (ι := ι)).charpoly = 1 := by
  rw [Matrix.charpoly_isEmpty]

/-! ## 3. The spectrum: the mean-zero subspace and the spectral gap -/

/-- **On the mean-zero subspace the box Laplacian acts as `-n` times the identity.**  This is
the discrete version of the fact that the Laplacian of a connected graph has one zero
eigenvalue (on the constants) and strictly negative eigenvalues on its orthogonal
complement. -/
theorem laplacian_meanZero (w : ι → ℝ) (hw : ∑ j, w j = 0) (i : ι) :
    laplacian ι w i = -(Fintype.card ι : ℝ) * w i := by
  unfold laplacian
  have h1 : (∑ j, (w j - w i)) = (∑ j, w j) - (Fintype.card ι : ℝ) * w i := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  rw [h1, hw]
  ring

/-- **The mean-zero subspace is an eigenspace of the box Laplacian with eigenvalue `-n`.** -/
theorem laplacian_meanZero_eq_smul (w : ι → ℝ) (hw : ∑ j, w j = 0) :
    laplacian ι w = -(Fintype.card ι : ℝ) • w := by
  funext i
  exact laplacian_meanZero w hw i

/-- **The mean-zero subspace is an eigenspace of the box Laplacian *matrix*.** -/
theorem laplacianMatrix_mulVec_meanZero (w : ι → ℝ) (hw : ∑ j, w j = 0) :
    (laplacianMatrix (ι := ι)).mulVec w = -(Fintype.card ι : ℝ) • w := by
  rw [laplacianMatrix_mulVec]
  exact laplacian_meanZero_eq_smul w hw

/-- **The spectral gap of the box Laplacian.**  On the mean-zero subspace the Laplacian acts
as `-n`, so the norm of the Laplacian of a mean-zero vector is `n` times the norm of the
vector: the (absolute) spectral gap is `n = |ι|`. -/
theorem laplacian_norm_meanZero (w : ι → ℝ) (hw : ∑ j, w j = 0) :
    ‖laplacian ι w‖ = (Fintype.card ι : ℝ) * ‖w‖ := by
  rw [laplacian_meanZero_eq_smul w hw, norm_smul, Real.norm_eq_abs,
    abs_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg _))]
  ring

/-- The spatial mean of a vector on the sites. -/
noncomputable def mean (w : ι → ℝ) : ℝ := (∑ j, w j) / (Fintype.card ι : ℝ)

/-- The mean-zero (fluctuation) part of a vector on the sites. -/
noncomputable def fluctuation (w : ι → ℝ) : ι → ℝ := w - mean w • (fun _ => (1 : ℝ))

omit [DecidableEq ι] in
/-- **The fluctuation of a vector has zero mean.** -/
theorem sum_fluctuation (w : ι → ℝ) : ∑ j, fluctuation w j = 0 := by
  by_cases h : IsEmpty ι
  · have hw0 : w = 0 := by
      funext i
      exact h.elim i
    have hsum : (∑ j, w j) = 0 := by rw [hw0]; simp
    have hmean : mean w = 0 := by unfold mean; rw [hsum]; simp
    simp [fluctuation, hw0]
  · have hne : Nonempty ι := by
      classical
      by_contra hcon
      exact h (not_nonempty_iff.mp hcon)
    have h0 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hne
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h0
    have hsum : (∑ j : ι, mean w) = (Fintype.card ι : ℝ) * mean w := by
      simp [Finset.sum_const, Finset.card_univ]
    have hkey : (Fintype.card ι : ℝ) * mean w = ∑ j, w j := by
      unfold mean
      field_simp [ne_of_gt hcard]
    unfold fluctuation
    have h1 : (∑ j, (w - mean w • (fun _ : ι => (1 : ℝ))) j)
        = ∑ j, (w j - mean w) := by
      apply Finset.sum_congr rfl
      intro j _
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : (∑ j, (w j - mean w)) = (∑ j, w j) - (∑ j : ι, mean w) := by
      rw [Finset.sum_sub_distrib]
    rw [h1, h2, hsum, hkey]
    ring

/-- **The Laplacian of a vector equals the Laplacian of its fluctuation**: the constant
vectors are annihilated by the box Laplacian. -/
theorem laplacian_fluctuation (w : ι → ℝ) :
    laplacian ι w = laplacian ι (fluctuation w) := by
  have hones : laplacian ι (fun _ => (1 : ℝ)) = 0 := by
    funext i
    exact laplacian_homogeneous _ (fun _ _ => rfl) i
  have hdecomp : fluctuation w + mean w • (fun _ => (1 : ℝ)) = w := by
    unfold fluctuation
    funext i
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  calc laplacian ι w = laplacian ι (fluctuation w + mean w • (fun _ => (1 : ℝ))) := by
        rw [hdecomp]
    _ = laplacian ι (fluctuation w) + laplacian ι (mean w • (fun _ => (1 : ℝ))) := laplacian_add _ _
    _ = laplacian ι (fluctuation w) + mean w • laplacian ι (fun _ => (1 : ℝ)) := by
        rw [laplacian_smul]
    _ = laplacian ι (fluctuation w) := by rw [hones, smul_zero, add_zero]

/-- **The discrete Poincaré inequality for the box Laplacian, in a division-free form.**
For `n = |ι|` and `s = ∑_j w_j` one has `‖n w - s · 1‖ ≤ ‖Δ_h w‖`; the mean-zero part of
the field is controlled by the Laplacian, with the sharp constant `1/n`. -/
theorem laplacian_poincare_scaled (w : ι → ℝ) :
    ‖(Fintype.card ι : ℝ) • w - (∑ j, w j) • (fun _ => (1 : ℝ))‖ ≤ ‖laplacian ι w‖ := by
  by_cases h : IsEmpty ι
  · have hw0 : w = 0 := by
      funext i
      exact h.elim i
    have hlap : laplacian ι w = 0 := by rw [hw0, laplacian_zero]
    rw [hlap, hw0]
    simp
  · have hne : Nonempty ι := by
      classical
      by_contra hcon
      exact h (not_nonempty_iff.mp hcon)
    have h0 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr hne
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h0
    have hnorm : ‖laplacian ι w‖ = (Fintype.card ι : ℝ) * ‖fluctuation w‖ := by
      rw [laplacian_fluctuation,
        laplacian_meanZero_eq_smul (fluctuation w) (sum_fluctuation w),
        norm_smul, Real.norm_eq_abs, abs_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg _))]
      ring
    have hscaled : (Fintype.card ι : ℝ) • w - (∑ j, w j) • (fun _ => (1 : ℝ))
        = (Fintype.card ι : ℝ) • fluctuation w := by
      have hkey : (Fintype.card ι : ℝ) * mean w = ∑ j, w j := by
        unfold mean
        field_simp [ne_of_gt hcard]
      funext i
      unfold fluctuation
      rw [← hkey]
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hscaled, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    calc (Fintype.card ι : ℝ) * ‖fluctuation w‖ = ‖laplacian ι w‖ := hnorm.symm
      _ ≤ ‖laplacian ι w‖ := le_rfl

/-- **The discrete Poincaré inequality for the box Laplacian.**  Every vector `w` on the sites
satisfies

```
‖w - (mean w) · 1‖ ≤ (1/n) ‖Δ_h w‖,      n = |ι|,
```

i.e. the Laplacian has a spectral gap of `n` on the mean-zero subspace.  The constant `1/n`
is sharp: equality holds for every `w`. -/
theorem laplacian_poincare [Nonempty ι] (w : ι → ℝ) :
    ‖fluctuation w‖ ≤ (1 / (Fintype.card ι : ℝ)) * ‖laplacian ι w‖ := by
  have h0 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr (inferInstance)
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h0
  have hnorm : ‖laplacian ι w‖ = (Fintype.card ι : ℝ) * ‖fluctuation w‖ := by
    rw [laplacian_fluctuation,
      laplacian_meanZero_eq_smul (fluctuation w) (sum_fluctuation w),
      norm_smul, Real.norm_eq_abs, abs_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg _))]
    ring
  have hkey : (1 / (Fintype.card ι : ℝ)) * ((Fintype.card ι : ℝ) * ‖fluctuation w‖)
      = ‖fluctuation w‖ := by
    field_simp [ne_of_gt hcard]
  rw [hnorm, hkey]

/-- **The quadratic form of the box Laplacian on the mean-zero subspace** is `-n ∑_i w_i²`. -/
theorem laplacian_quadratic_meanZero (w : ι → ℝ) (hw : ∑ j, w j = 0) :
    ∑ i, w i * laplacian ι w i = -(Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
  have h1 : (∑ i, w i * laplacian ι w i)
      = ∑ i, (-(Fintype.card ι : ℝ) * (w i * w i)) := by
    rw [laplacian_meanZero_eq_smul w hw]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have h2 : (∑ i, (-(Fintype.card ι : ℝ) * (w i * w i)))
      = -(Fintype.card ι : ℝ) * ∑ i, w i ^ 2 := by
    have h3 : (∑ i, w i * w i) = ∑ i, w i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [← Finset.mul_sum, h3]
  rw [h1, h2]

/-- **The quadratic form of the box Laplacian in terms of the fluctuation.** -/
theorem laplacian_quadratic_fluctuation (w : ι → ℝ) :
    ∑ i, w i * laplacian ι w i
      = -(Fintype.card ι : ℝ) * ∑ i, (fluctuation w i) ^ 2 := by
  have hv : ∀ i, w i = mean w + fluctuation w i := by
    intro i
    simp only [fluctuation, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have h1 : (∑ i, w i * laplacian ι w i)
      = mean w * (∑ i, laplacian ι w i) + ∑ i, (fluctuation w i * laplacian ι w i) := by
    have h2 : (∑ i, w i * laplacian ι w i)
        = ∑ i, ((mean w + fluctuation w i) * laplacian ι w i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hv]
    have h3 : (∑ i, ((mean w + fluctuation w i) * laplacian ι w i))
        = ∑ i, (mean w * laplacian ι w i) + ∑ i, (fluctuation w i * laplacian ι w i) := by
      have h4 : (∑ i, ((mean w + fluctuation w i) * laplacian ι w i))
          = ∑ i, (mean w * laplacian ι w i + fluctuation w i * laplacian ι w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [h4, Finset.sum_add_distrib]
    rw [h2, h3, Finset.mul_sum]
  rw [h1, laplacian_sum_zero, mul_zero, zero_add, laplacian_fluctuation]
  have h3 := laplacian_quadratic_meanZero (fluctuation w) (sum_fluctuation w)
  rw [h3]

/-- **The quadratic form of the box Laplacian is nonpositive.**  For the pairing
`⟨w, Δ_h w⟩ = ∑_i w_i (Δ_h w)_i` one has `⟨w, Δ_h w⟩ ≤ 0` for every `w`; this is the
discrete version of the integration by parts identity `∫ u Δu = -∫ |∇u|²`. -/
theorem laplacian_quadratic_nonpos (w : ι → ℝ) :
    ∑ i, w i * laplacian ι w i ≤ 0 := by
  rw [laplacian_quadratic_fluctuation]
  have hsq : 0 ≤ ∑ i, (fluctuation w i) ^ 2 := by positivity
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hmul : 0 ≤ (Fintype.card ι : ℝ) * ∑ i, (fluctuation w i) ^ 2 := mul_nonneg hcard hsq
  nlinarith [hmul]

/-- **The quadratic form of the box Laplacian vanishes exactly on the constant vectors.** -/
theorem laplacian_quadratic_nonpos_eq_iff [Nonempty ι] (w : ι → ℝ) :
    (∑ i, w i * laplacian ι w i = 0) ↔ ∃ c : ℝ, ∀ i, w i = c := by
  constructor
  · intro h
    rw [laplacian_quadratic_fluctuation] at h
    have h0 : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr (inferInstance)
    have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast h0
    have hsum : (∑ i, (fluctuation w i) ^ 2) = 0 := by nlinarith [h]
    have hzero : ∀ i, fluctuation w i = 0 := by
      have h' := Finset.sum_eq_zero_iff_of_nonneg (s := (Finset.univ : Finset ι))
        (f := fun i => (fluctuation w i) ^ 2) (fun i _ => by positivity)
      rw [h'] at hsum
      intro i
      have hsq := hsum i (Finset.mem_univ i)
      nlinarith [sq_nonneg (fluctuation w i)]
    refine ⟨mean w, ?_⟩
    intro i
    have hz := hzero i
    simp only [fluctuation, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hz
    linarith
  · rintro ⟨c, hc⟩
    have hhom : ∀ i j, w i = w j := by
      intro i j
      rw [hc i, hc j]
    have hz : laplacian ι w = 0 := by
      funext i
      exact laplacian_homogeneous w hhom i
    rw [hz]
    simp

/-! ## 4. The semidiscrete linearization and the Turing mode matrix -/

/-- **The semidiscrete two-species linearization.**  The reaction Jacobian `J` acts on the
species index and the diffusion matrix `D` acts on the site index (through the box
Laplacian): `(L v) s i = ∑_t J s t v t i + ∑_t D s t (Δ_h v t) i`.  With `D = diag(d₁, d₂)`
this is the linearization of `ẋ = D Δ_h x + J x` of the semidiscrete reaction–diffusion
system with *species-wise* diffusion. -/
def semidiscreteLinearization (J D : Matrix (Fin 2) (Fin 2) ℝ) (v : Fin 2 → (ι → ℝ)) :
    Fin 2 → (ι → ℝ) :=
  fun s => fun i => (∑ t, J s t * v t i) + ∑ t, D s t * laplacian ι (v t) i

/-- **The mean-zero spatial modes of the semidiscrete linearization are governed by
`J - n D`, where `n = |ι|`.**  Indeed the box Laplacian acts as `-n` on the mean-zero
subspace. -/
theorem semidiscreteLinearization_mean_zero (J D : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Fin 2 → (ι → ℝ)) (hv : ∀ s, ∑ i, v s i = 0) :
    semidiscreteLinearization J D v
      = fun s => fun i => ∑ t, (J - (Fintype.card ι : ℝ) • D) s t * v t i := by
  funext s i
  have hdiff : (∑ t, D s t * laplacian ι (v t) i)
      = -(Fintype.card ι : ℝ) * (∑ t, D s t * v t i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    rw [laplacian_meanZero (v t) (hv t) i]
    ring
  have hsum : (∑ t, (J - (Fintype.card ι : ℝ) • D) s t * v t i)
      = (∑ t, J s t * v t i) - (Fintype.card ι : ℝ) * (∑ t, D s t * v t i) := by
    have h1 : (∑ t, ((J - (Fintype.card ι : ℝ) • D) s t) * v t i)
        = ∑ t, (J s t * v t i - (Fintype.card ι : ℝ) * (D s t * v t i)) := by
      apply Finset.sum_congr rfl
      intro t _
      simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [h1, Finset.sum_sub_distrib, Finset.mul_sum]
  rw [semidiscreteLinearization, hdiff, hsum]
  ring

omit [DecidableEq ι] in
/-- **The Turing mode matrix at the wavenumber `|ι|`.**  The mode matrix `J - q D` of
`CRNT.Turing` is the symbol of the linearized two-species system at the wavenumber `q`; for
the box Laplacian on `n` sites the (non-constant) spatial modes have wavenumber `q = n`. -/
theorem modeMatrix_eq_sub_card (a b c d d₁ d₂ : ℝ) :
    !![a, b; c, d] - (Fintype.card ι : ℝ) • !![d₁, 0; 0, d₂]
      = modeMatrix a b c d d₁ d₂ (Fintype.card ι) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [modeMatrix, Matrix.sub_apply, smul_eq_mul] <;> ring

/-- **The semidiscrete system and the Turing criterion see the same linearization.**  The
mean-zero spatial modes of the semidiscrete two-species reaction–diffusion system on `|ι|`
sites are governed by the Turing mode matrix `J - q D` evaluated at the wavenumber
`q = |ι|`. -/
theorem semidiscreteLinearization_mean_zero_modeMatrix (a b c d d₁ d₂ : ℝ)
    (v : Fin 2 → (ι → ℝ)) (hv : ∀ s, ∑ i, v s i = 0) :
    semidiscreteLinearization !![a, b; c, d] !![d₁, 0; 0, d₂] v
      = fun s => fun i => ∑ t, (modeMatrix a b c d d₁ d₂ (Fintype.card ι)) s t * v t i := by
  rw [semidiscreteLinearization_mean_zero (hv := hv), modeMatrix_eq_sub_card]

/-- **The eigenvalue formulation of the Turing criterion.**  A mode matrix `J - q D` of a
reaction-stable two-species system (negative trace) has a positive real eigenvalue if and
only if its determinant is negative; in that case the mode is unstable, exactly as in
Turing's criterion. -/
theorem modeMatrix_pos_eigenvalue_iff_det_neg {a b c d d₁ d₂ q : ℝ}
    (htr : a + d - (d₁ + d₂) * q < 0) :
    (∃ μ : ℝ, 0 < μ ∧ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧
        (modeMatrix a b c d d₁ d₂ q).mulVec v = μ • v)
      ↔ (modeMatrix a b c d d₁ d₂ q).det < 0 := by
  constructor
  · rintro ⟨μ, hμ, v, hv, hmul⟩
    have h1 : (a - d₁ * q) * v 0 + b * v 1 = μ * v 0 := by
      have hz := congrFun hmul 0
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, modeMatrix, Pi.smul_apply] using hz
    have h2 : c * v 0 + (d - d₂ * q) * v 1 = μ * v 1 := by
      have hz := congrFun hmul 1
      simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, modeMatrix, Pi.smul_apply] using hz
    have htr' : (a - d₁ * q) + (d - d₂ * q) < 0 := by nlinarith [htr]
    rw [modeMatrix_det]
    unfold modeDet
    by_cases hx : v 0 = 0
    · have hy : v 1 ≠ 0 := by
        intro hy
        apply hv
        funext i
        fin_cases i
        · exact hx
        · exact hy
      have hb : b = 0 := by
        rw [hx] at h1
        have hz : b * v 1 = 0 := by nlinarith [h1]
        exact (mul_eq_zero.mp hz).resolve_right hy
      have hr : d - d₂ * q = μ := by
        rw [hx] at h2
        have hz : (d - d₂ * q - μ) * v 1 = 0 := by nlinarith [h2]
        have hz' : d - d₂ * q - μ = 0 := (mul_eq_zero.mp hz).resolve_right hy
        linarith
      have : (a - d₁ * q) * (d - d₂ * q) - b * c < 0 := by
        rw [hb, hr]
        nlinarith [htr', hμ]
      exact this
    · have h1' : (a - d₁ * q - μ) * v 0 + b * v 1 = 0 := by linarith [h1]
      have h2' : c * v 0 + (d - d₂ * q - μ) * v 1 = 0 := by linarith [h2]
      have hkey : ((a - d₁ * q - μ) * (d - d₂ * q - μ) - b * c) * v 0 = 0 := by
        linear_combination (d - d₂ * q - μ) * h1' - b * h2'
      have hA : (a - d₁ * q - μ) * (d - d₂ * q - μ) - b * c = 0 :=
        (mul_eq_zero.mp hkey).resolve_right (by exact hx)
      have hdet : (a - d₁ * q) * (d - d₂ * q) - b * c
          = μ * ((a - d₁ * q) + (d - d₂ * q) - μ) := by
        have hbc : (a - d₁ * q - μ) * (d - d₂ * q - μ) = b * c := by linarith [hA]
        nlinarith [hbc]
      nlinarith [hdet, htr', hμ]
  · intro hdet
    rw [modeMatrix_det] at hdet
    unfold modeDet at hdet
    obtain ⟨μ, v₁, v₂, hμ, hv, h₁, h₂⟩ :=
      exists_pos_eigen_of_det_neg (p := a - d₁ * q) (b := b) (c := c) (r := d - d₂ * q) hdet
    refine ⟨μ, hμ, ?_⟩
    let v : Fin 2 → ℝ := fun s => if s = 0 then v₁ else v₂
    refine ⟨v, ?_⟩
    refine ⟨?_, ?_⟩
    · intro hv0
      rcases hv with h1 | h2
      · have hz := congrFun hv0 0
        simp [v] at hz
        exact h1 hz
      · have hz := congrFun hv0 1
        simp [v] at hz
        exact h2 hz
    · have hval0 : v 0 = v₁ := by simp [v]
      have hval1 : v 1 = v₂ := by simp [v]
      have hexp0 : (modeMatrix a b c d d₁ d₂ q).mulVec v 0
          = (a - d₁ * q) * v 0 + b * v 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, modeMatrix]
      have hexp1 : (modeMatrix a b c d d₁ d₂ q).mulVec v 1
          = c * v 0 + (d - d₂ * q) * v 1 := by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, modeMatrix]
      have h0 : (modeMatrix a b c d d₁ d₂ q).mulVec v 0 = μ * v 0 := by
        rw [hexp0]
        have hh : (a - d₁ * q) * v 0 + b * v 1 = μ * v 0 := by
          simpa [hval0, hval1] using h₁
        linarith
      have h1' : (modeMatrix a b c d d₁ d₂ q).mulVec v 1 = μ * v 1 := by
        rw [hexp1]
        have hh : c * v 0 + (d - d₂ * q) * v 1 = μ * v 1 := by
          simpa [hval0, hval1] using h₂
        linarith
      funext i
      have hi : i = 0 ∨ i = 1 := by
        rcases (show i.val = 0 ∨ i.val = 1 by omega) with h | h
        · exact Or.inl (Fin.ext h)
        · exact Or.inr (Fin.ext h)
      rcases hi with h | h
      · rw [h, h0]
        simp [Pi.smul_apply]
      · rw [h, h1']
        simp [Pi.smul_apply]

omit [DecidableEq ι] in
/-- **The Turing criterion for the semidiscrete system.**  The mean-zero spatial mode of the
semidiscrete two-species reaction–diffusion system on `|ι|` sites is governed by the mode
matrix `J - |ι| D`; it is unstable (has a positive real eigenvalue) exactly when
`modeDet a b c d d₁ d₂ |ι| < 0`.  In particular, the semidiscrete system can only be
diffusion-driven unstable if the *unstable wavenumber* of the continuous Turing criterion
happens to be realized by the box Laplacian, i.e. at the single value `|ι|`. -/
theorem semidiscrete_mean_zero_turing_iff {a b c d d₁ d₂ : ℝ} (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (htr : a + d < 0) :
    (∃ μ : ℝ, 0 < μ ∧ ∃ v : Fin 2 → ℝ, v ≠ 0 ∧
        (modeMatrix a b c d d₁ d₂ (Fintype.card ι)).mulVec v = μ • v)
      ↔ modeDet a b c d d₁ d₂ (Fintype.card ι) < 0 := by
  have htr' : a + d - (d₁ + d₂) * (Fintype.card ι : ℝ) < 0 := by
    have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
    have hmul : (0 : ℝ) ≤ (d₁ + d₂) * (Fintype.card ι : ℝ) := mul_nonneg (by positivity) hcard
    linarith
  rw [modeMatrix_pos_eigenvalue_iff_det_neg (htr := htr'), modeMatrix_det]

/-- **The box Laplacian does not realize the Brusselator Turing instability.**  For the
Turing-unstable Brusselator instance (`A = 3`, `B = 2`, `d₁ = 1`, `d₂ = 64`, see
`CRNT.ReactionDiffusion.brusselator_turing_instance`) the mode determinant is *positive* at
every non-negative integer wavenumber `q = n`.  Since the box Laplacian on `n` sites
realizes only the wavenumbers `0` and `n` (its spectrum is `{0, -n}`), the semidiscrete
reaction–diffusion system on the complete graph is *never* diffusion-driven unstable for
these parameters, although the continuous Turing criterion is satisfied: the unstable
wavenumber `55 / 128` of the continuous problem is not realized by this discretisation. -/
theorem brusselator_semidiscrete_not_unstable (n : ℕ) :
    0 < modeDet (2 - 1) (3 ^ 2) (-2) (-(3 ^ 2)) 1 64 (n : ℝ) := by
  unfold modeDet
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · norm_num
  · have hle : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h1 : (1 : ℝ) - (n : ℝ) ≤ 0 := by linarith
    have h2 : (-(9 : ℝ) - 64 * (n : ℝ)) < 0 := by
      have hnonneg : (0 : ℝ) ≤ 64 * (n : ℝ) := by positivity
      linarith
    have hmul : 0 ≤ ((1 : ℝ) - (n : ℝ)) * (-(9 : ℝ) - 64 * (n : ℝ)) :=
      mul_nonneg_of_nonpos_of_nonpos h1 (le_of_lt h2)
    nlinarith [hmul]

end ReactionDiffusion

end CRNT

#print axioms CRNT.ReactionDiffusion.laplacianMatrix_charpoly
#print axioms CRNT.ReactionDiffusion.laplacian_norm_meanZero
#print axioms CRNT.ReactionDiffusion.laplacian_poincare
#print axioms CRNT.ReactionDiffusion.laplacian_poincare_scaled
#print axioms CRNT.ReactionDiffusion.laplacian_quadratic_nonpos
#print axioms CRNT.ReactionDiffusion.laplacian_quadratic_nonpos_eq_iff
#print axioms CRNT.ReactionDiffusion.semidiscreteLinearization_mean_zero
#print axioms CRNT.ReactionDiffusion.semidiscreteLinearization_mean_zero_modeMatrix
#print axioms CRNT.ReactionDiffusion.modeMatrix_pos_eigenvalue_iff_det_neg
#print axioms CRNT.ReactionDiffusion.semidiscrete_mean_zero_turing_iff
#print axioms CRNT.ReactionDiffusion.brusselator_semidiscrete_not_unstable
