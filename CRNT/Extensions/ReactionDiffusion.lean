import CRNT.Dynamics.FlowConstruction
import CRNT.Extensions.Turing
import CRNT.Basic.Network
import CRNT.Kinetics.MassAction
import CRNT.Kinetics.Concentration
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Topology.MetricSpace.Lipschitz

open scoped BigOperators

set_option maxHeartbeats 800000

/-!
# Reaction–diffusion systems (semidiscrete / method of lines)

This module formalizes the **semidiscrete (method-of-lines)** reading of a
reaction–diffusion system.  Mathlib contains no PDE theory (no Sobolev spaces, no
parabolic maximal regularity), so the literal nonlinear PDE `∂_t x = D Δ x + f(x)`
is out of reach.  What is formalizable here is the spatially discretized system

```
ẋ = D Δ_h x + f(x),
```

an ODE on the finite-dimensional space `ι → ℝ`.

## What is formalized

* **The diffusion operator.**  The discrete Laplacian is the *box Laplacian on the
  complete graph*, `(Δ w)_i = ∑_j (w_j - w_i)`, together with its matrix form
  (`laplacianMatrix`, `diffusionMatrix`), the fact that it annihilates spatially
  homogeneous vectors, that it sums to zero over the sites, and a sup-norm bound
  (`laplacian_bound`).
* **Equilibria.**  A spatially homogeneous equilibrium of the reaction term is an
  equilibrium of the field, and conversely.
* **Local existence (item: local existence).**  `exists_reactionDiffusion_solution`:
  for a reaction term that is globally Lipschitz in the scalar variable, the
  semidiscrete ODE has a local solution through `x₀`, obtained from the
  Picard–Lindelöf theorem of Mathlib.  The Lipschitz constant of the field is
  `L + diffusionLipschitzConst D` (in the sup norm), see
  `reactionDiffusionField_lipschitz`.  Only *local* existence is stated: global
  existence would require the standard continuation argument, which is not
  formalized here.
* **The Jacobian (item: Jacobian).**  `reactionDiffusionJacobian` is the matrix
  `D Δ_h + Df` of the semidiscrete linearization; `reactionDiffusionJacobian_mulVec`
  and `reactionDiffusionField_hasDerivAt_curve_matrix` identify it with the
  derivative of the field along the curve `w* + t v`.
* **The Turing connection (item: Turing connection).**  `modeMatrix` is the mode
  matrix `J - q D` of the linearized two-species system with *diagonal species
  diffusion* `D = diag(d₁, d₂)`, `modeMatrix_det`/`modeMatrix_trace` compute its
  determinant and trace, `modeMatrix_hurwitz_iff` links it to the Hurwitz criterion
  of `CRNT.Turing`, and `turing_connection` restates Turing's criterion
  (`CRNT.Turing.diffusionDrivenInstability_iff`) in the notation of this module.
* **A concrete instance (item: Brusselator instance).**  The two-species
  Brusselator: its reaction network `A → X`, `2X + Y → 3X`, `B + X → Y`, `X → E`
  with rate constants `(A, 1, B, 1)`, the induced reaction term
  `ẋ = A - (B+1) x + x² y`, `ẏ = B x - x² y` (the mass-action vector field of the
  network is proved to be exactly this term), its steady state `(A, B/A)`, its
  reaction Jacobian `[[B-1, A²], [-B, -A²]]`, Turing's criterion for those
  parameters, and an explicit Turing-unstable instance (`A = 3`, `B = 2`,
  `d₁ = 1`, `d₂ = 64`).

## Restrictions and what this module does **not** give

* No PDE well-posedness: no weak or strong solutions of the continuous PDE
  `∂_t x = D Δ x + f(x)`, no parabolic theory.
* No pattern selection, no nonlinear bifurcation analysis; the Turing statements
  are statements about the *linearized* system only.
* The diffusion operator is the box Laplacian on the complete graph (or its matrix
  form); it is **not** the continuous Laplacian, and it is not the diagonal
  species-wise diffusion used in `CRNT.Turing`.
* The reaction term of the field is assumed to be **decoupled**, `f i (w i)`: the
  rate of species `i` depends only on its own concentration.  This is what makes
  the reaction Jacobian diagonal, and it excludes genuinely coupled two-species
  systems such as the Brusselator from the vector field of Section 2; the
  Brusselator is therefore treated at the linear level (Section 5).

## Relation to leaf E2 and to `CRNT.Turing`

Leaf E2 (Reaction–diffusion systems; Turing instability) is partial: the linear
Turing analysis lives in `CRNT.Extensions.Turing`, and this module adds the
semidiscrete dynamical-systems backbone (diffusion operator, vector field, local
flow, Jacobian) together with one worked example.

-/

namespace CRNT

namespace ReactionDiffusion

open CRNT.Turing

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## 1. Diffusion operator and reaction–diffusion field -/

/-- The box Laplacian on the complete graph: `(Δ w)_i = ∑_j (w_j - w_i)`. -/
def laplacian (ι : Type) [Fintype ι] [DecidableEq ι] (w : ι → ℝ) : ι → ℝ :=
  fun i => ∑ j, (w j - w i)

/-- The box Laplacian is linear. -/
theorem laplacian_add (w v : ι → ℝ) :
    laplacian ι (w + v) = laplacian ι w + laplacian ι v := by
  funext i
  simp [laplacian]
  have : (∑ j, (w j + v j - (w i + v i))) =
      (∑ j, (w j - w i)) + (∑ j, (v j - v i)) := by
    rw [show (∑ j, (w j + v j - (w i + v i))) = ∑ j, ((w j - w i) + (v j - v i)) from by congr 1; ext j; ring]
    exact Finset.sum_add_distrib
  simpa using this

/-- The box Laplacian is homogeneous of degree one. -/
theorem laplacian_smul (c : ℝ) (w : ι → ℝ) :
    laplacian ι (c • w) = c • laplacian ι w := by
  funext i
  simp [laplacian, smul_eq_mul]
  rw [← Finset.mul_sum]
  ring

/-- The box Laplacian of the zero vector is zero. -/
theorem laplacian_zero : laplacian ι (0 : ι → ℝ) = 0 := by
  funext i
  simp [laplacian]

/-- **The box Laplacian conserves mass**: the sum of the Laplacians over the sites is zero. -/
theorem laplacian_sum_zero (w : ι → ℝ) :
    ∑ i, laplacian ι w i = 0 := by
  unfold laplacian
  calc ∑ i, ∑ j, (w j - w i)
      = ∑ i, ((∑ j, w j) - (Fintype.card ι : ℝ) * w i) := by
          congr 1; ext i; simp [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ]
    _ = (Fintype.card ι : ℝ) * (∑ j, w j) - (Fintype.card ι : ℝ) * (∑ i, w i) := by
          rw [Finset.sum_sub_distrib]
          have hA : ∑ i : ι, ∑ j, w j = (Fintype.card ι : ℝ) * ∑ j, w j := by
            simp [Finset.sum_const, Finset.card_univ]
          have hB : ∑ i, (Fintype.card ι : ℝ) * w i = (Fintype.card ι : ℝ) * ∑ i, w i := by
            rw [← Finset.mul_sum]
          rw [hA, hB]
    _ = 0 := by ring

/-- The box Laplacian annihilates spatially homogeneous vectors. -/
theorem laplacian_homogeneous (w : ι → ℝ) (hhom : ∀ i j, w i = w j) (i : ι) :
    laplacian ι w i = 0 := by
  unfold laplacian
  apply Finset.sum_eq_zero
  intro j _
  have : w j = w i := hhom j i
  rw [this]
  ring

/-- Bound: `|laplacian u i| ≤ (2*card ι - 1) * sup_j |u j|`. -/
theorem laplacian_bound (u : ι → ℝ) (i : ι) [Nonempty ι] :
    |laplacian ι u i| ≤ (2 * (Fintype.card ι : ℝ) - 1) *
      (Finset.sup' Finset.univ (Finset.univ_nonempty) (fun j => |u j|)) := by
  let M := Finset.sup' Finset.univ (Finset.univ_nonempty) (fun j => |u j|)
  have hM : ∀ j, |u j| ≤ M := fun j =>
    Finset.le_sup' (fun j => |u j|) (Finset.mem_univ j)
  have hMnn : 0 ≤ M := by
    obtain ⟨j⟩ := ‹Nonempty ι›
    exact le_trans (abs_nonneg (u j)) (Finset.le_sup' (fun j => |u j|) (Finset.mem_univ j))
  have hg : ∀ j, |u j - u i| ≤ if j = i then 0 else 2 * M := by
    intro j
    by_cases hji : j = i
    · simp [hji]
    · have h1 : |u j - u i| ≤ |u j| + |u i| := by
        simpa using abs_sub_le (u j) 0 (u i)
      have h2 : |u j| + |u i| ≤ M + M := by linarith [hM j, hM i]
      simp only [hji, ite_false]
      linarith
  have hsum_g : (∑ j, (if j = i then (0 : ℝ) else 2 * M)) = 2 * ((Fintype.card ι : ℝ) - 1) * M := by
    have hcard : (Finset.univ.filter (fun j => j ≠ i)).card = Fintype.card ι - 1 := by
      have : Finset.univ.filter (fun j => j ≠ i) = Finset.univ.erase i := by
        ext j; simp [Finset.mem_erase, Finset.mem_univ]
      rw [this]
      exact Finset.card_erase_of_mem (Finset.mem_univ i)
    calc ∑ j, (if j = i then (0 : ℝ) else 2 * M)
        = ∑ j ∈ Finset.univ.filter (fun j => j ≠ i), (2 * M) := by
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun j _ => ?_
            by_cases h : j = i
            · simp [h]
            · simp [h]
      _ = (Fintype.card ι - 1) * (2 * M) := by
            rw [Finset.sum_const, nsmul_eq_mul, hcard]
            have hcardpos : (1:ℕ) ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
            rw [Nat.cast_sub hcardpos]
            simp
      _ = 2 * ((Fintype.card ι : ℝ) - 1) * M := by ring
  calc |laplacian ι u i|
      = |∑ j, (u j - u i)| := by simp [laplacian]
    _ ≤ ∑ j, |u j - u i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, (if j = i then (0 : ℝ) else 2 * M) := Finset.sum_le_sum (fun j _ => hg j)
    _ = 2 * ((Fintype.card ι : ℝ) - 1) * M := hsum_g
    _ ≤ (2 * (Fintype.card ι : ℝ) - 1) * M := by
        have hn : 2 * ((Fintype.card ι : ℝ) - 1) ≤ 2 * (Fintype.card ι : ℝ) - 1 := by nlinarith
        nlinarith [hMnn, hn]

/-- The reaction–diffusion vector field (semidiscrete). -/
def reactionDiffusionField (D : ι → ℝ) (f : ι → ℝ → ℝ) (w : ι → ℝ) : ι → ℝ :=
  fun i => D i * laplacian ι w i + f i (w i)

/-- Homogeneous equilibrium of the reaction term gives an equilibrium of the field. -/
theorem reactionDiffusionField_eq_zero_of_homogeneous
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (w : ι → ℝ)
    (hhom : ∀ i j, w i = w j) (hf : ∀ i, f i (w i) = 0) :
    reactionDiffusionField D f w = 0 := by
  funext i
  simp [reactionDiffusionField, laplacian_homogeneous w hhom i, hf i]

/-- Conversely, a spatially homogeneous equilibrium of the field is an equilibrium of `f`. -/
theorem homogeneous_equilibrium_of_field
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (w : ι → ℝ)
    (hhom : ∀ i j, w i = w j) (heq : reactionDiffusionField D f w = 0) :
    ∀ i, f i (w i) = 0 := by
  intro i
  have hl : laplacian ι w i = 0 := laplacian_homogeneous w hhom i
  have := congrFun heq i
  simp [reactionDiffusionField, hl] at this
  exact this

/-! ## Lipschitz constant of the field -/

/-- The supremum of the absolute values of the diffusion coefficients. -/
noncomputable def Dsup (D : ι → ℝ) [Nonempty ι] : ℝ :=
  Finset.sup' Finset.univ (Finset.univ_nonempty) (fun i => |D i|)

/-- **The Lipschitz constant of the diffusion part** of the field, in the sup norm:
`sup_i |D i| * (2 |ι| - 1)`. -/
noncomputable def diffusionLipschitzConst (D : ι → ℝ) [Nonempty ι] : ℝ :=
  Dsup D * (2 * (Fintype.card ι : ℝ) - 1)

/-- **The semidiscrete field is Lipschitz.**  If every reaction rate `f i` is Lipschitz
with constant `L` in its own variable, then the field `D Δ_h + f` is Lipschitz (in the
sup norm on `ι → ℝ`) with constant `L + diffusionLipschitzConst D`. -/
theorem reactionDiffusionField_lipschitz
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    [Nonempty ι] :
    LipschitzWith (Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D)))
      (reactionDiffusionField D f) := by
  let K := Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D))
  refine LipschitzWith.of_dist_le_mul (K := K) (fun w v => ?_)
  rw [dist_pi_le_iff']
  intro i
  have hlap : |laplacian ι (w - v) i| ≤
      (2 * (Fintype.card ι : ℝ) - 1) *
        (Finset.sup' Finset.univ (Finset.univ_nonempty) (fun j => |(w - v) j|)) := by
    simpa using laplacian_bound (w - v) i
  have hsup : (Finset.sup' Finset.univ (Finset.univ_nonempty) (fun j => |(w - v) j|)) ≤
      dist w v := by
    have : ∀ j ∈ Finset.univ, |(w - v) j| ≤ dist w v := by
      intro j _
      exact dist_le_pi_dist w v j
    exact Finset.sup'_le (Finset.univ_nonempty) (fun j => |(w - v) j|) this
  have hD : |D i| ≤ Dsup D := Finset.le_sup' (fun i => |D i|) (Finset.mem_univ i)
  calc dist (reactionDiffusionField D f w i) (reactionDiffusionField D f v i)
      = |D i * laplacian ι w i + f i (w i) - (D i * laplacian ι v i + f i (v i))| := rfl
    _ = |D i * (laplacian ι (w - v) i) + (f i (w i) - f i (v i))| := by
        have h1 : laplacian ι (w - v) = laplacian ι w - laplacian ι v := by
          have hneg : w - v = w + (-v) := by abel
          have : laplacian ι (w - v) = laplacian ι w + laplacian ι (-v) := by
            rw [hneg]
            exact laplacian_add w (-v)
          rw [this]
          have : laplacian ι (-v) = - laplacian ι v := by
            funext i
            unfold laplacian
            have hpoint : ∀ j, ((-v) j - (-v) i) = -((v j) - (v i)) := by
              intro j; simp only [Pi.neg_apply]; ring
            simp_rw [hpoint]
            rw [Finset.sum_neg_distrib]
            rfl
          rw [this]
          simp [sub_eq_add_neg]
        have hl : laplacian ι w i - laplacian ι v i = laplacian ι (w - v) i :=
          (congrFun h1 i).symm
        have h2 : D i * laplacian ι w i + f i (w i) - (D i * laplacian ι v i + f i (v i))
            = D i * laplacian ι (w - v) i + (f i (w i) - f i (v i)) := by
          rw [← hl]
          ring
        rw [h2]
    _ ≤ |D i| * |laplacian ι (w - v) i| + |f i (w i) - f i (v i)| := by
      calc |D i * laplacian ι (w - v) i + (f i (w i) - f i (v i))|
          ≤ |D i * laplacian ι (w - v) i| + |f i (w i) - f i (v i)| := abs_add_le _ _
        _ ≤ |D i| * |laplacian ι (w - v) i| + |f i (w i) - f i (v i)| := by rw [abs_mul]
    _ ≤ Dsup D * ((2 * (Fintype.card ι : ℝ) - 1) * dist w v) +
        L * |w i - v i| := by
      have hcardpos : (1:ℕ) ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
      have hcard1 : (1:ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hcardpos
      have hnonneg : (0:ℝ) ≤ 2 * (Fintype.card ι : ℝ) - 1 := by linarith
      have hDsup : 0 ≤ Dsup D := by
        obtain ⟨j⟩ := (inferInstance : Nonempty ι)
        exact le_trans (abs_nonneg (D j))
          (Finset.le_sup' (fun i => |D i|) (Finset.mem_univ j))
      have hlap' : |laplacian ι (w - v) i|
          ≤ (2 * (Fintype.card ι : ℝ) - 1) * dist w v :=
        hlap.trans (mul_le_mul_of_nonneg_left hsup hnonneg)
      have h1 : |D i| * |laplacian ι (w - v) i|
          ≤ Dsup D * ((2 * (Fintype.card ι : ℝ) - 1) * dist w v) :=
        le_trans (mul_le_mul_of_nonneg_right hD (abs_nonneg _))
          (mul_le_mul_of_nonneg_left hlap' hDsup)
      have h2 : |f i (w i) - f i (v i)| ≤ L * |w i - v i| := hf i (w i) (v i)
      exact add_le_add h1 h2
    _ ≤ Dsup D * ((2 * (Fintype.card ι : ℝ) - 1) * dist w v) +
        L * dist w v := by
      have hL : 0 ≤ L := by
        have h := hf i (0:ℝ) 1
        have hone : |(0:ℝ) - 1| = 1 := by norm_num
        rw [hone] at h
        have h2 : L * 1 = L := by ring
        rw [h2] at h
        exact le_trans (abs_nonneg _) h
      have h3 : |w i - v i| ≤ dist w v := dist_le_pi_dist w v i
      exact add_le_add_right (mul_le_mul_of_nonneg_left h3 hL) _
    _ = (diffusionLipschitzConst D + L) * dist w v := by
      simp only [diffusionLipschitzConst]
      ring
    _ ≤ (max (0:ℝ) (L + diffusionLipschitzConst D)) * dist w v := by
      have hnonneg : (0:ℝ) ≤ L + diffusionLipschitzConst D := by
        have h1 : (0:ℝ) ≤ L := le_trans (by rfl) (by
          have hh := hf i (0:ℝ) 1
          have hone : |(0:ℝ) - 1| = 1 := by norm_num
          rw [hone] at hh
          have h2 : L * 1 = L := by ring
          rw [h2] at hh
          exact le_trans (abs_nonneg _) hh)
        have h2 : (0:ℝ) ≤ diffusionLipschitzConst D := by
          dsimp [diffusionLipschitzConst, Dsup]
          obtain ⟨j⟩ := (inferInstance : Nonempty ι)
          have hDsup : (0:ℝ) ≤ Finset.sup' Finset.univ (Finset.univ_nonempty)
              (fun j : ι => |D j|) := by
            exact le_trans (abs_nonneg (D j))
              (Finset.le_sup' (fun j : ι => |D j|) (Finset.mem_univ j))
          have hn : (0:ℝ) ≤ 2 * (Fintype.card ι : ℝ) - 1 := by
            have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
              exact_mod_cast (Nat.succ_le_of_lt Fintype.card_pos)
            nlinarith [hcard1]
          exact mul_nonneg hDsup hn
        linarith
      have hmax : (max (0:ℝ) (L + diffusionLipschitzConst D)) = L + diffusionLipschitzConst D :=
        max_eq_right hnonneg
      rw [hmax]
      rw [add_comm]
    _ ≤ ↑K * dist w v := by
      have h1 : (↑K : ℝ) = max (0:ℝ) (L + diffusionLipschitzConst D) := by
        dsimp [K]
        exact Real.coe_toNNReal _ (le_max_left _ _)
      rw [h1]

/-! ## 2. Well-posedness (method of lines) -/

/-- **Local existence for the semidiscrete reaction–diffusion ODE.** For a globally Lipschitz
reaction term `f` there is `ε > 0` and a solution of `ẋ = D Δ_h x + f(x)` through `x₀` on
`(-ε, ε)`.  (Global existence follows from the standard continuation argument from the linear
growth bound implied by global Lipschitzness; the local statement is what is formalized here.) -/
theorem exists_reactionDiffusion_solution
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hf : ∀ i x y, |f i x - f i y| ≤ L * |x - y|)
    (x₀ : ι → ℝ) [Nonempty ι] :
    ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → (ι → ℝ),
      γ 0 = x₀ ∧ ∀ t ∈ Set.Ioo (-ε) ε,
        HasDerivAt γ (reactionDiffusionField D f (γ t)) t := by
  let Kreal := L + diffusionLipschitzConst D
  have hKreal : 0 ≤ Kreal := by
    dsimp [Kreal]
    have hconst : 0 ≤ diffusionLipschitzConst D := by
      dsimp [diffusionLipschitzConst, Dsup]
      have hDsup : (0:ℝ) ≤ Finset.sup' Finset.univ (Finset.univ_nonempty)
          (fun i : ι => |D i|) := by
        obtain ⟨i⟩ := (inferInstance : Nonempty ι)
        exact le_trans (abs_nonneg (D i))
          (Finset.le_sup' (fun i : ι => |D i|) (Finset.mem_univ i))
      have hn : (0:ℝ) ≤ 2 * (Fintype.card ι : ℝ) - 1 := by
        have hcard1 : (1 : ℝ) ≤ (Fintype.card ι : ℝ) := by
          have hcard0 : (1:ℕ) ≤ Fintype.card ι := Fintype.card_pos_iff.mpr (inferInstance)
          exact_mod_cast hcard0
        nlinarith [hcard1]
      exact mul_nonneg hDsup hn
    linarith
  let Knn : NNReal := Real.toNNReal Kreal
  have hKnn_eq : Knn = Real.toNNReal (max (0:ℝ) (L + diffusionLipschitzConst D)) := by
    dsimp [Knn]
    have hKreal' : 0 ≤ L + diffusionLipschitzConst D := by simpa [Kreal] using hKreal
    rw [show Kreal = L + diffusionLipschitzConst D from rfl]
    congr 1
    exact (max_eq_right hKreal').symm
  have hlipF : LipschitzWith Knn (reactionDiffusionField D f) := by
    rw [hKnn_eq]
    exact reactionDiffusionField_lipschitz D f L hf
  let C : ℝ := ‖reactionDiffusionField D f 0‖ + Kreal
  have hCnn : 0 ≤ C := by
    dsimp [C]
    have hn := norm_nonneg (reactionDiffusionField D f 0)
    linarith [hn, hKreal]
  let Lb : NNReal := Real.toNNReal (C * (1 + (‖x₀‖ + 1)))
  have hLb : (0:ℝ) ≤ ↑Lb := by
    have h : (0:ℝ) ≤ C * (1 + (‖x₀‖ + 1)) := by
      have h2 : (0:ℝ) ≤ 1 + (‖x₀‖ + 1) := by positivity
      exact mul_nonneg hCnn h2
    have hco := Real.coe_toNNReal (C * (1 + (‖x₀‖ + 1))) h
    simp [Lb, hco, h]
  let ε : ℝ := 1 / (2 * (↑Lb + 1))
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  refine ⟨ε, hεpos, ?_⟩
  have hiso : IsPicardLindelof (fun _ : ℝ => reactionDiffusionField D f)
      (⟨0, by constructor <;> linarith [hεpos]⟩ : Set.Icc (-ε) ε) x₀ 1 0 Lb Knn := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht; exact hlipF.lipschitzOnWith
    · intro x hx; exact continuousOn_const
    · intro t ht x hx
      have hxnorm : ‖x‖ ≤ ‖x₀‖ + 1 := by
        have hmem := Metric.mem_closedBall.mp hx
        rw [dist_eq_norm_sub] at hmem
        have hmem' : ‖x - x₀‖ ≤ (1:ℝ) := by simpa using hmem
        calc ‖x‖ = ‖x - x₀ + x₀‖ := by rw [sub_add_cancel]
          _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
          _ ≤ ‖x₀‖ + 1 := by
            have hle : ‖x₀‖ + ‖x - x₀‖ ≤ ‖x₀‖ + 1 := add_le_add_right hmem' _
            have hcomm : ‖x - x₀‖ + ‖x₀‖ = ‖x₀‖ + ‖x - x₀‖ := add_comm _ _
            rw [hcomm]
            exact hle
      have hFx : ‖reactionDiffusionField D f x‖ ≤ C * (1 + ‖x‖) := by
        have hKnn_coe : (↑Knn : ℝ) = Kreal := by
          dsimp [Knn]
          exact Real.coe_toNNReal _ hKreal
        have h1 : ‖reactionDiffusionField D f x - reactionDiffusionField D f 0‖ ≤ Kreal * ‖x‖ := by
          have hdist := hlipF.dist_le_mul x 0
          rw [hKnn_coe] at hdist
          simp only [dist_eq_norm_sub, sub_zero] at hdist
          exact hdist
        have h2 : ‖reactionDiffusionField D f x‖
            ≤ ‖reactionDiffusionField D f 0‖
              + ‖reactionDiffusionField D f x - reactionDiffusionField D f 0‖ := by
          have h := norm_add_le (reactionDiffusionField D f x - reactionDiffusionField D f 0)
            (reactionDiffusionField D f 0)
          rw [sub_add_cancel] at h
          simpa [add_comm] using h
        have h3 : ‖reactionDiffusionField D f 0‖ + Kreal * ‖x‖
            ≤ (‖reactionDiffusionField D f 0‖ + Kreal) * (1 + ‖x‖) := by
          have hmul : Kreal * ‖x‖ ≤ Kreal * (1 + ‖x‖) := by
            have h1 : ‖x‖ ≤ 1 + ‖x‖ := by linarith [norm_nonneg x]
            exact mul_le_mul_of_nonneg_left h1 hKreal
          calc ‖reactionDiffusionField D f 0‖ + Kreal * ‖x‖
              ≤ ‖reactionDiffusionField D f 0‖ + Kreal * (1 + ‖x‖) :=
                add_le_add_right hmul _
            _ ≤ (‖reactionDiffusionField D f 0‖ + Kreal) * (1 + ‖x‖) := by
              have hnonneg : (0:ℝ) ≤ ‖reactionDiffusionField D f 0‖ * ‖x‖ :=
                mul_nonneg (norm_nonneg _) (norm_nonneg _)
              nlinarith [hnonneg]
        calc ‖reactionDiffusionField D f x‖
            ≤ ‖reactionDiffusionField D f 0‖
              + ‖reactionDiffusionField D f x - reactionDiffusionField D f 0‖ := h2
          _ ≤ ‖reactionDiffusionField D f 0‖ + Kreal * ‖x‖ := by
            linarith [h1]
          _ ≤ C * (1 + ‖x‖) := by dsimp [C]; exact h3
      have hbound : C * (1 + ‖x‖) ≤ ↑Lb := by
        have h1 : 1 + ‖x‖ ≤ 1 + (‖x₀‖ + 1) := by linarith [hxnorm]
        have h2 : C * (1 + (‖x₀‖ + 1)) = ↑Lb := by
          have hco := Real.coe_toNNReal (C * (1 + (‖x₀‖ + 1))) (by
            have h2 : (0:ℝ) ≤ 1 + (‖x₀‖ + 1) := by positivity
            exact mul_nonneg hCnn h2)
          simpa [Lb] using hco
        have hmul : C * (1 + ‖x‖) ≤ C * (1 + (‖x₀‖ + 1)) :=
          mul_le_mul_of_nonneg_left h1 hCnn
        rw [h2] at hmul
        exact hmul
      exact hFx.trans hbound
    · have : ↑Lb * ε ≤ 1 := by
        have hden : (0:ℝ) < 2 * (↑Lb + 1) := by nlinarith [hLb]
        have hquot : (↑Lb) / (2 * (↑Lb + 1)) ≤ 1 := by
          exact (div_le_one hden).mpr (by linarith [hLb])
        calc ↑Lb * ε = ↑Lb / (2 * (↑Lb + 1)) := by
              dsimp [ε]; field_simp
            _ ≤ 1 := hquot
      simpa [max_eq_left (by linarith [hεpos] : 0 ≤ ε)] using this
  obtain ⟨γ, hγ0, hγd⟩ :=
    IsPicardLindelof.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ hiso
  refine ⟨γ, hγ0, fun t ht => ?_⟩
  have htIcc : t ∈ Set.Icc (-ε) ε := Set.Ioo_subset_Icc_self ht
  have hder : HasDerivWithinAt γ (reactionDiffusionField D f (γ t)) (Set.Icc (-ε) ε) t :=
    hγd t htIcc
  exact hder.hasDerivAt (Icc_mem_nhds ht.1 ht.2)

/-! ## 3. Linearization and Jacobian -/

/-- The matrix of the box Laplacian on the complete graph: the off-diagonal entries are `1`
and the diagonal entries are `1 - |ι|`.  The matrix form acts exactly like the operator
`laplacian`, see `laplacianMatrix_mulVec`. -/
noncomputable def laplacianMatrix : Matrix ι ι ℝ :=
  fun i j => if i = j then (1 - (Fintype.card ι : ℝ)) else (1 : ℝ)

/-- **The matrix form of the box Laplacian.**  `(laplacianMatrix.mulVec w) i = ∑_j (w j - w i)`,
i.e. the matrix is the matrix of the operator `laplacian`. -/
theorem laplacianMatrix_mulVec (w : ι → ℝ) :
    laplacianMatrix.mulVec w = laplacian ι w := by
  funext i
  have hL : laplacianMatrix.mulVec w i
      = ∑ j, (if i = j then (1 - (Fintype.card ι : ℝ)) else (1:ℝ)) * w j := rfl
  have hR : laplacian ι w i = ∑ j, (w j - w i) := rfl
  rw [hL, hR]
  have hmain : (∑ j, (if i = j then (1 - (Fintype.card ι : ℝ)) else (1:ℝ)) * w j)
      = (∑ j, w j) - ∑ j, (if i = j then (Fintype.card ι : ℝ) else 0) * w j := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    by_cases h : i = j
    · simp [h]
      ring
    · simp [h]
  have hdelta : (∑ j, (if i = j then (Fintype.card ι : ℝ) else 0) * w j)
      = (Fintype.card ι : ℝ) * w i := by
    have h' : (∑ j, (if i = j then (Fintype.card ι : ℝ) else 0) * w j)
        = ∑ j, (if j = i then (Fintype.card ι : ℝ) * w j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j
      · subst h
        simp
      · have h2 : j ≠ i := Ne.symm h
        simp [h, h2]
    rw [h']
    rw [Finset.sum_ite_eq' Finset.univ i (fun j => (Fintype.card ι : ℝ) * w j)]
    simp
  have hR2 : (∑ j, (w j - w i)) = (∑ j, w j) - (Fintype.card ι : ℝ) * w i := by
    rw [Finset.sum_sub_distrib]
    simp [Finset.sum_const, Finset.card_univ]
  rw [hmain, hdelta]
  exact hR2.symm

/-- The matrix of the diffusion operator: the row `i` of the Laplacian is scaled by `D i`. -/
noncomputable def diffusionMatrix (D : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => D i * laplacianMatrix i j

/-- The diffusion part of the semidiscrete field, in matrix form. -/
theorem diffusionMatrix_mulVec (D : ι → ℝ) (w : ι → ℝ) :
    (diffusionMatrix D).mulVec w = fun i => D i * laplacian ι w i := by
  funext i
  have hsplit : (diffusionMatrix D).mulVec w i
      = ∑ j, (D i * laplacianMatrix i j) * w j := rfl
  rw [hsplit]
  have hA : (∑ j, (D i * laplacianMatrix i j) * w j)
      = D i * (∑ j, laplacianMatrix i j * w j) := by
    have hre : (∑ j, (D i * laplacianMatrix i j) * w j)
        = ∑ j, D i * (laplacianMatrix i j * w j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hre, Finset.mul_sum]
  have hL : (∑ j, laplacianMatrix i j * w j) = laplacian ι w i := by
    have h := congrArg (fun g : ι → ℝ => g i) (laplacianMatrix_mulVec w)
    have h2 : (laplacianMatrix.mulVec w) i = ∑ j, laplacianMatrix i j * w j := rfl
    rw [h2] at h
    exact h
  rw [hA, hL]

/-- **The reaction Jacobian** of a *decoupled* reaction term `f i (x i)`: it is the diagonal
matrix with entries `df i`, where `df i` is the derivative of the reaction rate of species
`i` at the steady state.  (For a coupled reaction term the Jacobian is not diagonal; the
Brusselator of Section 5 is an example.) -/
noncomputable def reactionJacobian (df : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if i = j then df i else 0

/-- **The semidiscrete Jacobian** `D Δ_h + Df`: the diffusion matrix plus the reaction
Jacobian. -/
noncomputable def reactionDiffusionJacobian (D : ι → ℝ) (df : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => D i * laplacianMatrix i j + (if i = j then df i else 0)

/-- **The semidiscrete Jacobian is the sum of the diffusion matrix and the reaction
Jacobian.** -/
theorem reactionDiffusionJacobian_add (D : ι → ℝ) (df : ι → ℝ) :
    reactionDiffusionJacobian D df = diffusionMatrix D + reactionJacobian df := by
  ext i j
  simp [reactionDiffusionJacobian, diffusionMatrix, reactionJacobian, Matrix.add_apply]

/-- **The action of the semidiscrete Jacobian** on a direction `v` is
`D i * (Δ v) i + Df(x*) i * v i`. -/
theorem reactionDiffusionJacobian_mulVec (D : ι → ℝ) (df : ι → ℝ) (v : ι → ℝ) :
    (reactionDiffusionJacobian D df).mulVec v = fun i => D i * laplacian ι v i + df i * v i := by
  funext i
  have hsplit : (reactionDiffusionJacobian D df).mulVec v i
      = ∑ j, (D i * laplacianMatrix i j + (if i = j then df i else 0)) * v j := rfl
  rw [hsplit]
  have hmain : (∑ j, (D i * laplacianMatrix i j + (if i = j then df i else 0)) * v j)
      = ∑ j, (D i * laplacianMatrix i j * v j + (if i = j then df i else 0) * v j) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hmain, Finset.sum_add_distrib]
  have hA : (∑ j, D i * laplacianMatrix i j * v j)
      = D i * (∑ j, laplacianMatrix i j * v j) := by
    have hre : (∑ j, D i * laplacianMatrix i j * v j)
        = ∑ j, D i * (laplacianMatrix i j * v j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hre, Finset.mul_sum]
  have hB : (∑ j, (if i = j then df i else 0) * v j) = df i * v i := by
    have h' : (∑ j, (if i = j then df i else 0) * v j)
        = ∑ j, (if j = i then df i * v j else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases h : i = j
      · subst h
        simp
      · have h2 : j ≠ i := Ne.symm h
        simp [h, h2]
    rw [h']
    rw [Finset.sum_ite_eq' Finset.univ i (fun j => df i * v j)]
    simp
  have hL : (∑ j, laplacianMatrix i j * v j) = laplacian ι v i := by
    have h := congrArg (fun g : ι → ℝ => g i) (laplacianMatrix_mulVec v)
    have h2 : (laplacianMatrix.mulVec v) i = ∑ j, laplacianMatrix i j * v j := rfl
    rw [h2] at h
    exact h
  rw [hA, hB, hL]

/-- **Variational (one-dimensional curve) derivative statement.**  Along the curve
`wstar + t v` the field differentiates to `D Δ_h v + Df(x*) v`, i.e. to the action of the
semidiscrete Jacobian `reactionDiffusionJacobian` on the direction `v`. -/
theorem reactionDiffusionField_hasDerivAt_curve
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (df : ι → ℝ)
    (wstar v : ι → ℝ)
    (hf : ∀ i, HasDerivAt (f i) (df i) (wstar i)) :
    HasDerivAt (fun t : ℝ => reactionDiffusionField D f (fun i => wstar i + t * v i))
      (fun i => D i * laplacian ι v i + df i * v i) 0 := by
  have hcomp : ∀ i,
      HasDerivAt (fun t => reactionDiffusionField D f (fun i => wstar i + t * v i) i)
        (D i * laplacian ι v i + df i * v i) 0 := by
    intro i
    have hlap : HasDerivAt (fun t => laplacian ι (fun i => wstar i + t * v i) i)
        (laplacian ι v i) 0 := by
      have haff : (fun t => laplacian ι (fun i => wstar i + t * v i) i) =
          (fun t => laplacian ι wstar i + t * laplacian ι v i) := by
        funext t
        have h1 : (fun i => wstar i + t * v i) = wstar + t • v := by
          funext j; simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        rw [h1, laplacian_add, laplacian_smul]
        simp
      rw [haff]
      have : HasDerivAt (fun t : ℝ => laplacian ι wstar i + t * laplacian ι v i)
          (laplacian ι v i) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => t * laplacian ι v i) (laplacian ι v i) 0 := by
          simpa using (hasDerivAt_id 0).mul_const (laplacian ι v i)
        simpa only [add_comm] using h1.add_const (laplacian ι wstar i)
      exact this
    have hD : HasDerivAt (fun t => D i * laplacian ι (fun i => wstar i + t * v i) i)
        (D i * laplacian ι v i) 0 :=
      hlap.const_mul (D i)
    have hfpart : HasDerivAt (fun t => f i (wstar i + t * v i))
        (df i * v i) 0 := by
      have hinner : HasDerivAt (fun t : ℝ => wstar i + t * v i) (v i) 0 := by
        have h := (hasDerivAt_id 0).mul_const (v i)
        simpa using h.const_add (wstar i)
      have hfi : HasDerivAt (f i) (df i) (wstar i + 0 * v i) := by
        (convert hf i using 1; simp)
      have hcomp : HasDerivAt ((f i) ∘ (fun t : ℝ => wstar i + t * v i))
          (df i * v i) 0 := HasDerivAt.comp 0 hfi hinner
      have hcomp' : HasDerivAt (fun t => f i (wstar i + t * v i))
          (df i * v i) 0 := by
        convert hcomp using 1
        funext t; rfl
      exact hcomp'
    have hsum : HasDerivAt (fun t => D i * laplacian ι (fun i => wstar i + t * v i) i +
        f i (wstar i + t * v i))
        (D i * laplacian ι v i + df i * v i) 0 :=
      hD.add hfpart
    have hrew : (fun t => reactionDiffusionField D f (fun i => wstar i + t * v i) i) =
        (fun t => D i * laplacian ι (fun i => wstar i + t * v i) i + f i (wstar i + t * v i)) := by
      funext t
      simp [reactionDiffusionField]
    rw [hrew]
    exact hsum
  exact (hasDerivAt_pi).mpr hcomp

/-- **The semidiscrete Jacobian is the linearization of the field.**  The derivative of the
field along the curve `wstar + t v` is the action of `reactionDiffusionJacobian` on `v`. -/
theorem reactionDiffusionField_hasDerivAt_curve_matrix
    (D : ι → ℝ) (f : ι → ℝ → ℝ) (df : ι → ℝ)
    (wstar v : ι → ℝ)
    (hf : ∀ i, HasDerivAt (f i) (df i) (wstar i)) :
    HasDerivAt (fun t : ℝ => reactionDiffusionField D f (fun i => wstar i + t * v i))
      ((reactionDiffusionJacobian D df).mulVec v) 0 := by
  have h := reactionDiffusionField_hasDerivAt_curve D f df wstar v hf
  rw [← reactionDiffusionJacobian_mulVec] at h
  exact h

/-! ## 4. Relation to Turing analysis -/

/-- **The mode matrix of the linearized two-species system.**  For the reaction Jacobian
`J = [[a, b], [c, d]]` and *diagonal species diffusion* `D = diag(d₁, d₂)` the linearization
of the semidiscrete system is `J + D`, and the mode with wavenumber `q` is represented by
the matrix `J - q D`, i.e. by `modeMatrix a b c d d₁ d₂ q`.  (This is the diffusion model
of `CRNT.Turing`; it is *not* the box Laplacian of Section 1, which couples the sites of
the grid rather than the species.) -/
def modeMatrix (a b c d d₁ d₂ q : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![a - d₁ * q, b; c, d - d₂ * q]

/-- The trace of the mode matrix `J - q D` is `a + d - (d₁ + d₂) q`. -/
theorem modeMatrix_trace (a b c d d₁ d₂ q : ℝ) :
    (modeMatrix a b c d d₁ d₂ q).trace = a + d - (d₁ + d₂) * q := by
  rw [Matrix.trace_fin_two]
  simp [modeMatrix]
  ring

/-- The determinant of the mode matrix `J - q D` is `modeDet a b c d d₁ d₂ q`. -/
theorem modeMatrix_det (a b c d d₁ d₂ q : ℝ) :
    (modeMatrix a b c d d₁ d₂ q).det = modeDet a b c d d₁ d₂ q := by
  rw [Matrix.det_fin_two]
  simp [modeMatrix, modeDet]

/-- **The mode matrix and the Hurwitz criterion.**  For a reaction-stable two-species
system (`a + d < 0`) the `q`-mode `J - q D` is Hurwitz exactly when its determinant is
positive; this is the statement of `CRNT.Turing.mode_hurwitz_iff` in matrix form. -/
theorem modeMatrix_hurwitz_iff (a b c d d₁ d₂ q : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hq : 0 ≤ q) (htr : a + d < 0) :
    IsHurwitz (charPoly (a - d₁ * q) b c (d - d₂ * q)) ↔
      0 < (modeMatrix a b c d d₁ d₂ q).det := by
  rw [modeMatrix_det]
  exact mode_hurwitz_iff hd₁ hd₂ hq htr

/-- **Turing's criterion for the semidiscrete two-species system.**  The linearized system
with reaction Jacobian `[[a, b], [c, d]]` and diagonal species diffusion `diag(d₁, d₂)`
admits an unstable mode — a mode matrix `J - q D` with negative determinant, hence a
positive real eigenvalue — for some `q ≥ 0` if and only if
`d₂ a + d₁ d > 0` and `(d₂ a + d₁ d)² > 4 d₁ d₂ det J`.  This is
`CRNT.Turing.diffusionDrivenInstability_iff`, restated in the notation of this module. -/
theorem turing_connection (a b c d d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hdet : 0 < a * d - b * c) :
    (∃ q : ℝ, 0 ≤ q ∧ modeDet a b c d d₁ d₂ q < 0) ↔
      0 < d₂ * a + d₁ * d ∧ 4 * d₁ * d₂ * (a * d - b * c) < (d₂ * a + d₁ * d) ^ 2 := by
  exact diffusionDrivenInstability_iff hd₁ hd₂ hdet

/-- **Equal diffusivities rule out Turing instability.**  If the two species diffuse with
the same coefficient `δ`, no mode of the linearization is unstable. -/
theorem turing_equal_diffusion_stable (a b c d δ : ℝ) (hδ : 0 < δ)
    (hstable : IsHurwitz (charPoly a b c d)) (q : ℝ) (hq : 0 ≤ q) :
    IsHurwitz (charPoly (a - δ * q) b c (d - δ * q)) :=
  no_instability_of_equal_diffusion hδ hstable q hq

/-! ## 5. A concrete instance: the two-species Brusselator -/

/-- The Brusselator species: `0 = X` (the activator) and `1 = Y` (the inhibitor). -/
abbrev BrSpecies := Fin 2

/-- The four Brusselator reaction channels. -/
abbrev BrRxn := Fin 4

/-- **The Brusselator reaction network.**  The four channels are `A → X`, `2X + Y → 3X`,
`B + X → Y` and `X → E`.  The feed species `A, B` and the product species `D, E` are held
constant, so they are not part of the state; their values are the rate constants of the
channels `0` and `2` (see `brusselatorRateConstants`). -/
def brusselatorReaction : BrRxn → Reaction BrSpecies :=
  fun r => match r with
  | 0 => { source := Complex.zero, target := ![1, 0] }          -- A → X
  | 1 => { source := ![2,  1], target := ![3, 0] }            -- 2X + Y → 3X
  | 2 => { source := ![1,  0], target := ![0, 1] }            -- B + X → Y
  | 3 => { source := ![1,  0], target := Complex.zero }       -- X → E

/-- The Brusselator network. -/
def brusselatorNetwork : Network BrSpecies :=
  { R := BrRxn, decEqR := inferInstance, fintypeR := inferInstance,
    reaction := brusselatorReaction }

/-- **The rate constant of the Brusselator channel `r`.**  The feed `A` drives the channel
`0`, the autocatalytic channel `1` and the decay channel `3` have rate `1`, and the feed `B`
drives the channel `2`. -/
def brusselatorRate (A B : ℝ) : BrRxn → ℝ :=
  fun r => match r with
  | 0 => A
  | 1 => 1
  | 2 => B
  | 3 => 1

/-- The rate constants of the Brusselator are positive. -/
theorem brusselatorRate_pos (A B : ℝ) (hA : 0 < A) (hB : 0 < B) (r : BrRxn) :
    0 < brusselatorRate A B r := by
  fin_cases r
  · exact hA
  · simp [brusselatorRate]
  · exact hB
  · simp [brusselatorRate]

/-- **The rate constants of the Brusselator.** -/
def brusselatorRateConstants (A B : ℝ) (hA : 0 < A) (hB : 0 < B) :
    (brusselatorNetwork : Network BrSpecies).RateConstants where
  k := fun r => brusselatorRate A B r
  positive := fun r => brusselatorRate_pos A B hA hB r

/-- **The Brusselator reaction term.**  For the state `w = (x, y)` the reaction rates are
`A - (B+1) x + x² y` for the activator `X` and `B x - x² y` for the inhibitor `Y`. -/
def brusselatorReactionTerm (A B : ℝ) (w : BrSpecies → ℝ) : BrSpecies → ℝ :=
  fun i => match i with
  | 0 => A - (B + 1) * w 0 + w 0 ^ 2 * w 1
  | 1 => B * w 0 - w 0 ^ 2 * w 1

/-- **The mass-action vector field of the Brusselator network is the Brusselator reaction
term.**  With the rate constants `(A, 1, B, 1)` the network induces the reaction rates
`ẋ = A - (B+1) x + x² y` and `ẏ = B x - x² y`. -/
theorem brusselator_massActionVectorField (A B : ℝ) (hA : 0 < A) (hB : 0 < B)
    (w : BrSpecies → ℝ) :
    brusselatorNetwork.massActionVectorField (brusselatorRateConstants A B hA hB) w
      = brusselatorReactionTerm A B w := by
  unfold brusselatorNetwork
  funext s
  fin_cases s
  · simp [Network.massActionVectorField, Network.massActionRate,
      brusselatorReaction, brusselatorRate, brusselatorRateConstants,
      Network.reactionVector_apply, Complex.massActionMonomial, brusselatorReactionTerm,
      Fin.sum_univ_four, Fin.prod_univ_two]
    ring
  · simp [Network.massActionVectorField, Network.massActionRate,
      brusselatorReaction, brusselatorRate, brusselatorRateConstants,
      Network.reactionVector_apply, Complex.massActionMonomial, brusselatorReactionTerm,
      Fin.sum_univ_four, Fin.prod_univ_two]
    ring

/-- The Brusselator steady state `(x, y) = (A, B/A)`. -/
noncomputable def brusselatorSteady (A B : ℝ) : BrSpecies → ℝ :=
  fun i => match i with
  | 0 => A
  | 1 => B / A

/-- **The Brusselator steady state is an equilibrium of the reaction term.** -/
theorem brusselator_steady_equilibrium (A B : ℝ) (_hA : A ≠ 0) :
    brusselatorReactionTerm A B (brusselatorSteady A B) = 0 := by
  funext i
  fin_cases i
  · simp [brusselatorReactionTerm, brusselatorSteady]
    field_simp [_hA]
    ring
  · simp [brusselatorReactionTerm, brusselatorSteady]
    field_simp [_hA]
    ring

/-- **The reaction Jacobian of the Brusselator** at the state `w = (x, y)`: the `(i, j)`-entry
is the partial derivative of the `i`-th reaction rate with respect to the `j`-th
concentration. -/
noncomputable def brusselatorJacobian (B : ℝ) (w : BrSpecies → ℝ) : Matrix BrSpecies BrSpecies ℝ :=
  !![-(B + 1) + 2 * w 0 * w 1, w 0 ^ 2;
      B - 2 * w 0 * w 1, -(w 0 ^ 2)]

/-- The derivative of a linear polynomial in `t` at `0` is its slope. -/
theorem hasDerivAt_linear (c₀ c₁ : ℝ) :
    HasDerivAt (fun t : ℝ => c₀ + c₁ * t) c₁ 0 := by
  have h0 : HasDerivAt (fun _t : ℝ => c₀) 0 0 := hasDerivAt_const 0 c₀
  have h1 : HasDerivAt (fun t : ℝ => c₁ * t) c₁ 0 := by
    simpa using (hasDerivAt_id 0).const_mul c₁
  have h := h0.add h1
  convert h using 1
  ring

/-- The derivative of a quadratic polynomial in `t` at `0` is its linear coefficient. -/
theorem hasDerivAt_quadratic (c₀ c₁ c₂ : ℝ) :
    HasDerivAt (fun t : ℝ => c₀ + (c₁ * t + c₂ * t ^ 2)) c₁ 0 := by
  have h0 : HasDerivAt (fun _t : ℝ => c₀) 0 0 := hasDerivAt_const 0 c₀
  have h1 : HasDerivAt (fun t : ℝ => c₁ * t) c₁ 0 := by
    simpa using (hasDerivAt_id 0).const_mul c₁
  have h2 : HasDerivAt (fun t : ℝ => c₂ * t ^ 2) 0 0 := by
    simpa using ((hasDerivAt_id 0).pow 2).const_mul c₂
  have h := h0.add (h1.add h2)
  convert h using 1
  ring

/-- **The partial derivatives of the Brusselator reaction rates.**  At the state
`(x, y)` the derivative of the `X`-rate with respect to `x` is `-(B+1) + 2xy`, with respect
to `y` it is `x²`; the derivative of the `Y`-rate with respect to `x` is `B - 2xy` and with
respect to `y` it is `-x²`.  These are the entries of `brusselatorJacobian`. -/
theorem brusselator_partials (A B x y : ℝ) :
    HasDerivAt (fun t : ℝ => A - (B + 1) * (x + t) + (x + t) ^ 2 * y)
      (-(B + 1) + 2 * x * y) 0 ∧
    HasDerivAt (fun t : ℝ => A - (B + 1) * x + x ^ 2 * (y + t)) (x ^ 2) 0 ∧
    HasDerivAt (fun t : ℝ => B * (x + t) - (x + t) ^ 2 * y) (B - 2 * x * y) 0 ∧
    HasDerivAt (fun t : ℝ => B * x - x ^ 2 * (y + t)) (-(x ^ 2)) 0 := by
  have h1 : (fun t : ℝ => A - (B + 1) * (x + t) + (x + t) ^ 2 * y)
      = (fun t : ℝ => (A - (B + 1) * x + x ^ 2 * y) +
          ((-(B + 1) + 2 * x * y) * t + y * t ^ 2)) := by
    funext t
    ring
  have h2 : (fun t : ℝ => A - (B + 1) * x + x ^ 2 * (y + t))
      = (fun t : ℝ => (A - (B + 1) * x + x ^ 2 * y) + x ^ 2 * t) := by
    funext t
    ring
  have h3 : (fun t : ℝ => B * (x + t) - (x + t) ^ 2 * y)
      = (fun t : ℝ => (B * x - x ^ 2 * y) + ((B - 2 * x * y) * t + (-y) * t ^ 2)) := by
    funext t
    ring
  have h4 : (fun t : ℝ => B * x - x ^ 2 * (y + t))
      = (fun t : ℝ => (B * x - x ^ 2 * y) + (-(x ^ 2)) * t) := by
    funext t
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [h1]
    exact hasDerivAt_quadratic (A - (B + 1) * x + x ^ 2 * y) (-(B + 1) + 2 * x * y) (y)
  · rw [h2]
    exact hasDerivAt_linear (A - (B + 1) * x + x ^ 2 * y) (x ^ 2)
  · rw [h3]
    exact hasDerivAt_quadratic (B * x - x ^ 2 * y) (B - 2 * x * y) (-y)
  · rw [h4]
    exact hasDerivAt_linear (B * x - x ^ 2 * y) (-(x ^ 2))

/-- **The reaction Jacobian at the Brusselator steady state** is
`[[B - 1, A²], [-B, -A²]]`. -/
theorem brusselatorJacobian_steady (A B : ℝ) (hA : A ≠ 0) :
    brusselatorJacobian B (brusselatorSteady A B) = !![B - 1, A ^ 2; -B, -(A ^ 2)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [brusselatorJacobian, brusselatorSteady] <;> field_simp <;> ring

/-- **The Turing criterion for the Brusselator.**  With reaction Jacobian
`[[B-1, A²], [-B, -A²]]` and diagonal species diffusion `diag(d₁, d₂)` (the activator `X`
diffusing with coefficient `d₁`, the inhibitor `Y` with coefficient `d₂`) the linearized
system has an unstable mode iff `d₂ (B-1) - d₁ A² > 0` and
`(d₂ (B-1) - d₁ A²)² > 4 d₁ d₂ A²`. -/
theorem brusselator_turing_criterion (A B d₁ d₂ : ℝ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hA : A ≠ 0) :
    (∃ q : ℝ, 0 ≤ q ∧ modeDet (B - 1) (A ^ 2) (-B) (-(A ^ 2)) d₁ d₂ q < 0) ↔
      0 < d₂ * (B - 1) + d₁ * (-(A ^ 2)) ∧
        4 * d₁ * d₂ * ((B - 1) * (-(A ^ 2)) - A ^ 2 * (-B))
          < (d₂ * (B - 1) + d₁ * (-(A ^ 2))) ^ 2 := by
  have hdet : 0 < (B - 1) * (-(A ^ 2)) - A ^ 2 * (-B) := by
    have h : (B - 1) * (-(A ^ 2)) - A ^ 2 * (-B) = A ^ 2 := by ring
    rw [h]
    exact sq_pos_of_ne_zero hA
  exact diffusionDrivenInstability_iff hd₁ hd₂ hdet

/-- **A Turing-unstable Brusselator.**  For `A = 3`, `B = 2` (the steady state is
`(3, 2/3)`) and the species diffusion `d₁ = 1` (the activator `X`), `d₂ = 64` (the
inhibitor `Y`) the reaction Jacobian `[[1, 9], [-2, -9]]` is Hurwitz, while the linearized
system is Turing-unstable. -/
theorem brusselator_turing_instance :
    IsHurwitz (charPoly (2 - 1) (3 ^ 2) (-2) (-(3 ^ 2))) ∧
      0 < 64 * (2 - 1) + 1 * (-(3 ^ 2)) ∧
      4 * 1 * 64 * ((2 - 1) * (-(3 ^ 2)) - 3 ^ 2 * (-2))
        < (64 * (2 - 1) + 1 * (-(3 ^ 2))) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [reaction_hurwitz_iff]
    norm_num
  · norm_num
  · norm_num

/-- **The unstable mode of the Turing-unstable Brusselator.** -/
theorem brusselator_turing_instance_unstable :
    ∃ q : ℝ, 0 ≤ q ∧ modeDet (2 - 1) (3 ^ 2) (-2) (-(3 ^ 2)) 1 64 q < 0 :=
  (diffusionDrivenInstability_iff (a := 2 - 1) (b := 3 ^ 2) (c := -2) (d := -(3 ^ 2))
    (d₁ := 1) (d₂ := 64) (by norm_num) (by norm_num) (by norm_num)).mpr
    ⟨by norm_num, by norm_num⟩

/-- **The explicit unstable wavenumber** `q = 55 / 128` of the Brusselator instance. -/
theorem brusselator_turing_instance_mode :
    modeDet (2 - 1) (3 ^ 2) (-2) (-(3 ^ 2)) 1 64 (55 / 128) < 0 := by
  norm_num [modeDet]

end ReactionDiffusion

end CRNT
