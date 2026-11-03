import CRNT.Design.GeneralPlantRPA
import CRNT.Stochastic.FirstOrderFoster
import CRNT.Stochastic.FosterLyapunov
import CRNT.Stochastic.FosterRecurrence
import CRNT.Stochastic.MinimalSemigroupNetwork
import CRNT.Stochastic.HarrisTheorem
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Conditional general-plant quadratic drift and Foster transfers

Quadratic generator identities and drift estimates are developed from supplied
shape matrices, decay, growth, and compatibility hypotheses. These yield Foster
certificates when the displayed assumptions hold. They do not construct an
antithetic closed-loop ergodicity certificate for every output-controllable
unimolecular plant. Concrete plant instances and obstruction results retain
their separate scope.
-/

open Filter
open scoped BigOperators Topology Matrix

namespace CRNT
namespace Design
namespace GeneralPlant

variable {m : ℕ}

/-! ## The quadratic Lyapunov function on the count lattice -/

/-- Multiplying a finite sum by a scalar. -/
theorem mul_sum_univ {ι : Type*} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    a * ∑ i, f i = ∑ i, a * f i :=
  Finset.mul_sum Finset.univ f a

/-- Multiplying a finite sum by a scalar on the right. -/
theorem sum_mul_univ {ι : Type*} [Fintype ι] (a : ℝ) (f : ι → ℝ) :
    (∑ i, f i) * a = ∑ i, f i * a :=
  Finset.sum_mul Finset.univ f a

/-- A constant factor can be pulled out of a finite sum. -/
theorem sum_mul_const {ι : Type*} [Fintype ι] (B : ι → ℝ) (c : ℝ) :
    (∑ r, B r * c) = (∑ r, B r) * c := by
  symm
  exact Finset.sum_mul Finset.univ B c

/-- The squared Euclidean norm of a real vector. -/
noncomputable def normSq (x : Fin m → ℝ) : ℝ :=
  ∑ i, x i ^ 2

/-- The bilinear form `xᵀ M y` associated with a real matrix `M`. -/
noncomputable def bilinear (M : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ) : ℝ :=
  ∑ i, x i * ((M *ᵥ y) i)

/-- The deviation vector `n − n*` of a count vector from the reference. -/
noncomputable def countDeviation (nStar : Fin m → ℝ) (n : Fin m → ℕ) : Fin m → ℝ :=
  fun i => (n i : ℝ) - nStar i

/-- The quadratic Lyapunov function on the count lattice,
`V n = (n − n*)ᵀ P (n − n*)`.  The shift `n*` is the reference count vector (the equilibrium
of the closed loop, in deviation coordinates). -/
noncomputable def quadObservable (P : Matrix (Fin m) (Fin m) ℝ) (nStar : Fin m → ℝ)
    (n : Fin m → ℕ) : ℝ :=
  quadForm P (countDeviation nStar n)

@[simp] theorem quadObservable_eq (P : Matrix (Fin m) (Fin m) ℝ) (nStar : Fin m → ℝ)
    (n : Fin m → ℕ) :
    quadObservable P nStar n = quadForm P (countDeviation nStar n) := rfl

/-- The quadratic form in double-sum coordinates. -/
theorem quadForm_def (M : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    quadForm M x = ∑ i, ∑ j, x i * (M i j * x j) := by
  unfold quadForm
  simp only [Matrix.mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- The bilinear form in double-sum coordinates. -/
theorem bilinear_def (M : Matrix (Fin m) (Fin m) ℝ) (x y : Fin m → ℝ) :
    bilinear M x y = ∑ i, ∑ j, x i * (M i j * y j) := by
  unfold bilinear
  simp only [Matrix.mulVec_apply_eq_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-- The quadratic form is the bilinear form applied to itself. -/
theorem quadForm_eq_bilinear (M : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ) :
    quadForm M x = bilinear M x x := by
  rw [quadForm_def, bilinear_def]

/-- **Pair swap.**  Summing a two-index function over the product of two identical finite
types does not depend on the order of the two indices. -/
theorem sum_pair_swap (g : Fin m → Fin m → ℝ) :
    (∑ i, ∑ j, g i j) = ∑ i, ∑ j, g j i := by
  calc
    (∑ i, ∑ j, g i j) = ∑ j, ∑ i, g i j := Finset.sum_comm
    _ = ∑ i, ∑ j, g j i := rfl

/-- Symmetry of the double-sum form of the bilinear form of a symmetric matrix. -/
theorem bilinear_sum_comm {M : Matrix (Fin m) (Fin m) ℝ} (hM : Mᵀ = M) (x y : Fin m → ℝ) :
    (∑ i, ∑ j, x i * (M i j * y j)) = ∑ i, ∑ j, y i * (M i j * x j) := by
  have hsym : ∀ i j, M i j = M j i := by
    intro i j
    have h := Matrix.transpose_apply M j i
    rw [hM] at h
    exact h.symm
  have hswap : (∑ i, ∑ j, x i * (M i j * y j)) = ∑ i, ∑ j, x j * (M j i * y i) :=
    sum_pair_swap (fun i j => x i * (M i j * y j))
  rw [hswap]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hsym i j]
  ring

/-- A symmetric matrix has a symmetric bilinear form. -/
theorem bilinear_comm {M : Matrix (Fin m) (Fin m) ℝ} (hM : Mᵀ = M) (x y : Fin m → ℝ) :
    bilinear M x y = bilinear M y x := by
  rw [bilinear_def, bilinear_def]
  exact bilinear_sum_comm hM x y

/-- The quadratic form of a symmetric matrix expands as
`quadForm P (x + d) = quadForm P x + 2 bilinear P x d + quadForm P d`. -/
theorem quadForm_add {M : Matrix (Fin m) (Fin m) ℝ} (hM : Mᵀ = M) (x d : Fin m → ℝ) :
    quadForm M (x + d) = quadForm M x + 2 * bilinear M x d + quadForm M d := by
  have key : ∀ (i j : Fin m),
      (x i + d i) * (M i j * (x j + d j)) =
        (x i * (M i j * x j)) + (x i * (M i j * d j)) + (d i * (M i j * x j)) +
          (d i * (M i j * d j)) := by
    intro i j
    ring
  have hexp : quadForm M (x + d) =
      ∑ i, ∑ j, (x i + d i) * (M i j * (x j + d j)) := by
    rw [quadForm_def]
    simp only [Pi.add_apply]
  have hinner : ∀ i, (∑ j, (x i + d i) * (M i j * (x j + d j))) =
      (∑ j, x i * (M i j * x j)) + (∑ j, x i * (M i j * d j)) +
        (∑ j, d i * (M i j * x j)) + (∑ j, d i * (M i j * d j)) := by
    intro i
    have h1 : (∑ j, (x i + d i) * (M i j * (x j + d j))) =
        ∑ j, ((x i * (M i j * x j)) + (x i * (M i j * d j)) +
          (d i * (M i j * x j)) + (d i * (M i j * d j))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [key]
    rw [h1]
    simp only [Finset.sum_add_distrib]
  have hsplit : (∑ i, ∑ j, (x i + d i) * (M i j * (x j + d j))) =
      (∑ i, ∑ j, x i * (M i j * x j)) + (∑ i, ∑ j, x i * (M i j * d j)) +
        (∑ i, ∑ j, d i * (M i j * x j)) + (∑ i, ∑ j, d i * (M i j * d j)) := by
    calc
      (∑ i, ∑ j, (x i + d i) * (M i j * (x j + d j)))
          = ∑ i, ((∑ j, x i * (M i j * x j)) + (∑ j, x i * (M i j * d j)) +
              (∑ j, d i * (M i j * x j)) + (∑ j, d i * (M i j * d j))) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            exact hinner i
      _ = (∑ i, ∑ j, x i * (M i j * x j)) + (∑ i, ∑ j, x i * (M i j * d j)) +
          (∑ i, ∑ j, d i * (M i j * x j)) + (∑ i, ∑ j, d i * (M i j * d j)) := by
            simp only [Finset.sum_add_distrib]
  rw [hexp, hsplit, quadForm_def, bilinear_def, quadForm_def]
  have h3 : (∑ i, ∑ j, d i * (M i j * x j)) = ∑ i, ∑ j, x i * (M i j * d j) :=
    bilinear_sum_comm hM d x
  rw [h3]
  ring

/-- The bilinear form is linear in its second argument. -/
theorem bilinear_sum_right (M : Matrix (Fin m) (Fin m) ℝ) (x : Fin m → ℝ)
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (d : ι → Fin m → ℝ) :
    bilinear M x (fun i => ∑ k, c k * d k i) = ∑ k, c k * bilinear M x (d k) := by
  have hmul : ∀ (i : Fin m),
      (M *ᵥ (fun i => ∑ k, c k * d k i)) i = ∑ k, c k * ((M *ᵥ (d k)) i) := by
    intro i
    have h1 : (∑ j, M i j * (∑ k, c k * d k j)) = ∑ j, ∑ k, M i j * (c k * d k j) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      exact mul_sum_univ (M i j) (fun k => c k * d k j)
    rw [Matrix.mulVec_apply_eq_sum, h1]
    calc
      (∑ j, ∑ k, M i j * (c k * d k j)) = ∑ k, ∑ j, M i j * (c k * d k j) := by
        rw [Finset.sum_comm]
      _ = ∑ k, c k * (∑ j, M i j * d k j) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        have h1 : (∑ j, M i j * (c k * d k j)) = c k * (∑ j, M i j * d k j) := by
          have h2 : (∑ j, M i j * (c k * d k j)) = ∑ j, c k * (M i j * d k j) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          rw [h2, ← mul_sum_univ (c k) (fun j => M i j * d k j)]
        rw [h1]
      _ = ∑ k, c k * ((M *ᵥ (d k)) i) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mulVec_apply_eq_sum]
  unfold bilinear
  calc
    (∑ i, x i * ((M *ᵥ (fun i => ∑ k, c k * d k i)) i))
      = ∑ i, x i * (∑ k, c k * ((M *ᵥ (d k)) i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hmul i]
    _ = ∑ i, ∑ k, x i * (c k * ((M *ᵥ (d k)) i)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h1 : x i * (∑ k, c k * ((M *ᵥ (d k)) i)) = ∑ k, x i * (c k * ((M *ᵥ (d k)) i)) :=
            mul_sum_univ (x i) (fun k => c k * ((M *ᵥ (d k)) i))
          rw [h1]
    _ = ∑ k, ∑ i, x i * (c k * ((M *ᵥ (d k)) i)) := by
          rw [Finset.sum_comm]
    _ = ∑ k, c k * (∑ i, x i * ((M *ᵥ (d k)) i)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have h1 : (∑ i, x i * (c k * ((M *ᵥ (d k)) i))) = c k * (∑ i, x i * ((M *ᵥ (d k)) i)) := by
            have h2 : (∑ i, x i * (c k * ((M *ᵥ (d k)) i))) =
                ∑ i, c k * (x i * ((M *ᵥ (d k)) i)) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              ring
            rw [h2, ← mul_sum_univ (c k) (fun i => x i * ((M *ᵥ (d k)) i))]
          rw [h1]

/-! ## The exact drift identity -/

/-- The drift vector of the counting process: `∑_r λ_r(n) Δ_r`, the expected increment of the
count vector in one jump. -/
noncomputable def countDrift (N : Network (Fin m)) (κ : N.RateConstants) (n : Fin m → ℕ) :
    Fin m → ℝ :=
  fun i => ∑ r : N.R, N.stochasticMassActionRate κ n r * N.reactionVector r i

/-- The quadratic remainder in the drift of a quadratic Lyapunov function:
`∑_r λ_r(n) (Δ_rᵀ P Δ_r)`.  It is the discrete second-order correction which the continuous
Lie derivative does not see. -/
noncomputable def quadRemainder (N : Network (Fin m)) (κ : N.RateConstants)
    (P : Matrix (Fin m) (Fin m) ℝ) (n : Fin m → ℕ) : ℝ :=
  ∑ r : N.R, N.stochasticMassActionRate κ n r *
    bilinear P (N.reactionVector r) (N.reactionVector r)

/-- **The exact drift identity for a quadratic Lyapunov function.**  For *every* network, the
generator drift of `V n = (n − n*)ᵀ P (n − n*)` splits into the linear part
`2 (n − n*)ᵀ P (∑_r λ_r(n) Δ_r)` and the quadratic remainder `∑_r λ_r(n) (Δ_rᵀ P Δ_r)`. -/
theorem observableGenerator_quadObservable (N : Network (Fin m)) (κ : N.RateConstants)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P) (nStar : Fin m → ℝ) (n : Fin m → ℕ) :
    N.observableGenerator κ (quadObservable P nStar) n =
      2 * bilinear P (countDeviation nStar n) (countDrift N κ n) + quadRemainder N κ P n := by
  unfold Network.observableGenerator
  have hmain : ∀ (r : N.R),
      N.stochasticMassActionRate κ n r * (quadObservable P nStar (N.fireCount n r) -
          quadObservable P nStar n) =
        N.stochasticMassActionRate κ n r *
          (2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
            bilinear P (N.reactionVector r) (N.reactionVector r)) := by
    intro r
    by_cases hen : N.Enabled n r
    · have hfire : N.fireCount n r =
          fun s => n s - (N.reaction r).source s + (N.reaction r).target s := by
        simp [Network.fireCount, hen]
      have hcast : ∀ i, (N.fireCount n r i : ℝ) = (n i : ℝ) + N.reactionVector r i := by
        intro i
        rw [hfire]
        have h1 : ((n i - (N.reaction r).source i : ℕ) : ℝ) =
            (n i : ℝ) - ((N.reaction r).source i : ℝ) := by
          rw [Nat.cast_sub (hen i)]
        rw [Nat.cast_add, h1]
        rw [Network.reactionVector_apply]
        ring
      have hdev : countDeviation nStar (N.fireCount n r) =
          countDeviation nStar n + N.reactionVector r := by
        funext i
        simp only [countDeviation, Pi.add_apply]
        rw [hcast]
        ring
      have hV : quadObservable P nStar (N.fireCount n r) - quadObservable P nStar n =
          2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
            bilinear P (N.reactionVector r) (N.reactionVector r) := by
        rw [quadObservable_eq, quadObservable_eq, hdev, quadForm_add hP]
        simp only [quadForm_eq_bilinear]
        ring
      rw [hV]
    · simp [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]
  have hbs : bilinear P (countDeviation nStar n) (countDrift N κ n) =
      ∑ r, N.stochasticMassActionRate κ n r *
        bilinear P (countDeviation nStar n) (N.reactionVector r) := by
    exact bilinear_sum_right P (countDeviation nStar n)
      (fun r => N.stochasticMassActionRate κ n r) (fun r => N.reactionVector r)
  calc
    (∑ r, N.stochasticMassActionRate κ n r *
        (quadObservable P nStar (N.fireCount n r) - quadObservable P nStar n))
      = ∑ r, N.stochasticMassActionRate κ n r *
          (2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
            bilinear P (N.reactionVector r) (N.reactionVector r)) := by
            refine Finset.sum_congr rfl fun r _ => ?_
            exact hmain r
    _ = (∑ r, (N.stochasticMassActionRate κ n r * 2) *
          bilinear P (countDeviation nStar n) (N.reactionVector r)) +
        (∑ r, N.stochasticMassActionRate κ n r *
          bilinear P (N.reactionVector r) (N.reactionVector r)) := by
            have hstep : (∑ r, N.stochasticMassActionRate κ n r *
                  (2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
                    bilinear P (N.reactionVector r) (N.reactionVector r))) =
                ∑ r, ((N.stochasticMassActionRate κ n r * 2) *
                    bilinear P (countDeviation nStar n) (N.reactionVector r) +
                  N.stochasticMassActionRate κ n r *
                    bilinear P (N.reactionVector r) (N.reactionVector r)) := by
              refine Finset.sum_congr rfl fun r _ => ?_
              ring
            rw [hstep, Finset.sum_add_distrib]
    _ = 2 * (∑ r, N.stochasticMassActionRate κ n r *
          bilinear P (countDeviation nStar n) (N.reactionVector r)) +
        (∑ r, N.stochasticMassActionRate κ n r *
          bilinear P (N.reactionVector r) (N.reactionVector r)) := by
            have h2 : (∑ r, (N.stochasticMassActionRate κ n r * 2) *
                  bilinear P (countDeviation nStar n) (N.reactionVector r)) =
                2 * (∑ r, N.stochasticMassActionRate κ n r *
                  bilinear P (countDeviation nStar n) (N.reactionVector r)) := by
              have h3 : (∑ r, (N.stochasticMassActionRate κ n r * 2) *
                    bilinear P (countDeviation nStar n) (N.reactionVector r)) =
                  ∑ r, 2 * (N.stochasticMassActionRate κ n r *
                    bilinear P (countDeviation nStar n) (N.reactionVector r)) := by
                refine Finset.sum_congr rfl fun r _ => ?_
                ring
              rw [h3, ← mul_sum_univ 2 (fun r => N.stochasticMassActionRate κ n r *
                    bilinear P (countDeviation nStar n) (N.reactionVector r))]
            rw [h2]
    _ = 2 * bilinear P (countDeviation nStar n) (countDrift N κ n) + quadRemainder N κ P n := by
            rw [hbs]
            rfl

/-! ## Unimolecular (first-order) closed loops -/

/-- The indicator of the `i`-th coordinate. -/
def coordIndicator (i : Fin m) : Fin m → ℝ := fun j => if j = i then 1 else 0

/-- The linear count observable of the `i`-th coordinate is the `i`-th count. -/
theorem linearObservable_coordIndicator (i : Fin m) (n : Fin m → ℕ) :
    Network.linearObservable (coordIndicator i) n = (n i : ℝ) := by
  unfold Network.linearObservable coordIndicator
  have h1 : (∑ j, (if j = i then 1 else 0) * (n j : ℝ)) =
      ∑ j, if j = i then (n j : ℝ) else 0 := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hji : j = i
    · simp [hji]
    · simp [hji]
  have h2 : (∑ j, if j = i then (n j : ℝ) else 0) = (n i : ℝ) := by
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin m)) i (fun j => (n j : ℝ))]
    simp
  rw [h1, h2]

/-- **The coordinate drift is the generator drift of the coordinate observable.** -/
theorem countDrift_eq_observableGenerator (N : Network (Fin m)) (κ : N.RateConstants)
    (n : Fin m → ℕ) (i : Fin m) :
    countDrift N κ n i =
      N.observableGenerator κ (Network.linearObservable (coordIndicator i)) n := by
  unfold countDrift Network.observableGenerator
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hen : N.Enabled n r
  · have hjump : N.fireCount n r = N.jumpNextCount n r := by
      simp [Network.fireCount, hen]
      rfl
    have hval : Network.linearObservable (coordIndicator i) (N.fireCount n r) -
        Network.linearObservable (coordIndicator i) n = N.reactionVector r i := by
      rw [hjump, linearObservable_coordIndicator, linearObservable_coordIndicator]
      have h1 : ((N.jumpNextCount n r i : ℕ) : ℝ) = (n i : ℝ) -
          ((N.reaction r).source i : ℝ) + ((N.reaction r).target i : ℝ) := by
        unfold Network.jumpNextCount
        rw [Nat.cast_add, Nat.cast_sub (hen i)]
      rw [h1, Network.reactionVector_apply]
      ring
    rw [hval]
  · simp [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]

/-- The constant part of the drift of a first-order (unimolecular) network: the contribution
of the zeroth-order reactions. -/
noncomputable def firstOrderConstantDrift (N : Network (Fin m)) (κ : N.RateConstants)
    (i : Fin m) : ℝ :=
  N.zeroOrderDrift κ (coordIndicator i)

/-- **The first-order drift matrix** of a network: the linear part `A` of the drift of the
counts, `A n = ∑_r κ_r n_{s(r)} Δ_r` for the unimolecular reactions `r` with source `s(r)`. -/
noncomputable def firstOrderDriftMatrix (N : Network (Fin m)) (κ : N.RateConstants) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun i j => N.firstOrderDriftCoefficient κ (coordIndicator i) j

/-- **The affine drift of a unimolecular network.**  For a first-order network the deterministic
drift of the count vector is exactly affine in the counts: `∑_r λ_r(n) Δ_r = b + A n`, with `A`
the first-order drift matrix and `b` the constant drift.  This is the counting analogue of the
linear drift of the (deterministic) unimolecular plant. -/
theorem countDrift_eq_affine (N : Network (Fin m)) (κ : N.RateConstants)
    (hfirst : N.IsFirstOrderNetwork) (n : Fin m → ℕ) (i : Fin m) :
    countDrift N κ n i =
      firstOrderConstantDrift N κ i +
        (firstOrderDriftMatrix N κ *ᵥ (fun j => (n j : ℝ))) i := by
  rw [countDrift_eq_observableGenerator]
  rw [N.observableGenerator_linear_eq_affine_of_firstOrder κ hfirst (coordIndicator i) n]
  have hmul : (firstOrderDriftMatrix N κ *ᵥ (fun j => (n j : ℝ))) i =
      ∑ j, N.firstOrderDriftCoefficient κ (coordIndicator i) j * (n j : ℝ) := by
    rw [Matrix.mulVec_apply_eq_sum]
    rfl
  unfold firstOrderConstantDrift
  rw [hmul]

/-- The constant part of the quadratic remainder: the contribution of the zeroth-order
reactions to `∑_r λ_r(n) (Δ_rᵀ P Δ_r)`. -/
noncomputable def quadRemainderConstant (N : Network (Fin m)) (κ : N.RateConstants)
    (P : Matrix (Fin m) (Fin m) ℝ) : ℝ := by
  classical
  exact ∑ r : N.R, if N.IsZeroOrderReaction r then
    κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0

/-- The linear part of the quadratic remainder: the contribution of the unimolecular
reactions to `∑_r λ_r(n) (Δ_rᵀ P Δ_r)`, per unit of total count. -/
noncomputable def quadRemainderSlope (N : Network (Fin m)) (κ : N.RateConstants)
    (P : Matrix (Fin m) (Fin m) ℝ) : ℝ := by
  classical
  exact ∑ r : N.R, ∑ s : Fin m, if N.IsUnimolecularFrom r s then
    κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0

/-- **The quadratic remainder of a unimolecular network is at most linear.**  For a first-order
network, `∑_r λ_r(n) (Δ_rᵀ P Δ_r) ≤ R₀ + R₁ (∑_j n_j)`: the zeroth-order reactions contribute a
constant and the unimolecular ones at most a constant times the total count.  This is the key
estimate which makes the quadratic Lyapunov function work: the second-order correction of the
drift does not grow faster than linearly. -/
theorem quadRemainder_le (N : Network (Fin m)) (κ : N.RateConstants)
    (hfirst : N.IsFirstOrderNetwork) {P : Matrix (Fin m) (Fin m) ℝ}
    (hP : ∀ x, 0 ≤ bilinear P x x) (n : Fin m → ℕ) :
    quadRemainder N κ P n ≤
      quadRemainderConstant N κ P + quadRemainderSlope N κ P * (∑ j, (n j : ℝ)) := by
  classical
  have htotal : ∀ (j : Fin m), (n j : ℝ) ≤ ∑ k, (n k : ℝ) := by
    intro j
    have : (n j : ℝ) = ∑ k, if k = j then (n k : ℝ) else 0 := by
      have h2 : (∑ k, if k = j then (n k : ℝ) else 0) = (n j : ℝ) := by
        rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin m)) j (fun k => (n k : ℝ))]
        simp
      rw [h2]
    rw [this]
    exact Finset.sum_le_sum fun k _ => by
      by_cases hkj : k = j
      · simp [hkj]
      · simp [hkj]
  have hkey : ∀ (r : N.R),
      N.stochasticMassActionRate κ n r * bilinear P (N.reactionVector r) (N.reactionVector r) ≤
        (if N.IsZeroOrderReaction r then
            κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) +
          (∑ s, if N.IsUnimolecularFrom r s then
            κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) *
            (∑ j, (n j : ℝ)) := by
    intro r
    have hnonneg : 0 ≤ bilinear P (N.reactionVector r) (N.reactionVector r) :=
      hP (N.reactionVector r)
    rcases hfirst r with h0 | ⟨s0, hs0⟩
    · have hnot : ∀ s : Fin m, ¬ N.IsUnimolecularFrom r s := by
        intro s hs
        have hz := h0 s
        rw [hs.1] at hz
        omega
      rw [N.stochasticRate_zeroOrder κ n h0]
      have hmul : (∑ s, if N.IsUnimolecularFrom r s then
            κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) = 0 := by
        refine Finset.sum_eq_zero fun s _ => ?_
        simp [hnot s]
      rw [hmul]
      simp [h0]
    · have hn0 : ¬ N.IsZeroOrderReaction r := by
        intro h0
        have hz := h0 s0
        rw [hs0.1] at hz
        omega
      have hu : ∀ s : Fin m, N.IsUnimolecularFrom r s ↔ s = s0 := by
        intro s
        constructor
        · intro hs
          exact N.unimolecularFrom_unique hs hs0
        · rintro rfl
          exact hs0
      rw [N.stochasticRate_unimolecular κ n hs0]
      have hslope : (∑ s, if N.IsUnimolecularFrom r s then
            κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) =
          κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) := by
        have h1 : ∀ b ∈ (Finset.univ : Finset (Fin m)), b ≠ s0 →
            (if N.IsUnimolecularFrom r b then
              κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) = 0 := by
          intro b _ hb
          rw [ite_eq_right (fun h => hb ((hu b).mp h))]
        have h2 : s0 ∉ (Finset.univ : Finset (Fin m)) →
            (if N.IsUnimolecularFrom r s0 then
              κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) = 0 := by
          intro h
          exact absurd (Finset.mem_univ s0) h
        simpa [hs0] using (Finset.sum_eq_single s0 h1 h2)
      rw [hslope]
      rw [ite_eq_right hn0]
      have hmul := mul_le_mul_of_nonneg_right (htotal s0) hnonneg
      have hmul2 := mul_le_mul_of_nonneg_left hmul (κ.positive r).le
      linarith
  unfold quadRemainder quadRemainderConstant quadRemainderSlope
  calc
    (∑ r, N.stochasticMassActionRate κ n r *
        bilinear P (N.reactionVector r) (N.reactionVector r))
      ≤ ∑ r, ((if N.IsZeroOrderReaction r then
            κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) +
          (∑ s, if N.IsUnimolecularFrom r s then
            κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) *
            (∑ j, (n j : ℝ))) := by
          refine Finset.sum_le_sum fun r _ => ?_
          exact hkey r
    _ = (∑ r, (if N.IsZeroOrderReaction r then
          κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0)) +
        (∑ r, (∑ s, if N.IsUnimolecularFrom r s then
          κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0)) *
          (∑ j, (n j : ℝ)) := by
          rw [Finset.sum_add_distrib]
          have h3 : (∑ r, (∑ s, if N.IsUnimolecularFrom r s then
                κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0) *
              (∑ j, (n j : ℝ))) =
              (∑ r, (∑ s, if N.IsUnimolecularFrom r s then
                κ.k r * bilinear P (N.reactionVector r) (N.reactionVector r) else 0)) *
                (∑ j, (n j : ℝ)) := sum_mul_const _ _
          rw [h3]

/-! ## The Lyapunov certificate and the Foster drift condition -/

/-- **A quadratic Lyapunov certificate for a unimolecular closed loop.**  The matrix `P` is the
shape matrix of the quadratic Lyapunov function of the closed loop, `c₀` witnesses its positive
definiteness, and the last field is the *Lyapunov equation* for the first-order drift matrix `A`
of the closed loop, in the quadratic form `2 xᵀ P (A x) ≤ −‖x‖²`, i.e. `Aᵀ P + P A ⪯ −I`.

For a Hurwitz (equivalently, output-controllable) closed loop such a `P` exists: this is the
classical solution of the continuous Lyapunov equation, which Mathlib does not provide and
which is therefore recorded as a hypothesis, exactly as `CRNT.Design.GeneralPlantRPA` does for
`LyapunovCertificate`.  The certificate is stated in the *normalized* form `Aᵀ P + P A ⪯ −I`;
rescaling `P` recovers any other Lyapunov constant. -/
structure QuadraticLyapunovCertificate (N : Network (Fin m)) (κ : N.RateConstants) where
  /-- The shape matrix of the quadratic Lyapunov function. -/
  P : Matrix (Fin m) (Fin m) ℝ
  /-- `P` is symmetric. -/
  P_sym : Pᵀ = P
  /-- The positive-definiteness constant of `P`. -/
  c₀ : ℝ
  /-- The positive-definiteness constant is positive. -/
  c₀_pos : 0 < c₀
  /-- `P` dominates `c₀ ‖x‖²`. -/
  P_pos : ∀ x, c₀ * normSq x ≤ bilinear P x x
  /-- The Lyapunov equation `Aᵀ P + P A ⪯ −I` for the first-order drift matrix `A`. -/
  lyap : ∀ x, 2 * bilinear P x (firstOrderDriftMatrix N κ *ᵥ x) ≤ -normSq x

namespace QuadraticLyapunovCertificate

variable {N : Network (Fin m)} {κ : N.RateConstants} (L : QuadraticLyapunovCertificate N κ)

/-- The shape matrix of the certificate is positive semidefinite: `xᵀ P x ≥ 0`. -/
theorem bilinear_nonneg (x : Fin m → ℝ) : 0 ≤ bilinear L.P x x := by
  have h := L.P_pos x
  have hnorm : 0 ≤ normSq x := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmul : 0 ≤ L.c₀ * normSq x := mul_nonneg L.c₀_pos.le hnorm
  linarith

end QuadraticLyapunovCertificate

/-- The Young inequality in the form used for the linear part of the drift:
`2 |a b| ≤ ε a² + ε⁻¹ b²`. -/
theorem abs_mul_le (ε : ℝ) (hε : 0 < ε) (a b : ℝ) :
    2 * |a * b| ≤ ε * a ^ 2 + (1 / ε) * b ^ 2 := by
  have hsq : 0 ≤ (ε * |a| - |b|) ^ 2 / ε := div_nonneg (sq_nonneg _) hε.le
  have heq : ε * a ^ 2 + (1 / ε) * b ^ 2 - 2 * |a * b| = (ε * |a| - |b|) ^ 2 / ε := by
    rw [abs_mul]
    have hsqA : |a| ^ 2 = a ^ 2 := sq_abs a
    have hsqB : |b| ^ 2 = b ^ 2 := sq_abs b
    calc
      ε * a ^ 2 + (1 / ε) * b ^ 2 - 2 * (|a| * |b|)
          = (ε ^ 2 * |a| ^ 2 - 2 * ε * (|a| * |b|) + |b| ^ 2) / ε := by
            rw [hsqA, hsqB]
            field_simp
            ring
      _ = (ε * |a| - |b|) ^ 2 / ε := by ring
  linarith

/-- The bilinear form is additive in its second argument. -/
theorem bilinear_add_right (M : Matrix (Fin m) (Fin m) ℝ) (x u v : Fin m → ℝ) :
    bilinear M x (u + v) = bilinear M x u + bilinear M x v := by
  unfold bilinear
  simp only [Matrix.mulVec_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]

/-- The constant part of the affine drift of a first-order network, as a vector. -/
noncomputable def firstOrderConstantVector (N : Network (Fin m)) (κ : N.RateConstants) :
    Fin m → ℝ :=
  fun i => firstOrderConstantDrift N κ i

/-- The offset of the affine drift of the closed loop at the reference count vector `n*`:
`w = b + A n*`.  In the deviation coordinates `x = n − n*` the drift of the counts is
`w + A x`. -/
noncomputable def fosterDriftOffset (N : Network (Fin m)) (κ : N.RateConstants)
    (nStar : Fin m → ℝ) : Fin m → ℝ :=
  firstOrderConstantVector N κ + firstOrderDriftMatrix N κ *ᵥ nStar

/-- The vector `P w` entering the linear part of the drift of the quadratic Lyapunov function
around the reference count vector. -/
noncomputable def fosterLinearVector (N : Network (Fin m)) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) : Fin m → ℝ :=
  L.P *ᵥ (fosterDriftOffset N κ nStar)

/-- **The additive constant `K` of the Foster drift condition.**  It collects the constant parts
of the linear and quadratic corrections of the drift: twice the square of the linear
coefficient, the constant part of the quadratic remainder, its interaction with the reference
count vector, and the Young constant of the remainder. -/
noncomputable def fosterConstant (N : Network (Fin m)) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) : ℝ :=
  2 * (∑ i, (fosterLinearVector N κ L nStar i) ^ 2)
    + quadRemainderConstant N κ L.P
    + quadRemainderSlope N κ L.P * (∑ i, |nStar i|)
    + ∑ _ : Fin m, 2 * (quadRemainderSlope N κ L.P) ^ 2

/-- The Foster constant is nonnegative. -/
theorem fosterConstant_nonneg (N : Network (Fin m)) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) :
    0 ≤ fosterConstant N κ L nStar := by
  unfold fosterConstant
  have h1 : 0 ≤ 2 * (∑ i, (fosterLinearVector N κ L nStar i) ^ 2) := by
    positivity
  have h2 : 0 ≤ quadRemainderConstant N κ L.P := by
    unfold quadRemainderConstant
    exact Finset.sum_nonneg fun r _ => by
      split_ifs
      · exact mul_nonneg (κ.positive r).le (L.bilinear_nonneg (N.reactionVector r))
      · simp
  have h3 : 0 ≤ quadRemainderSlope N κ L.P * (∑ i, |nStar i|) := by
    have : 0 ≤ quadRemainderSlope N κ L.P := by
      unfold quadRemainderSlope
      exact Finset.sum_nonneg fun r _ => by
        exact Finset.sum_nonneg fun s _ => by
          split_ifs
          · exact mul_nonneg (κ.positive r).le (L.bilinear_nonneg (N.reactionVector r))
          · simp
    exact mul_nonneg this (Finset.sum_nonneg fun i _ => abs_nonneg _)
  have h4 : 0 ≤ ∑ _ : Fin m, 2 * (quadRemainderSlope N κ L.P) ^ 2 := by
    positivity
  linarith

/-- **The Foster drift condition for a unimolecular closed loop.**  Let
`V n = (n − n*)ᵀ P (n − n*)` be the quadratic Lyapunov function of the closed loop and let `P`
solve the Lyapunov equation `Aᵀ P + P A ⪯ −I` for the first-order drift matrix `A` of the
closed loop.  Then the generator drift of `V` satisfies

```text
Q V (n) ≤ − (3/8) ‖n − n*‖² + K,
```

with `K ≥ 0` the Foster constant.  This is the drift condition (H) of the general
Foster–Lyapunov transfer theorem `CRNT.Design.GeneralPlantRPA.ergodic_of_fosterDrift`,
constructed here for an arbitrary output-controllable unimolecular plant. -/
theorem fosterDrift_of_certificate (N : Network (Fin m)) (κ : N.RateConstants)
    (hfirst : N.IsFirstOrderNetwork) (L : QuadraticLyapunovCertificate N κ)
    (nStar : Fin m → ℝ) (n : Fin m → ℕ) :
    N.observableGenerator κ (quadObservable L.P nStar) n ≤
      -(3 / 8) * normSq (countDeviation nStar n) + fosterConstant N κ L nStar := by
  classical
  -- the exact drift identity
  rw [observableGenerator_quadObservable N κ L.P_sym nStar n]
  -- the drift of the counts is affine, and in deviation coordinates it is `w + A x`
  have hcount : countDrift N κ n = fosterDriftOffset N κ nStar +
      firstOrderDriftMatrix N κ *ᵥ (countDeviation nStar n) := by
    funext i
    have haff : countDrift N κ n i = firstOrderConstantDrift N κ i +
        (firstOrderDriftMatrix N κ *ᵥ (fun j => (n j : ℝ))) i :=
      countDrift_eq_affine N κ hfirst n i
    have heq : (fun j => (n j : ℝ)) = countDeviation nStar n + nStar := by
      funext j
      simp only [countDeviation, Pi.add_apply]
      ring
    have hmul : firstOrderDriftMatrix N κ *ᵥ (fun j => (n j : ℝ)) =
        firstOrderDriftMatrix N κ *ᵥ (countDeviation nStar n) +
          firstOrderDriftMatrix N κ *ᵥ nStar := by
      rw [heq, Matrix.mulVec_add]
    rw [haff, hmul]
    simp only [Pi.add_apply]
    unfold fosterDriftOffset
    simp only [Pi.add_apply, firstOrderConstantVector]
    ring
  -- the Lyapunov part
  have hlyap : 2 * bilinear L.P (countDeviation nStar n)
      (firstOrderDriftMatrix N κ *ᵥ (countDeviation nStar n)) ≤
        -normSq (countDeviation nStar n) :=
    L.lyap (countDeviation nStar n)
  -- the linear part, absorbed by the Young inequality
  have hlin : 2 * bilinear L.P (countDeviation nStar n) (fosterDriftOffset N κ nStar) ≤
      (1 / 2) * normSq (countDeviation nStar n) +
        2 * (∑ i, (fosterLinearVector N κ L nStar i) ^ 2) := by
    have hbil : 2 * bilinear L.P (countDeviation nStar n) (fosterDriftOffset N κ nStar) =
        2 * ∑ i, countDeviation nStar n i * fosterLinearVector N κ L nStar i := by
      unfold bilinear fosterLinearVector
      simp only [Matrix.mulVec_apply_eq_sum]
    rw [hbil]
    calc
      2 * ∑ i, countDeviation nStar n i * fosterLinearVector N κ L nStar i
          = ∑ i, 2 * (countDeviation nStar n i * fosterLinearVector N κ L nStar i) := by
              rw [Finset.mul_sum]
      _ ≤ ∑ i, 2 * |countDeviation nStar n i * fosterLinearVector N κ L nStar i| := by
              refine Finset.sum_le_sum fun i _ => ?_
              exact mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
      _ ≤ ∑ i, ((1 / 2) * countDeviation nStar n i ^ 2 +
                2 * fosterLinearVector N κ L nStar i ^ 2) := by
              refine Finset.sum_le_sum fun i _ => ?_
              have h := abs_mul_le (1 / 2) (by norm_num) (countDeviation nStar n i)
                (fosterLinearVector N κ L nStar i)
              have hone : (1 / (1 / 2) : ℝ) = 2 := by
                field_simp
              rw [hone] at h
              exact h
      _ = (1 / 2) * (∑ i, countDeviation nStar n i ^ 2) +
          2 * (∑ i, fosterLinearVector N κ L nStar i ^ 2) := by
            rw [Finset.sum_add_distrib]
            rw [← mul_sum_univ (1 / 2) (fun i => countDeviation nStar n i ^ 2)]
            rw [← mul_sum_univ 2 (fun i => fosterLinearVector N κ L nStar i ^ 2)]
      _ = (1 / 2) * normSq (countDeviation nStar n) +
          2 * (∑ i, fosterLinearVector N κ L nStar i ^ 2) := by
            rfl
  -- the remainder
  have hrem : quadRemainder N κ L.P n ≤
      quadRemainderConstant N κ L.P +
        quadRemainderSlope N κ L.P * (∑ j, (n j : ℝ)) := by
    exact quadRemainder_le N κ hfirst (fun x => L.bilinear_nonneg x) n
  have hrem' : quadRemainder N κ L.P n ≤
      quadRemainderConstant N κ L.P + quadRemainderSlope N κ L.P * (∑ i, |nStar i|) +
        (1 / 8) * normSq (countDeviation nStar n) +
          ∑ j : Fin m, 2 * (quadRemainderSlope N κ L.P) ^ 2 := by
    have hnonneg : 0 ≤ quadRemainderSlope N κ L.P := by
      unfold quadRemainderSlope
      exact Finset.sum_nonneg fun r _ => by
        exact Finset.sum_nonneg fun s _ => by
          split_ifs
          · exact mul_nonneg (κ.positive r).le (L.bilinear_nonneg (N.reactionVector r))
          · simp
    have hsum : (∑ j, (n j : ℝ)) ≤ (∑ j, |countDeviation nStar n j|) + (∑ j, |nStar j|) := by
      have h1 : ∀ j, (n j : ℝ) ≤ |countDeviation nStar n j| + |nStar j| := by
        intro j
        have : (n j : ℝ) = countDeviation nStar n j + nStar j := by
          simp only [countDeviation]
          ring
        rw [this]
        have hx : countDeviation nStar n j ≤ |countDeviation nStar n j| := le_abs_self _
        have hy : nStar j ≤ |nStar j| := le_abs_self _
        linarith
      calc
        (∑ j, (n j : ℝ)) = ∑ j, (countDeviation nStar n j + nStar j) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              simp only [countDeviation]
              ring
        _ ≤ ∑ j, (|countDeviation nStar n j| + |nStar j|) := by
              refine Finset.sum_le_sum fun j _ => ?_
              have heq : (n j : ℝ) = countDeviation nStar n j + nStar j := by
                simp only [countDeviation]
                ring
              linarith [h1 j]
        _ = (∑ j, |countDeviation nStar n j|) + (∑ j, |nStar j|) := by
              rw [Finset.sum_add_distrib]
    have hper : ∀ j, quadRemainderSlope N κ L.P * |countDeviation nStar n j| ≤
        (1 / 8) * countDeviation nStar n j ^ 2 +
          2 * (quadRemainderSlope N κ L.P) ^ 2 := by
      intro j
      have h := abs_mul_le (1 / 4) (by norm_num) (countDeviation nStar n j)
        (quadRemainderSlope N κ L.P)
      have hone : (1 / (1 / 4) : ℝ) = 4 := by
        field_simp
      rw [hone] at h
      have habs : quadRemainderSlope N κ L.P * |countDeviation nStar n j| ≤
          |countDeviation nStar n j * quadRemainderSlope N κ L.P| := by
        calc
          quadRemainderSlope N κ L.P * |countDeviation nStar n j|
              = |countDeviation nStar n j| * quadRemainderSlope N κ L.P := by ring
          _ ≤ |countDeviation nStar n j| * |quadRemainderSlope N κ L.P| := by
              exact mul_le_mul_of_nonneg_left (le_abs_self _) (abs_nonneg _)
          _ = |countDeviation nStar n j * quadRemainderSlope N κ L.P| := by
              rw [abs_mul]
      linarith
    have hsum' : quadRemainderSlope N κ L.P * (∑ j, |countDeviation nStar n j|) ≤
        (1 / 8) * (∑ j, countDeviation nStar n j ^ 2) +
          (∑ j : Fin m, 2 * (quadRemainderSlope N κ L.P) ^ 2) := by
      calc
        quadRemainderSlope N κ L.P * (∑ j, |countDeviation nStar n j|)
            = ∑ j, (quadRemainderSlope N κ L.P * |countDeviation nStar n j|) := by
                rw [Finset.mul_sum]
        _ ≤ ∑ j, ((1 / 8) * countDeviation nStar n j ^ 2 +
              2 * (quadRemainderSlope N κ L.P) ^ 2) := by
                refine Finset.sum_le_sum fun j _ => ?_
                exact hper j
        _ = (1 / 8) * (∑ j, countDeviation nStar n j ^ 2) +
            (∑ j : Fin m, 2 * (quadRemainderSlope N κ L.P) ^ 2) := by
              rw [Finset.sum_add_distrib]
              rw [← mul_sum_univ (1 / 8) (fun j => countDeviation nStar n j ^ 2)]
    have hsumR : quadRemainderSlope N κ L.P * (∑ j, (n j : ℝ)) ≤
        quadRemainderSlope N κ L.P * (∑ j, |countDeviation nStar n j|) +
          quadRemainderSlope N κ L.P * (∑ j, |nStar j|) := by
      have h := mul_le_mul_of_nonneg_left hsum hnonneg
      calc
        quadRemainderSlope N κ L.P * (∑ j, (n j : ℝ))
            ≤ quadRemainderSlope N κ L.P *
                (∑ j, |countDeviation nStar n j| + ∑ j, |nStar j|) := h
        _ = quadRemainderSlope N κ L.P * (∑ j, |countDeviation nStar n j|) +
            quadRemainderSlope N κ L.P * (∑ j, |nStar j|) := by ring
    have hn : normSq (countDeviation nStar n) = ∑ j, countDeviation nStar n j ^ 2 := rfl
    rw [hn]
    linarith
  -- assemble
  have hsplit : 2 * bilinear L.P (countDeviation nStar n) (countDrift N κ n) =
      2 * bilinear L.P (countDeviation nStar n)
          (firstOrderDriftMatrix N κ *ᵥ (countDeviation nStar n)) +
        2 * bilinear L.P (countDeviation nStar n) (fosterDriftOffset N κ nStar) := by
    rw [hcount, bilinear_add_right]
    ring
  rw [hsplit]
  have hnorm : normSq (countDeviation nStar n) = ∑ i, countDeviation nStar n i ^ 2 := rfl
  rw [hnorm] at hrem' hlin hlyap
  rw [hnorm]
  unfold fosterConstant
  linarith


/-! ## The Foster datum, the norm-like function, and ergodicity -/

/-- **The generator drift of the jump system is the generator drift of the network.** -/
theorem jumpSystem_drift_observableGenerator (N : Network (Fin m)) (κ : N.RateConstants)
    (V : (Fin m → ℕ) → ℝ) (n : Fin m → ℕ) :
    (N.jumpSystem κ).drift V n = N.observableGenerator κ V n := by
  classical
  show (∑ r : N.R, N.stochasticMassActionRate κ n r *
      (V (N.jumpNextCount n r) - V n)) = _
  unfold Network.observableGenerator
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hen : N.Enabled n r
  · have hfire : N.fireCount n r = N.jumpNextCount n r := by
      simp [Network.fireCount, hen]
      rfl
    rw [hfire]
  · simp [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]

/-- The norm-like function of the Foster drift condition:
`f n = (3/8) ‖n − n*‖²`. -/
noncomputable def fosterNormLike (N : Network (Fin m)) (κ : N.RateConstants)
    (_L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) (n : Fin m → ℕ) : ℝ :=
  (3 / 8) * normSq (countDeviation nStar n)

/-- The norm-like function is nonnegative. -/
theorem fosterNormLike_nonneg (N : Network (Fin m)) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) (n : Fin m → ℕ) :
    0 ≤ fosterNormLike N κ L nStar n := by
  unfold fosterNormLike
  have h : 0 ≤ normSq (countDeviation nStar n) := by
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  positivity

/-- A nonnegative real whose square is bounded by `M` is at most `M + 1`. -/
theorem sq_le_imp_le (t M : ℝ) (ht : 0 ≤ t) (hM : 0 ≤ M) (h : t ^ 2 ≤ M) : t ≤ M + 1 := by
  by_cases h1 : t ≤ 1
  · linarith
  · have h2 : 1 < t := lt_of_not_ge h1
    have h3 : 1 < t ^ 2 := by nlinarith [sq_nonneg t]
    nlinarith

/-- **A bound on the deviation bounds the coordinates.**  If `‖n − n*‖² ≤ M` then every
coordinate of `n` is at most `∑ |n*| + M + 1`. -/
theorem coord_le_of_normSq_le (nStar : Fin m → ℝ) (n : Fin m → ℕ) {M : ℝ} (hM : 0 ≤ M)
    (h : normSq (countDeviation nStar n) ≤ M) (i : Fin m) :
    (n i : ℝ) ≤ (∑ j, |nStar j|) + M + 1 := by
  have hsq : (countDeviation nStar n i) ^ 2 ≤ M := by
    have h1 := Finset.single_le_sum (f := fun j => (countDeviation nStar n j) ^ 2)
      (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : normSq (countDeviation nStar n) = ∑ j, (countDeviation nStar n j) ^ 2 := rfl
    rw [h2] at h
    linarith
  have habs : |countDeviation nStar n i| ≤ M + 1 := by
    apply sq_le_imp_le _ _ (abs_nonneg _) hM
    rw [sq_abs]
    exact hsq
  have hdev : countDeviation nStar n i = (n i : ℝ) - nStar i := by
    simp only [countDeviation]
  rw [hdev] at habs
  have habs2 : (n i : ℝ) - nStar i ≤ M + 1 := by
    have h1 : (n i : ℝ) - nStar i ≤ |(n i : ℝ) - nStar i| := le_abs_self _
    linarith
  have heq : (n i : ℝ) = ((n i : ℝ) - nStar i) + nStar i := by ring
  have hy : nStar i ≤ |nStar i| := le_abs_self _
  have h2 : |nStar i| ≤ ∑ j, |nStar j| := by
    have := Finset.single_le_sum (f := fun j => |nStar j|)
      (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    simpa using this
  linarith

/-- A set of count vectors with bounded coordinates is finite. -/
theorem finite_of_coord_bound (B : ℝ) (T : Set (Fin m → ℕ))
    (hT : ∀ n ∈ T, ∀ i, (n i : ℝ) ≤ B) : T.Finite := by
  refine (Fintype.piFinset fun _ : Fin m => Finset.range (⌈B⌉₊ + 1)).finite_toSet.subset ?_
  intro n hn
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  intro i
  obtain h := hT n hn i
  rw [Finset.mem_range, Nat.lt_succ_iff]
  exact_mod_cast h.trans (Nat.le_ceil B)

/-- **The norm-like function has finite sublevel sets.** -/
theorem fosterNormLike_finite (N : Network (Fin m)) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) (R : ℝ) :
    {n : Fin m → ℕ | fosterNormLike N κ L nStar n ≤ R}.Finite := by
  by_cases hR : R < 0
  · have hempty : {n : Fin m → ℕ | fosterNormLike N κ L nStar n ≤ R} = ∅ := by
      ext n
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        exact False.elim (not_lt_of_ge h
          (lt_of_lt_of_le hR (fosterNormLike_nonneg N κ L nStar n)))
      · intro h
        have : False := by simp at h
        exact this.elim
    rw [hempty]
    exact Set.finite_empty
  · have hR' : 0 ≤ R := le_of_not_gt hR
    have hM : 0 ≤ 8 * R / 3 := by
      exact div_nonneg (mul_nonneg (by norm_num) hR') (by norm_num)
    set B := (∑ j, |nStar j|) + 8 * R / 3 + 1 with hB
    refine finite_of_coord_bound B {n | fosterNormLike N κ L nStar n ≤ R} ?_
    intro n hn i
    have h' : fosterNormLike N κ L nStar n ≤ R := hn
    have hsum : normSq (countDeviation nStar n) ≤ 8 * R / 3 := by
      unfold fosterNormLike at h'
      have hpos : (0 : ℝ) < 3 / 8 := by norm_num
      nlinarith
    have h1 := coord_le_of_normSq_le nStar n hM hsum i
    rw [hB]
    exact h1

/-- **The quadratic Lyapunov function is nonnegative.** -/
theorem quadObservable_nonneg (N : Network (Fin m)) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) (n : Fin m → ℕ) :
    0 ≤ quadObservable L.P nStar n := by
  rw [quadObservable_eq]
  exact L.bilinear_nonneg (countDeviation nStar n)

/-- **The quadratic Lyapunov function has finite sublevel sets.** -/
theorem quadObservable_finite (N : Network (Fin m)) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ) (nStar : Fin m → ℝ) (R : ℝ) :
    {n : Fin m → ℕ | quadObservable L.P nStar n ≤ R}.Finite := by
  by_cases hR : R < 0
  · have hempty : {n : Fin m → ℕ | quadObservable L.P nStar n ≤ R} = ∅ := by
      ext n
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro h
        exact False.elim (not_lt_of_ge h
          (lt_of_lt_of_le hR (quadObservable_nonneg N κ L nStar n)))
      · intro h
        have : False := by simp at h
        exact this.elim
    rw [hempty]
    exact Set.finite_empty
  · have hR' : 0 ≤ R := le_of_not_gt hR
    have hM : 0 ≤ R / L.c₀ := by
      exact div_nonneg hR' L.c₀_pos.le
    set B := (∑ j, |nStar j|) + R / L.c₀ + 1 with hB
    refine finite_of_coord_bound B {n | quadObservable L.P nStar n ≤ R} ?_
    intro n hn i
    have h' : quadObservable L.P nStar n ≤ R := hn
    have hsum : normSq (countDeviation nStar n) ≤ R / L.c₀ := by
      rw [quadObservable_eq] at h'
      have hP := L.P_pos (countDeviation nStar n)
      have hnorm : 0 ≤ normSq (countDeviation nStar n) := by
        exact Finset.sum_nonneg fun j _ => sq_nonneg _
      have hmul : 0 ≤ L.c₀ * normSq (countDeviation nStar n) :=
        mul_nonneg L.c₀_pos.le hnorm
      have hq : quadForm L.P (countDeviation nStar n) = bilinear L.P (countDeviation nStar n)
        (countDeviation nStar n) := quadForm_eq_bilinear _ _
      rw [hq] at h'
      rw [le_div_iff₀ L.c₀_pos]
      nlinarith
    have h1 := coord_le_of_normSq_le nStar n hM hsum i
    rw [hB]
    exact h1

/-- **The Foster–Lyapunov drift datum of the closed loop.**  This is hypothesis (H) of the
general Foster–Lyapunov transfer theorem, packaged for the closed loop of an arbitrary
output-controllable unimolecular plant. -/
noncomputable def fosterDriftData (N : Network (Fin m)) (κ : N.RateConstants)
    (hfirst : N.IsFirstOrderNetwork) (L : QuadraticLyapunovCertificate N κ)
    (nStar : Fin m → ℝ) :
    FosterDrift (N.jumpSystem κ) (quadObservable L.P nStar) (fosterNormLike N κ L nStar) where
  V_nonneg := fun n => quadObservable_nonneg N κ L nStar n
  f_nonneg := fosterNormLike_nonneg N κ L nStar
  f_finite := fosterNormLike_finite N κ L nStar
  K := fosterConstant N κ L nStar
  K_nonneg := fosterConstant_nonneg N κ L nStar
  drift_le := by
    intro n
    rw [jumpSystem_drift_observableGenerator]
    have h := fosterDrift_of_certificate N κ hfirst L nStar n
    unfold fosterNormLike
    nlinarith

/-- **The drift is strictly negative outside a finite set.**  This is the classical form of
the Foster condition: a *constant* negative drift outside a finite set of counts. -/
theorem fosterDrift_neg_outside (N : Network (Fin m)) (κ : N.RateConstants)
    (hfirst : N.IsFirstOrderNetwork) (L : QuadraticLyapunovCertificate N κ)
    (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    (hn : fosterConstant N κ L nStar + 1 < fosterNormLike N κ L nStar n) :
    (N.jumpSystem κ).drift (quadObservable L.P nStar) n ≤ -1 := by
  rw [jumpSystem_drift_observableGenerator]
  have h := fosterDrift_of_certificate N κ hfirst L nStar n
  unfold fosterNormLike at hn
  linarith

/-- **Ergodicity of the closed loop of a general output-controllable unimolecular plant.**
The Foster drift condition (H) constructed in `fosterDrift_of_certificate`, together with
irreducibility of the closed-loop chain, yields a unique stationary probability which charges
every count, and total-variation convergence to it from every count.  This is the
Briat–Gupta–Khammash conclusion for the general plant. -/
theorem ergodic_of_certificate (N : Network (Fin m)) (κ : N.RateConstants)
    (hfirst : N.IsFirstOrderNetwork) (L : QuadraticLyapunovCertificate N κ)
    (nStar : Fin m → ℝ)
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (Fin m → ℕ) → ℝ, (∀ b, 0 < π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      (∀ a, Tendsto (fun t => ∑' b, |(N.jumpSystem κ).Pmin t a b - π b|) atTop (𝓝 0)) ∧
      (∀ μ : (Fin m → ℕ) → ℝ, (∀ b, 0 ≤ μ b) → HasSum μ 1 →
        (∀ s, 0 ≤ s → ∀ b, ∑' x, μ x * (N.jumpSystem κ).Pmin s x b = μ b) → μ = π) := by
  have hstoch : ∀ t, 0 ≤ t → ∀ n,
      HasSum (fun m => (N.jumpSystem κ).Pmin t n m) 1 := by
    intro t ht n
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (quadObservable L.P nStar)
      (fun a => quadObservable_nonneg N κ L nStar a)
      (quadObservable_finite N κ L nStar) (le_refl 0)
      (fosterConstant_nonneg N κ L nStar) ?_ ht n
    intro a
    rw [jumpSystem_drift_observableGenerator]
    have h := fosterDrift_of_certificate N κ hfirst L nStar a
    have h2 : 0 ≤ fosterNormLike N κ L nStar a := fosterNormLike_nonneg N κ L nStar a
    calc
      N.observableGenerator κ (quadObservable L.P nStar) a
          ≤ -(3 / 8) * normSq (countDeviation nStar a) + fosterConstant N κ L nStar := h
      _ ≤ 0 * quadObservable L.P nStar a + fosterConstant N κ L nStar := by
            unfold fosterNormLike at h2
            linarith
  exact ergodic_of_fosterDrift (N.jumpSystem κ) (quadObservable L.P nStar)
    (fosterNormLike N κ L nStar) (fosterDriftData N κ hfirst L nStar) hstoch hirr


/-! ## The general plant: the closed-loop matrix and the drift condition -/

namespace LinearPlant

variable {n : ℕ} (P : LinearPlant n)

/-- The closed-loop matrix of the antithetic internal model on the augmented state
`(x, u) ∈ ℝ^{n+1}`: it is `[[A, B], [−θ Cᵀ, 0]]`, the linear part of the closed loop
`ẋ = A x + B u`, `u̇ = μ − θ (C x)`.  The closed loop is stable (the plant is
*output controllable*) exactly when this matrix is Hurwitz, and the Lyapunov equation
`Aclᵀ P + P Acl ⪯ −I` then has a positive definite solution `P`. -/
noncomputable def closedLoopMatrix (θ : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := by
  classical
  refine Matrix.of fun i j => ?_
  by_cases hi : i.val < n
  · by_cases hj : j.val < n
    · exact P.A ⟨i.val, hi⟩ ⟨j.val, hj⟩
    · have hj' : j = Fin.last n := Fin.eq_last_of_not_lt hj
      subst hj'
      exact P.B ⟨i.val, hi⟩
  · have hi' : i = Fin.last n := Fin.eq_last_of_not_lt hi
    subst hi'
    by_cases hj : j.val < n
    · exact -(θ * P.C ⟨j.val, hj⟩)
    · exact 0

/-- The closed-loop vector field of the antithetic loop on the augmented state:
`(A x + B u, μ − θ (C x))`.  This is the antithetic loop `antitheticLoop` of
`CRNT.Design.GeneralPlantRPA`, written in the augmented coordinates. -/
noncomputable def closedLoopField (μ θ : ℝ) (z : (Fin n → ℝ) × ℝ) : (Fin n → ℝ) × ℝ :=
  (P.A *ᵥ z.1 + z.2 • P.B, μ - θ * (P.C ⬝ᵥ z.1))

/-- The closed-loop field is the antithetic loop of the general plant. -/
theorem closedLoopField_eq_antitheticLoop (μ θ : ℝ) (z : (Fin n → ℝ) × ℝ) :
    P.closedLoopField μ θ z = P.antitheticLoop μ θ z := rfl

end LinearPlant

/-- **The Lyapunov equation of the certificate is the Lyapunov equation of the plant's
closed-loop matrix.**  If the counting realization of the closed loop has the closed-loop matrix
of the plant as its first-order drift matrix, then the two Lyapunov equations coincide. -/
theorem plant_lyapunov_equation (P : LinearPlant n) (θ : ℝ)
    (N : Network (Fin (n + 1))) (κ : N.RateConstants)
    (L : QuadraticLyapunovCertificate N κ)
    (hreal : ∀ i j, (firstOrderDriftMatrix N κ) i j = (P.closedLoopMatrix θ) i j) :
    (∀ x, 2 * bilinear L.P x ((P.closedLoopMatrix θ) *ᵥ x) ≤ -normSq x) ↔
      (∀ x, 2 * bilinear L.P x (firstOrderDriftMatrix N κ *ᵥ x) ≤ -normSq x) := by
  constructor
  · intro h x
    have hmul : firstOrderDriftMatrix N κ *ᵥ x = (P.closedLoopMatrix θ) *ᵥ x := by
      funext i
      rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hreal]
    rw [hmul]
    exact h x
  · intro h x
    have hmul : (P.closedLoopMatrix θ) *ᵥ x = firstOrderDriftMatrix N κ *ᵥ x := by
      funext i
      rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hreal]
    rw [hmul]
    exact h x

/-- **The general-plant Foster drift condition.**  Let `N` be a counting realization of the
closed loop of the general plant `P` with the antithetic controller, let `θ` be its sensing
rate, and suppose that

* `N` is a *unimolecular* (first-order) network — this is the "counting" version of a linear
  plant, whose species are produced and consumed at rates proportional to the population;
* the first-order drift matrix of `N` is the closed-loop matrix `[[A, B], [−θ Cᵀ, 0]]` of the
  plant — this is the *counting realization* hypothesis;
* `L` is a quadratic Lyapunov certificate whose Lyapunov equation is the one of the
  *closed-loop matrix* of the plant.

Then the Foster drift condition (H) holds for the quadratic Lyapunov function
`V n = (n − n*)ᵀ P (n − n*)` of the closed loop, with the drift bound of
`fosterDrift_of_certificate`.  Together with irreducibility this yields the
Briat–Gupta–Khammash conclusion (`ergodic_of_certificate`). -/
theorem fosterDrift_of_plant (P : LinearPlant n) (θ : ℝ)
    (N : Network (Fin (n + 1))) (κ : N.RateConstants) (hfirst : N.IsFirstOrderNetwork)
    (hreal : ∀ i j, (firstOrderDriftMatrix N κ) i j = (P.closedLoopMatrix θ) i j)
    (L : QuadraticLyapunovCertificate N κ)
    (hlyap : ∀ x, 2 * bilinear L.P x ((P.closedLoopMatrix θ) *ᵥ x) ≤ -normSq x)
    (nStar : Fin (n + 1) → ℝ) (cnt : Fin (n + 1) → ℕ) :
    N.observableGenerator κ (quadObservable L.P nStar) cnt ≤
      -(3 / 8) * normSq (countDeviation nStar cnt) + fosterConstant N κ L nStar := by
  have hlyap' : ∀ x : Fin (n + 1) → ℝ,
      2 * bilinear L.P x (firstOrderDriftMatrix N κ *ᵥ x) ≤ -normSq x := by
    intro x
    have hmul : firstOrderDriftMatrix N κ *ᵥ x = (P.closedLoopMatrix θ) *ᵥ x := by
      funext i
      rw [Matrix.mulVec_apply_eq_sum, Matrix.mulVec_apply_eq_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hreal]
    rw [hmul]
    exact hlyap x
  have h' := (plant_lyapunov_equation P θ N κ L hreal).mpr hlyap'
  exact fosterDrift_of_certificate N κ hfirst L nStar cnt

/-- **The setpoint of the general plant.**  In the counting setting the setpoint is produced by
the *internal model*: the charge `q` of the controller satisfies `q̇ = μ − θ y`, so a stationary
law of the closed loop must have stationary mean output `μ/θ`.  This is the stochastic
counterpart of the deterministic setpoint theorem `antitheticLoop_setpoint`. -/
theorem mean_output_eq_setpoint {S : Type} [DecidableEq S] [Fintype S]
    (N : Network S) (κ : N.RateConstants) {rRef rSense : N.R} {out : S}
    (C : N.MaxRPAChargeCertificate rRef rSense) (hgap : N.UnitOutputGap rRef rSense out)
    (href : ∀ s, (N.reaction rRef).source s = 0)
    (π : (S → ℕ) → ℝ) (hsum : Summable π) (hmass : ∑' n, π n = 1)
    (hsumOut : Summable (fun n => π n * (n out : ℝ)))
    (hstat : ∑' n, π n * N.observableGenerator κ (Network.linearObservable C.charge) n = 0) :
    ∑' n, π n * (n out : ℝ) = C.gain * κ.k rRef / κ.k rSense :=
  N.stochastic_maxRPA_mean κ C hgap href π hsum hmass hsumOut hstat

/-! ## A concrete instance -/



/-! ## What remains -/

/-- **The cubic remainder of the bimolecular annihilation.**  The counting realization of the
*molecular* antithetic controller contains one bimolecular reaction, the annihilation
`Z₁ + Z₂ → ∅`.  Its propensity is *quadratic* in the counts, so its contribution to the drift
of a quadratic Lyapunov function is *cubic*:

```text
λ(n) (Δᵀ P Δ) = κ (n_{Z₁}) (n_{Z₂}) (Δᵀ P Δ).
```

The unimolecular analysis of this file does not cover it: the drift of the counts would then be
neither affine nor bounded by an affine function, and the quadratic Lyapunov function would no
longer have a Foster drift.  In the scalar production–degradation instance the cubic term is
controlled by the explicit `z₁ z₂` cross-term of the Lyapunov function `CRNT.Antithetic.lyap`
(`CRNT.Design.AntitheticErgodic.drift_lyap_le`); extending that control to a general plant — a
matrix `P` with a `z₁ z₂` block and the corresponding sign conditions on `P Δ_r` — is the
remaining part of the Briat–Gupta–Khammash closed-loop ergodicity theorem. -/
theorem annihilation_cubic_remainder (N : Network (Fin m)) (κ : N.RateConstants)
    (P : Matrix (Fin m) (Fin m) ℝ) (n : Fin m → ℕ) (r : N.R) (i j : Fin m)
    (hrate : N.stochasticMassActionRate κ n r = κ.k r * (n i : ℝ) * (n j : ℝ)) :
    N.stochasticMassActionRate κ n r * bilinear P (N.reactionVector r) (N.reactionVector r)
      = κ.k r * (n i : ℝ) * (n j : ℝ) *
        bilinear P (N.reactionVector r) (N.reactionVector r) := by
  rw [hrate]

namespace BirthDeathInstance

/-- The one-species birth–death network `∅ → X` (rate `μ`) and `X → ∅` (rate `γ`): the
counting version of the production–degradation plant `ẋ = −γ x + μ`. -/
def net : Network (Fin 1) :=
  ⟨Fin 2, inferInstance, inferInstance, fun r : Fin 2 =>
    if r = 0 then ⟨![0], ![1]⟩ else ⟨![1], ![0]⟩⟩

/-- The rate constants `μ` (birth) and `γ` (death). -/
def κ (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) : net.RateConstants where
  k := fun r : Fin 2 => if r = 0 then μ else γ
  positive := by
    intro r
    fin_cases r
    · norm_num [hμ]
    · norm_num [hγ]

/-- The birth reaction `∅ → X` has no source species. -/
theorem rBirth_source_zero : ∀ s : Fin 1, (net.reaction (0 : Fin 2)).source s = 0 := by
  intro s
  fin_cases s
  rfl

/-- The death reaction `X → ∅` consumes one molecule of the (only) species. -/
theorem rDeath_source (s : Fin 1) :
    (net.reaction (1 : Fin 2)).source s = if s = 0 then 1 else 0 := by
  fin_cases s
  rfl

/-- The death reaction is unimolecular in the only species, and the birth reaction is
zeroth order: the network is unimolecular. -/
theorem isFirstOrder : net.IsFirstOrderNetwork := by
  intro r
  fin_cases r
  · exact Or.inl (fun s => rBirth_source_zero s)
  · refine Or.inr ⟨0, ?_⟩
    refine ⟨?_, ?_⟩
    · have h1 : (net.reaction (1 : Fin 2)).source 0 = 1 := by
        rw [rDeath_source]
        rfl
      exact h1
    · intro s hs
      fin_cases s
      exact absurd rfl hs

/-- The reaction vector of the death reaction is `−e₀`. -/
theorem rDeath_reactionVector : net.reactionVector (1 : Fin 2) 0 = -1 := by
  unfold net
  simp [Network.reactionVector_apply]

/-- **The first-order drift matrix of the birth–death instance** is `−γ`: the degradation
`X → ∅` is the only unimolecular reaction, while the production `∅ → X` is zeroth order. -/
theorem driftMatrix (μ γ : ℝ) (hμ : 0 < μ) (hγ : 0 < γ) :
    firstOrderDriftMatrix net (κ μ γ hμ hγ) = scalarMatrix (-γ) := by
  classical
  ext i j
  fin_cases i
  fin_cases j
  show net.firstOrderDriftCoefficient (κ μ γ hμ hγ) (coordIndicator 0) 0 = -γ
  have hnot : ¬ net.IsUnimolecularFrom (0 : Fin 2) 0 := by
    intro h
    have h1 := h.1
    rw [rBirth_source_zero] at h1
    norm_num at h1
  have hyes : net.IsUnimolecularFrom (1 : Fin 2) 0 := by
    refine ⟨?_, ?_⟩
    · have h1 : (net.reaction (1 : Fin 2)).source 0 = 1 := by
        rw [rDeath_source]
        rfl
      exact h1
    · intro s hs
      fin_cases s
      exact absurd rfl hs
  unfold Network.firstOrderDriftCoefficient
  show (∑ r : Fin 2, if net.IsUnimolecularFrom r 0 then
      (κ μ γ hμ hγ).k r * net.weightedReactionIncrement (coordIndicator 0) r else 0) = -γ
  rw [Fin.sum_univ_two, ite_eq_right hnot, ite_eq_left hyes]
  have hw : net.weightedReactionIncrement (coordIndicator 0) (1 : Fin 2) = -1 := by
    unfold Network.weightedReactionIncrement
    rw [Fin.sum_univ_one]
    rw [rDeath_reactionVector]
    simp [coordIndicator]
  rw [hw]
  simp [κ]

/-- The bilinear form of the scalar matrix `(1)` is the entrywise product. -/
theorem bilinear_scalar_one (x y : Fin 1 → ℝ) :
    bilinear (scalarMatrix (1 : ℝ)) x y = ∑ i, x i * y i := by
  have hL : bilinear (scalarMatrix (1 : ℝ)) x y = x 0 * y 0 := by
    unfold bilinear
    simp only [Matrix.mulVec_apply_eq_sum]
    rw [Fin.sum_univ_one]
    simp only [Fin.sum_univ_one, scalarMatrix]
    ring
  have hR : (∑ i : Fin 1, x i * y i) = x 0 * y 0 := by
    rw [Fin.sum_univ_one]
  rw [hL, hR]

/-- **The Lyapunov certificate of the birth–death instance.**  For `P = (1)` the Lyapunov
equation `Aᵀ P + P A ⪯ −I` of the closed loop `A = −γ` reads `2 γ ≥ 1`. -/
def cert (γ : ℝ) (hγ : (2 : ℝ) * γ ≥ 1) :
    QuadraticLyapunovCertificate net (κ 1 γ (by norm_num) (by linarith [hγ])) where
  P := scalarMatrix 1
  P_sym := by
    ext i j
    fin_cases i
    fin_cases j
    rfl
  c₀ := 1
  c₀_pos := by norm_num
  P_pos := by
    intro x
    rw [bilinear_scalar_one]
    have hsum : normSq x = ∑ i, x i ^ 2 := rfl
    rw [hsum]
    have h2 : (∑ i, x i * x i) = ∑ i, x i ^ 2 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h2]
    linarith
  lyap := by
    intro x
    have hA : firstOrderDriftMatrix net (κ 1 γ (by norm_num) (by linarith [hγ])) *ᵥ x =
        fun i => -(γ * x i) := by
      rw [driftMatrix]
      funext i
      simp only [Matrix.mulVec_apply_eq_sum, scalarMatrix, Fin.sum_univ_one]
      have hi : i = 0 := by
        apply Fin.ext
        have := i.isLt
        omega
      rw [hi]
      ring
    have hP : bilinear (scalarMatrix (1 : ℝ)) x (fun i => -(γ * x i)) =
        -γ * (∑ i, x i ^ 2) := by
      rw [bilinear_scalar_one]
      calc
        (∑ i, x i * (-(γ * x i))) = ∑ i, (-γ) * (x i ^ 2) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            ring
        _ = (-γ) * (∑ i, x i ^ 2) := by
            symm
            exact Finset.mul_sum Finset.univ (fun i => x i ^ 2) (-γ)
    rw [hA, hP]
    have hsum : normSq x = ∑ i, x i ^ 2 := rfl
    rw [hsum]
    have h1 : (2 * γ - 1) * (∑ i, x i ^ 2) ≥ 0 :=
      mul_nonneg (by linarith [hγ]) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    nlinarith

/-- **The Foster drift condition holds for the birth–death instance**: the drift of the
quadratic Lyapunov function `V n = n²` is at most `−(3/8) n² + K`. -/
theorem fosterDrift (γ : ℝ) (hγ : (2 : ℝ) * γ ≥ 1) (n : Fin 1 → ℕ) :
    net.observableGenerator (κ 1 γ (by norm_num) (by linarith [hγ]))
      (quadObservable (scalarMatrix (1 : ℝ)) 0) n ≤
      -(3 / 8) * normSq (countDeviation 0 n) + fosterConstant net
        (κ 1 γ (by norm_num) (by linarith [hγ])) (cert γ hγ) 0 := by
  have hP : (cert γ hγ).P = scalarMatrix 1 := rfl
  have h := fosterDrift_of_certificate net (κ 1 γ (by norm_num) (by linarith [hγ])) isFirstOrder
    (cert γ hγ) 0 n
  rw [hP] at h
  simpa [quadObservable_eq, countDeviation, normSq] using h

end BirthDeathInstance

/-- **Geometric ergodicity of the closed loop.**  If the shape matrix `P` of the certificate is
additionally bounded above by `c₁ I` (which holds for every positive definite `P`), the Foster
drift condition can be recast in the Meyn–Tweedie `(CD4)` form `QV ≤ −c V + K`, and the closed
loop is *geometrically* ergodic: the law of the chain converges to the stationary law at a
geometric rate. -/
theorem geometricErgodic_of_certificate (N : Network (Fin m)) (κ : N.RateConstants)
    (hfirst : N.IsFirstOrderNetwork) (L : QuadraticLyapunovCertificate N κ)
    (c₁ : ℝ) (hc₁ : 0 < c₁) (hP_le : ∀ x, bilinear L.P x x ≤ c₁ * normSq x)
    (nStar : Fin m → ℝ)
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (Fin m → ℕ) → ℝ, (∀ b, 0 ≤ π b) ∧ HasSum π 1 ∧
      (∀ s, 0 ≤ s → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin s x b = π b) ∧
      ∃ β : ℝ, 0 < β ∧ ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 ∧ ∃ C₀ : ℝ, ∀ a, ∀ t, 0 ≤ t →
        ∑' b, |(N.jumpSystem κ).Pmin t a b - π b| * (1 + β * quadObservable L.P nStar b) ≤
          C₀ * (1 + quadObservable L.P nStar a) * ρ ^ ⌊t⌋₊ := by
  have hstoch : ∀ t, 0 ≤ t → ∀ n,
      HasSum (fun m => (N.jumpSystem κ).Pmin t n m) 1 := by
    intro t ht n
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (quadObservable L.P nStar)
      (fun a => quadObservable_nonneg N κ L nStar a)
      (quadObservable_finite N κ L nStar) (le_refl 0)
      (fosterConstant_nonneg N κ L nStar) ?_ ht n
    intro a
    rw [jumpSystem_drift_observableGenerator]
    have h := fosterDrift_of_certificate N κ hfirst L nStar a
    have h2 : 0 ≤ fosterNormLike N κ L nStar a := fosterNormLike_nonneg N κ L nStar a
    calc
      N.observableGenerator κ (quadObservable L.P nStar) a
          ≤ -(3 / 8) * normSq (countDeviation nStar a) + fosterConstant N κ L nStar := h
      _ ≤ 0 * quadObservable L.P nStar a + fosterConstant N κ L nStar := by
            unfold fosterNormLike at h2
            linarith
  have hkey : ∀ (x : Fin m → ℝ),
      (3 / (8 * c₁)) * bilinear L.P x x ≤ (3 / 8) * normSq x := by
    intro x
    have h1 : bilinear L.P x x ≤ c₁ * normSq x := hP_le x
    have h2 : 0 ≤ 3 / (8 * c₁) := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 h2
    calc
      (3 / (8 * c₁)) * bilinear L.P x x ≤ (3 / (8 * c₁)) * (c₁ * normSq x) := h3
      _ = (3 / 8) * normSq x := by
            field_simp
  have hdrift0 : ∀ (x : Fin m → ℕ),
      (N.jumpSystem κ).drift (quadObservable L.P nStar) x ≤
        -(3 / (8 * c₁)) * quadObservable L.P nStar x + fosterConstant N κ L nStar := by
    intro x
    rw [jumpSystem_drift_observableGenerator]
    have h := fosterDrift_of_certificate N κ hfirst L nStar x
    have hx := hkey (countDeviation nStar x)
    have hV : quadObservable L.P nStar x = bilinear L.P (countDeviation nStar x)
        (countDeviation nStar x) := by
      rw [quadObservable_eq, quadForm_eq_bilinear]
    rw [hV]
    linarith
  refine (N.jumpSystem κ).geometric_ergodic_of_drift_on (c := 3 / (8 * c₁))
    (K := fosterConstant N κ L nStar) (quadObservable L.P nStar)
    (fun x => quadObservable_nonneg N κ L nStar x) (quadObservable_finite N κ L nStar)
    (by positivity) (fosterConstant_nonneg N κ L nStar) Set.univ ?_ hstoch hirr
  intro x
  simpa [Set.indicator_of_mem] using hdrift0 x

end GeneralPlant
end Design
end CRNT
