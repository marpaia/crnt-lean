import CRNT.Equilibria.ToricSteadyStates
import CRNT.Equilibria.SingletonSource
import CRNT.LinearAlgebra.OrthogonalComplement
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Exponential log-kernel parametrizations and steady-state invariants

The positive binomial steady-state set is parametrized by exponentiating an
appropriate log-kernel/affine subspace, with the stated coefficient hypotheses.
The file also characterizes invariants of singleton-source linear systems.
A rational parametrization in independent algebraic coordinates requires an
integer-lattice/exponent bridge which is not constructed here. This file does
not complete the published partitioned MESSI theory.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type} [Fintype S]

/-! ## The exponent-difference matrix and its kernel -/

/-- The real exponent difference `a − b` of a binomial, read as a vector of species. -/
def expDifference (a b : Complex S) : S → ℝ := fun s => (a s : ℝ) - (b s : ℝ)

/-- The pairing of a log-concentration with an exponent difference is the dot product
with the exponent-difference vector. -/
theorem expPairing_eq_dot (a b : Complex S) (v : S → ℝ) :
    expPairing a b v = ∑ s, v s * expDifference a b s := by
  unfold expPairing expDifference
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The pairing is additive in the log-concentration. -/
theorem expPairing_add (a b : Complex S) (v w : S → ℝ) :
    expPairing a b (v + w) = expPairing a b v + expPairing a b w := by
  unfold expPairing
  simp only [Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The pairing is homogeneous in the log-concentration. -/
theorem expPairing_smul (a b : Complex S) (c : ℝ) (v : S → ℝ) :
    expPairing a b (c • v) = c * expPairing a b v := by
  unfold expPairing
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The pairing is a difference of pairings. -/
theorem expPairing_sub (a b : Complex S) (v w : S → ℝ) :
    expPairing a b (v - w) = expPairing a b v - expPairing a b w := by
  unfold expPairing
  simp only [Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The exponent-difference (incidence) matrix of a family of binomials**, read as a
linear map from log-concentrations to `ι → ℝ`: the `i`-th coordinate of the image of
`v` is the pairing `⟨aᵢ − bᵢ, v⟩`. -/
def expPairingMap (a b : ι → Complex S) : (S → ℝ) →ₗ[ℝ] (ι → ℝ) where
  toFun v := fun i => expPairing (a i) (b i) v
  map_add' v w := by
    funext i
    exact expPairing_add _ _ _ _
  map_smul' c v := by
    funext i
    exact expPairing_smul _ _ _ _

/-- **The log-kernel of a family of binomials**: the log-concentrations orthogonal to
every exponent difference `aᵢ − bᵢ`.  This is the kernel of the exponent-difference
matrix, i.e. the linear space parametrizing the toric steady-state variety. -/
def expLogKernel (a b : ι → Complex S) : Submodule ℝ (S → ℝ) where
  carrier := {v | ∀ i, expPairing (a i) (b i) v = 0}
  zero_mem' := by
    intro v
    simp [expPairing]
  add_mem' := by
    intro v w hv hw i
    rw [expPairing_add, hv i, hw i, add_zero]
  smul_mem' := by
    intro c v hv i
    rw [expPairing_smul, hv i, mul_zero]

/-- Membership in the log-kernel is orthogonality to every exponent difference. -/
theorem mem_expLogKernel {a b : ι → Complex S} {v : S → ℝ} :
    v ∈ expLogKernel a b ↔ ∀ i, expPairing (a i) (b i) v = 0 := Iff.rfl

/-- The log-kernel is the kernel of the exponent-difference matrix. -/
theorem expLogKernel_eq_ker (a b : ι → Complex S) :
    expLogKernel a b = LinearMap.ker (expPairingMap a b) := by
  ext v
  rw [mem_expLogKernel]
  constructor
  · intro h
    refine LinearMap.mem_ker.mp ?_
    funext i
    exact h i
  · intro h
    have h' := LinearMap.mem_ker.mp h
    intro i
    exact congrFun h' i

/-- **The log-kernel is the orthogonal complement of the span of the exponent
differences.**  This is the "incidence matrix" picture: the kernel of the matrix whose
rows are the `aᵢ − bᵢ` is the set of vectors orthogonal to all of them. -/
theorem expLogKernel_eq_orthSum_span (a b : ι → Complex S) :
    expLogKernel a b
      = orthSum (Submodule.span ℝ (Set.range fun i => expDifference (a i) (b i))) := by
  ext v
  rw [mem_orthSum]
  constructor
  · intro h
    refine mem_orthSum_span ?_
    intro u hu
    obtain ⟨i, rfl⟩ := hu
    have h1 : expPairing (a i) (b i) v = 0 := (mem_expLogKernel.mp h) i
    rw [expPairing_eq_dot] at h1
    exact h1
  · intro h
    refine mem_expLogKernel.mpr fun i => ?_
    have h1 := h (expDifference (a i) (b i))
      (Submodule.subset_span ⟨i, rfl⟩)
    rw [expPairing_eq_dot]
    exact h1

/-! ## The exponential and the monomial parametrization -/

/-- The coordinatewise exponential of a log-vector. -/
noncomputable def expVec (v : S → ℝ) : S → ℝ := fun s => Real.exp (v s)

omit [Fintype S] in
/-- The exponential is multiplicative: `exp (v + w) = exp v · exp w`. -/
theorem expVec_mul (v w : S → ℝ) : expVec (v + w) = expVec v * expVec w := by
  funext s
  simp [expVec, Real.exp_add]

omit [Fintype S] in
/-- The exponential is injective. -/
theorem expVec_injective (S : Type) : Function.Injective (expVec (S := S)) := by
  intro v w h
  funext s
  have h1 := congrFun h s
  exact Real.exp_injective h1

/-- **The monomial parametrization of the toric variety with base point `x*`**:
`x = x* · exp v`.  It is a monomial map: it multiplies the coordinates of `x*` by the
coordinates of `exp v`. -/
noncomputable def toricParametrization (xs : Concentration S) (v : S → ℝ) : Concentration S :=
  fun s => xs s * Real.exp (v s)

omit [Fintype S] in
/-- **The monomial map** `x* ⊙ u`: the coordinatewise product of a fixed vector with a
point of the positive torus. -/
def monomialMul (xs u : Concentration S) : Concentration S := fun s => xs s * u s

omit [Fintype S] in
/-- The parametrization of the origin of the log-space is the base point itself. -/
theorem toricParametrization_zero (xs : Concentration S) :
    toricParametrization xs 0 = xs := by
  funext s
  simp [toricParametrization]

omit [Fintype S] in
/-- The parametrization is injective on the log-space, provided the base point is
positive. -/
theorem toricParametrization_injective {xs : Concentration S} (hxs : xs.Positive) :
    Function.Injective (toricParametrization xs) := by
  intro v w h
  funext s
  have h1 := congrFun h s
  simp only [toricParametrization] at h1
  have hne : xs s ≠ 0 := ne_of_gt (hxs s)
  have : Real.exp (v s) = Real.exp (w s) := by
    apply (mul_left_cancel₀ hne)
    linarith
  exact (Real.exp_injective this)

omit [Fintype S] in
/-- The monomial parametrization is the exponential of the shifted log-vector. -/
theorem toricParametrization_eq_expVec_add {xs : Concentration S} (hxs : xs.Positive)
    (v : S → ℝ) :
    toricParametrization xs v = expVec ((fun s => Real.log (xs s)) + v) := by
  funext s
  simp only [toricParametrization, expVec, Pi.add_apply]
  calc xs s * Real.exp (v s)
      = Real.exp (Real.log (xs s)) * Real.exp (v s) := by rw [Real.exp_log (hxs s)]
    _ = Real.exp (Real.log (xs s) + v s) := by rw [Real.exp_add]

/-! ## The positive torus -/

/-- **The positive torus** `(ℝ_{>0})^S`: the set of strictly positive vectors, which is a
group under componentwise multiplication. -/
def posTorus (S : Type) : Set (S → ℝ) := {u | ∀ s, 0 < u s}

/-- The multiplicative identity belongs to the positive torus. -/
theorem posTorus_one (S : Type) : (1 : S → ℝ) ∈ posTorus S := by
  intro s
  simp

/-- The positive torus is closed under componentwise multiplication. -/
theorem posTorus_mul {S : Type} {u v : S → ℝ} (hu : u ∈ posTorus S) (hv : v ∈ posTorus S) :
    u * v ∈ posTorus S := by
  intro s
  exact mul_pos (hu s) (hv s)

/-- The positive torus is closed under componentwise inversion. -/
theorem posTorus_inv {S : Type} {u : S → ℝ} (hu : u ∈ posTorus S) :
    u⁻¹ ∈ posTorus S := by
  intro s
  exact inv_pos.mpr (hu s)

/-- Every element of the positive torus has its inverse in the positive torus. -/
theorem posTorus_mul_inv {S : Type} {u : S → ℝ} (hu : u ∈ posTorus S) :
    u * u⁻¹ = 1 := by
  funext s
  have hne : u s ≠ 0 := ne_of_gt (hu s)
  simp [Pi.mul_apply, Pi.inv_apply, hne]

/-- **The torus of a binomial system**: the image of the log-kernel under the
exponential.  It is a group under componentwise multiplication, and it is the
*torus* whose image under the monomial parametrization is the toric variety. -/
def toricTorus (a b : ι → Complex S) : Set (S → ℝ) :=
  {u | ∃ v ∈ expLogKernel a b, u = expVec v}

/-- The torus of a binomial system consists of positive vectors. -/
theorem toricTorus_pos {a b : ι → Complex S} {u : S → ℝ} (hu : u ∈ toricTorus a b) :
    u ∈ posTorus S := by
  obtain ⟨v, -, rfl⟩ := hu
  intro s
  exact Real.exp_pos _

/-- The identity belongs to the torus of a binomial system. -/
theorem toricTorus_one {a b : ι → Complex S} : (1 : S → ℝ) ∈ toricTorus a b := by
  refine ⟨0, ?_, ?_⟩
  · exact (expLogKernel a b).zero_mem
  · funext s
    simp [expVec]

/-- The torus of a binomial system is closed under componentwise multiplication. -/
theorem toricTorus_mul {a b : ι → Complex S} {u v : S → ℝ}
    (hu : u ∈ toricTorus a b) (hv : v ∈ toricTorus a b) :
    u * v ∈ toricTorus a b := by
  obtain ⟨u', hu', rfl⟩ := hu
  obtain ⟨v', hv', rfl⟩ := hv
  refine ⟨u' + v', (expLogKernel a b).add_mem hu' hv', ?_⟩
  rw [expVec_mul]

/-- The torus of a binomial system is closed under componentwise inversion. -/
theorem toricTorus_inv {a b : ι → Complex S} {u : S → ℝ} (hu : u ∈ toricTorus a b) :
    u⁻¹ ∈ toricTorus a b := by
  obtain ⟨v, hv, rfl⟩ := hu
  refine ⟨-v, ?_, ?_⟩
  · have h1 : (-1 : ℝ) • v ∈ expLogKernel a b :=
      (expLogKernel a b).smul_mem (-1) hv
    rwa [show (-1 : ℝ) • v = -v from by simp] at h1
  · funext s
    simp [expVec, Real.exp_neg, Pi.neg_apply]

/-- Every element of the torus of a binomial system has its inverse in the torus. -/
theorem toricTorus_mul_inv {a b : ι → Complex S} {u : S → ℝ} (hu : u ∈ toricTorus a b) :
    u * u⁻¹ = 1 := by
  exact posTorus_mul_inv (toricTorus_pos hu)

/-! ## The rational parametrization of a toric steady-state variety -/

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- **A parametrized point of the toric variety is a positive steady state.**  If `v` is
orthogonal to all exponent differences then `x* · exp v` is a positive steady state. -/
theorem toric_parametrization_isSteadyState
    (N : Network S) (κ : N.RateConstants) {n : ℕ} (a b : Fin n → Complex S)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (v : S → ℝ) (hv : ∀ i, expPairing (a i) (b i) v = 0) :
    (toricParametrization xs v).Positive ∧
      N.IsMassActionSteadyState κ (toricParametrization xs v) := by
  have hiff := N.toricSteadyState_iff_exp_parametrization κ a b c hc htor hxs hxss
    (toricParametrization xs v)
  obtain ⟨w, hw, hxw⟩ :
      ∃ w, (∀ i, expPairing (a i) (b i) w = 0) ∧
        toricParametrization xs v = fun s => xs s * Real.exp (w s) := ⟨v, hv, rfl⟩
  have h1 := hiff.symm.mp ⟨w, hw, hxw⟩
  exact h1

/-- **A positive steady state is a parametrized point of the toric variety.** -/
theorem toric_steadyState_exists_parametrization
    (N : Network S) (κ : N.RateConstants) {n : ℕ} (a b : Fin n → Complex S)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (x : Concentration S) (hx : x.Positive) (hss : N.IsMassActionSteadyState κ x) :
    ∃ v, (∀ i, expPairing (a i) (b i) v = 0) ∧ x = toricParametrization xs v := by
  have h1 := (N.toricSteadyState_iff_exp_parametrization κ a b c hc htor hxs hxss x).mp ⟨hx, hss⟩
  obtain ⟨v, hv, hxv⟩ := h1
  exact ⟨v, hv, hxv⟩

/-- **The exponential log-kernel parametrization of the toric steady-state variety.**  Under the
binomial hypothesis `htor`, the positive steady states of `N` are exactly the image of
the monomial parametrization over the log-kernel of the exponent differences: the
variety is the image of a torus under a monomial map. -/
theorem toric_positiveSteadyStates_eq_parametrization
    (N : Network S) (κ : N.RateConstants) {n : ℕ} (a b : Fin n → Complex S)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs) :
    { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x }
      = { toricParametrization xs v | v ∈ expLogKernel a b } := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hx' : x.Positive ∧ N.IsMassActionSteadyState κ x := Set.mem_ofPred_eq.mp hx
    obtain ⟨v, hv, rfl⟩ :=
      N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss x hx'.1 hx'.2
    exact ⟨v, mem_expLogKernel.mpr hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact N.toric_parametrization_isSteadyState κ a b c hc htor hxs hxss v (mem_expLogKernel.mp hv)

/-- **Every positive steady state has a unique parametrization.**  The rational
parametrization of the toric variety is a bijection onto the positive steady states. -/
theorem exists_unique_toric_parametrization
    (N : Network S) (κ : N.RateConstants) {n : ℕ} (a b : Fin n → Complex S)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (x : Concentration S) :
    (x.Positive ∧ N.IsMassActionSteadyState κ x) ↔
      ∃! v : S → ℝ, v ∈ expLogKernel a b ∧ x = toricParametrization xs v := by
  constructor
  · rintro ⟨hx, hss⟩
    obtain ⟨v, hv, hxv⟩ :=
      N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss x hx hss
    refine ⟨v, ⟨mem_expLogKernel.mpr hv, hxv⟩, ?_⟩
    intro y hy
    have hy' : ∀ i, expPairing (a i) (b i) y = 0 := mem_expLogKernel.mp hy.1
    have hxy : toricParametrization xs v = toricParametrization xs y := by
      rw [hxv.symm, hy.2.symm]
    exact toricParametrization_injective hxs hxy.symm
  · rintro ⟨v, hv, _⟩
    have hmem : v ∈ expLogKernel a b := hv.1
    have hxv : x = toricParametrization xs v := hv.2
    rw [hxv]
    exact N.toric_parametrization_isSteadyState κ a b c hc htor hxs hxss v
      (mem_expLogKernel.mp hmem)

/-- **The exponential (kernel) parametrization of a toric steady-state variety.**
When the binomial equations are *homogeneous*, `x ^ aᵢ = x ^ bᵢ` (that is, all
coefficients `cᵢ` are `1`), the positive steady states of `N` are exactly the
exponentials of the vectors in the kernel of the exponent-difference matrix:
`x = exp v` with `v ⊥ aᵢ − bᵢ` for all `i`. -/
theorem toric_steadyStates_eq_exp_kernel (N : Network S) (κ : N.RateConstants)
    {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (hc1 : ∀ i, c i = 1)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs) :
    { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x }
      = { fun s => Real.exp (v s) | v ∈ expLogKernel a b } := by
  have hlog : (fun s => Real.log (xs s)) ∈ expLogKernel a b := by
    refine mem_expLogKernel.mpr fun i => ?_
    have hsol := (htor xs hxs).mp hxss i
    have hsol' : (a i).massActionMonomial xs = 1 * (b i).massActionMonomial xs := by
      rw [hc1 i] at hsol
      exact hsol
    have h1 := (binomial_iff_log hxs (a i) (b i) (c := 1) (by norm_num)).mp hsol'
    simpa using h1
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hx' : x.Positive ∧ N.IsMassActionSteadyState κ x := Set.mem_ofPred_eq.mp hx
    obtain ⟨v, hv, hxv⟩ :=
      N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss x hx'.1 hx'.2
    have hmem : (fun s => Real.log (xs s)) + v ∈ expLogKernel a b := by
      refine mem_expLogKernel.mpr fun i => ?_
      have h1 := (mem_expLogKernel.mp hv) i
      have h2 := (mem_expLogKernel.mp hlog) i
      rw [expPairing_add]
      linarith
    refine ⟨(fun s => Real.log (xs s)) + v, hmem, ?_⟩
    rw [hxv, toricParametrization_eq_expVec_add hxs]
    funext s
    simp [expVec]
  · rintro ⟨w, hw, rfl⟩
    have hmem : w - (fun s => Real.log (xs s)) ∈ expLogKernel a b := by
      refine mem_expLogKernel.mpr fun i => ?_
      have h1 := (mem_expLogKernel.mp hw) i
      have h2 := (mem_expLogKernel.mp hlog) i
      rw [expPairing_sub]
      linarith
    have hx : (fun s => Real.exp (w s))
        = toricParametrization xs (w - (fun s => Real.log (xs s))) := by
      rw [toricParametrization_eq_expVec_add hxs]
      funext s
      simp only [expVec, Pi.add_apply, Pi.sub_apply]
      congr 1
      ring
    rw [hx]
    exact N.toric_parametrization_isSteadyState κ a b c hc htor hxs hxss
      (w - (fun s => Real.log (xs s))) (mem_expLogKernel.mp hmem)

/-- The set of log-vectors solving the *affine* system `⟨aᵢ − bᵢ, v⟩ = log cᵢ` of a
family of binomials. -/
def expAffineCondition (a b : ι → Complex S) (c : ι → ℝ) : Set (S → ℝ) :=
  { v : S → ℝ | ∀ i, expPairing (a i) (b i) v = Real.log (c i) }

/-- **The affine log-condition.**  The positive steady states of a toric network are
exactly the exponentials of the log-vectors solving the *affine* system
`⟨aᵢ − bᵢ, v⟩ = log cᵢ`.  The system is homogeneous (and its solution set a linear
subspace) exactly when all coefficients `cᵢ` are `1`; this is why the exponential
*kernel* parametrization `CRNT.toric_steadyStates_eq_exp_kernel` needs the hypothesis
`cᵢ = 1`. -/
theorem toric_steadyStates_eq_exp_affine (N : Network S) (κ : N.RateConstants)
    {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x)) :
    { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x }
      = { fun s => Real.exp (v s) | v ∈ expAffineCondition a b c } := by
  ext x
  constructor
  · rintro ⟨hx, hss⟩
    have h1 := (htor x hx).mp hss
    refine ⟨fun s => Real.log (x s), ⟨?_, ?_⟩⟩
    · intro i
      exact (binomial_iff_log hx (a i) (b i) (hc i)).mp (h1 i)
    · funext s
      rw [Real.exp_log (hx s)]
  · rintro ⟨v, ⟨hv, rfl⟩⟩
    refine ⟨fun s => Real.exp_pos (v s), ?_⟩
    have h1 : ∀ i, (a i).massActionMonomial (fun s => Real.exp (v s))
        = c i * (b i).massActionMonomial (fun s => Real.exp (v s)) := by
      intro i
      exact (binomial_iff_log (fun s => Real.exp_pos (v s)) (a i) (b i) (hc i)).mpr (by
        rw [show (fun s => Real.log (Real.exp (v s))) = v from by
          funext s; rw [Real.log_exp]]
        exact hv i)
    exact (htor _ (fun s => Real.exp_pos (v s))).mpr h1

/-- **The exponential parametrization of a toric steady-state variety, with the kernel
of the incidence matrix.**  This is `CRNT.toric_steadyStates_eq_exp_kernel` with the
log-kernel written as the kernel of the linear map `expPairingMap` associated to the
exponent-difference matrix. -/
theorem toric_steadyStates_eq_exp_ker (N : Network S) (κ : N.RateConstants)
    {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (hc1 : ∀ i, c i = 1)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs) :
    { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x }
      = { fun s => Real.exp (v s) | v ∈ LinearMap.ker (expPairingMap a b) } := by
  rw [toric_steadyStates_eq_exp_kernel N κ a b c hc hc1 htor hxs hxss, expLogKernel_eq_ker]

/-- **The toric steady-state variety is a coset of the torus.**  The positive steady
states of a toric network form `x* · 𝕋`, the coset of the torus `𝕋 = exp (ker)` in the
multiplicative monoid of positive vectors; the monomial map `u ↦ x* · u` is a group
homomorphism on the torus. -/
theorem toric_positiveSteadyStates_eq_coset
    (N : Network S) (κ : N.RateConstants) {n : ℕ} (a b : Fin n → Complex S)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs) :
    { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x }
      = { monomialMul xs u | u ∈ toricTorus a b } := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    have hx' : x.Positive ∧ N.IsMassActionSteadyState κ x := Set.mem_ofPred_eq.mp hx
    obtain ⟨v, hv, hxv⟩ :=
      N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss x hx'.1 hx'.2
    refine ⟨expVec v, ⟨v, mem_expLogKernel.mpr hv, rfl⟩, ?_⟩
    rw [hxv]
    funext s
    simp [monomialMul, toricParametrization, expVec]
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hu
    have hmem : v ∈ expLogKernel a b := mem_expLogKernel.mpr hv
    have h1 := N.toric_parametrization_isSteadyState κ a b c hc htor hxs hxss v
      (mem_expLogKernel.mp hmem)
    refine Set.mem_ofPred_eq.mpr ?_
    rw [show (monomialMul xs (expVec v) : Concentration S) = toricParametrization xs v by
      funext s; simp [monomialMul, toricParametrization, expVec]]
    exact h1

/-! ## The linear parametrization of a SingletonSource steady-state variety -/

omit [DecidableEq S] [Fintype S] in
/-- **The ambient coordinates of a linear combination of basis vectors.** -/
theorem coe_sum_smul {ι : Type} [Fintype ι] (V : Submodule ℝ (S → ℝ))
    (B : Module.Basis ι ℝ V) (u : ι → ℝ) (s : S) :
    ((∑ j, u j • B j : V) : S → ℝ) s = ∑ j, u j * (B j : S → ℝ) s := by
  simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply,
    smul_eq_mul]

/-- A basis of the steady-state variety of a SingletonSource network.  The variety is a finite
dimensional linear subspace, hence admits a basis. -/
noncomputable def singletonSourceVarietyBasis (N : Network S) (κ : N.RateConstants) :
    Module.Basis (Fin (Module.finrank ℝ (N.singletonSourceVariety κ))) ℝ (N.singletonSourceVariety κ) :=
  Module.finBasis ℝ (N.singletonSourceVariety κ)

/-- Each basis vector of the steady-state variety is a steady state. -/
theorem singletonSourceVarietyBasis_mem (N : Network S) (κ : N.RateConstants)
    (B : Module.Basis (Fin (Module.finrank ℝ (N.singletonSourceVariety κ))) ℝ (N.singletonSourceVariety κ))
    (j : Fin (Module.finrank ℝ (N.singletonSourceVariety κ))) :
    (B j : S → ℝ) ∈ N.singletonSourceVariety κ := by
  have h : (B j : S → ℝ) ∈ (N.singletonSourceVariety κ : Set (S → ℝ)) := SetLike.coe_mem (B j)
  exact h

/-- **The linear parametrization of the steady-state variety.**  With a basis `B` of the
variety, every steady state is a linear combination `∑ j, u j • B j` of the basis
vectors; this is the exponential log-kernel parametrization of the (linear, hence rational)
steady-state variety of a SingletonSource network. -/
theorem singletonSource_variety_eq_linearParametrization (N : Network S) (κ : N.RateConstants)
    (B : Module.Basis (Fin (Module.finrank ℝ (N.singletonSourceVariety κ))) ℝ (N.singletonSourceVariety κ))
    (x : Concentration S) :
    x ∈ N.singletonSourceVariety κ ↔
      ∃ u : Fin (Module.finrank ℝ (N.singletonSourceVariety κ)) → ℝ,
        x = fun s => ∑ j, u j * (B j : S → ℝ) s := by
  constructor
  · intro hx
    refine ⟨B.repr ⟨x, hx⟩, ?_⟩
    have hsum := B.sum_repr ⟨x, hx⟩
    funext s
    have hco := coe_sum_smul (N.singletonSourceVariety κ) B (B.repr ⟨x, hx⟩) s
    rw [← hco, hsum]
  · rintro ⟨u, rfl⟩
    have hmem : ((∑ j, u j • B j : N.singletonSourceVariety κ) : S → ℝ) ∈ N.singletonSourceVariety κ := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun j _ =>
        (N.singletonSourceVariety κ).smul_mem _ (N.singletonSourceVarietyBasis_mem κ B j)
    have hfun : (fun s => ∑ j, u j * (B j : S → ℝ) s)
        = ((∑ j, u j • B j : N.singletonSourceVariety κ) : S → ℝ) := by
      funext s
      exact (coe_sum_smul (N.singletonSourceVariety κ) B u s).symm
    rw [hfun]
    exact hmem

/-- The image of the linear parametrization of the steady-state variety of a SingletonSource
network, restricted to a set of parameters. -/
def singletonSourceLinearParametrization (N : Network S) (κ : N.RateConstants)
    (B : Module.Basis (Fin (Module.finrank ℝ (N.singletonSourceVariety κ))) ℝ (N.singletonSourceVariety κ))
    (P : Set (Fin (Module.finrank ℝ (N.singletonSourceVariety κ)) → ℝ)) : Set (Concentration S) :=
  { fun s => ∑ j, u j * (B j : S → ℝ) s | u ∈ P }

/-- **The positive steady states of a SingletonSource network are the positive part of the linear
parametrization.** -/
theorem singletonSource_positiveSteadyStates_eq_linearParametrization (N : Network S)
    (κ : N.RateConstants) (hM : SingletonSource N)
    (B : Module.Basis (Fin (Module.finrank ℝ (N.singletonSourceVariety κ))) ℝ (N.singletonSourceVariety κ)) :
    { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x }
      = N.singletonSourceLinearParametrization κ B
          { u | ∀ s, 0 < ∑ j, u j * (B j : S → ℝ) s } := by
  ext x
  constructor
  · rintro ⟨hx, hss⟩
    have hx' : x ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM x).mpr hss
    obtain ⟨u, hu⟩ := (singletonSource_variety_eq_linearParametrization N κ B x).mp hx'
    refine ⟨u, ?_, ?_⟩
    · intro s
      have hs : x s = ∑ j, u j * (B j : S → ℝ) s := by rw [hu]
      rw [← hs]
      exact hx s
    · rw [hu]
  · rintro ⟨u, hu, rfl⟩
    have hmem : ((∑ j, u j • B j : N.singletonSourceVariety κ) : S → ℝ) ∈ N.singletonSourceVariety κ := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun j _ =>
        (N.singletonSourceVariety κ).smul_mem _ (N.singletonSourceVarietyBasis_mem κ B j)
    have hfun : (fun s => ∑ j, u j * (B j : S → ℝ) s)
        = ((∑ j, u j • B j : N.singletonSourceVariety κ) : S → ℝ) := by
      funext s
      exact (coe_sum_smul (N.singletonSourceVariety κ) B u s).symm
    have hmem' : (fun s => ∑ j, u j * (B j : S → ℝ) s) ∈ N.singletonSourceVariety κ := by
      rw [hfun]
      exact hmem
    have hx' : N.IsMassActionSteadyState κ (fun s => ∑ j, u j * (B j : S → ℝ) s) :=
      (mem_singletonSourceVariety_iff N κ hM (fun s => ∑ j, u j * (B j : S → ℝ) s)).mp hmem'
    refine ⟨?_, hx'⟩
    intro s
    show 0 < ∑ j, u j * (B j : S → ℝ) s
    exact hu s

/-- **The linear variety is spanned by the torus.**  For a SingletonSource network with a
homogeneous binomial presentation of its steady-state equations, the linear
steady-state variety is the linear span of the torus `exp (ker (aᵢ − bᵢ))`. -/
theorem singletonSource_toric_variety_eq_span_torus (N : Network S) (κ : N.RateConstants)
    (hM : SingletonSource N) {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (hc1 : ∀ i, c i = 1)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs) :
    N.singletonSourceVariety κ = Submodule.span ℝ { expVec v | v ∈ expLogKernel a b } := by
  have hker : ∀ v ∈ expLogKernel a b, expVec v ∈ N.singletonSourceVariety κ := by
    intro v hv
    have hmem : expVec v ∈ { x : Concentration S | x.Positive ∧ N.IsMassActionSteadyState κ x } := by
      rw [toric_steadyStates_eq_exp_kernel N κ a b c hc hc1 htor hxs hxss]
      exact ⟨v, hv, rfl⟩
    have hmem' : expVec v ∈ N.singletonSourceVariety κ := by
      have h1 : Concentration.Positive (expVec v) ∧
          N.IsMassActionSteadyState κ (expVec v) :=
        Set.mem_ofPred_eq.mp hmem
      exact (mem_singletonSourceVariety_iff N κ hM (expVec v)).mpr h1.2
    exact hmem'
  apply le_antisymm
  · intro x hx
    -- the constant vector `1` lies in the torus, hence in the variety
    have hone : (1 : S → ℝ) ∈ N.singletonSourceVariety κ := by
      have h := hker 0 (expLogKernel a b).zero_mem
      rwa [← show (1 : S → ℝ) = expVec 0 by funext s; simp [expVec]] at h
    -- shift `x` into the positive orthant
    set t : ℝ := (∑ s, max (-x s) 0) + 1 with ht
    have hpos : ∀ s, 0 < x s + t := by
      intro s
      have h1 : max (-x s) 0 ≤ ∑ y, max (-x y) 0 :=
        Finset.single_le_sum (fun y _ => le_max_right (-x y) 0) (a := s) (Finset.mem_univ s)
      have h2 : 0 ≤ ∑ y, max (-x y) 0 := Finset.sum_nonneg fun y _ => le_max_right _ _
      have h3 : -x s ≤ max (-x s) 0 := le_max_left _ _
      rw [ht]
      linarith
    have hmem : x + t • (1 : S → ℝ) ∈ N.singletonSourceVariety κ :=
      (N.singletonSourceVariety κ).add_mem hx ((N.singletonSourceVariety κ).smul_mem t hone)
    have hpos' : Concentration.Positive (x + t • (1 : S → ℝ)) := fun s => by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have h1s : (1 : S → ℝ) s = 1 := rfl
      rw [h1s, mul_one]
      exact hpos s
    have hss : N.IsMassActionSteadyState κ (x + t • (1 : S → ℝ)) :=
      (mem_singletonSourceVariety_iff N κ hM (x + t • (1 : S → ℝ))).mp hmem
    have himg : x + t • (1 : S → ℝ) ∈ { fun s => Real.exp (v s) | v ∈ expLogKernel a b } := by
      rw [← toric_steadyStates_eq_exp_kernel N κ a b c hc hc1 htor hxs hxss]
      exact ⟨hpos', hss⟩
    obtain ⟨v, hv, hxv⟩ := himg
    have hxv' : x + t • (1 : S → ℝ) = expVec v := by
      rw [← hxv]
      rfl
    have hspan : x ∈ Submodule.span ℝ { expVec v | v ∈ expLogKernel a b } := by
      have hxv'' : expVec v ∈ Submodule.span ℝ { expVec w | w ∈ expLogKernel a b } :=
        Submodule.subset_span ⟨v, mem_expLogKernel.mpr hv, rfl⟩
      have hone' : (1 : S → ℝ) ∈ Submodule.span ℝ { expVec w | w ∈ expLogKernel a b } := by
        have hone'' : (1 : S → ℝ) = expVec 0 := by
          funext s
          simp [expVec]
        rw [hone'']
        exact Submodule.subset_span ⟨0, (expLogKernel a b).zero_mem, rfl⟩
      have h1 : x + t • (1 : S → ℝ)
          ∈ Submodule.span ℝ { expVec w | w ∈ expLogKernel a b } := by
        rw [hxv']
        exact hxv''
      have h2 : (x + t • (1 : S → ℝ)) - t • (1 : S → ℝ)
          ∈ Submodule.span ℝ { expVec w | w ∈ expLogKernel a b } :=
        (Submodule.span ℝ _).sub_mem h1 ((Submodule.span ℝ _).smul_mem t hone')
      have h3 : x = (x + t • (1 : S → ℝ)) - t • (1 : S → ℝ) := by
        funext s
        simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        ring
      rw [h3]
      exact h2
    exact hspan
  · apply Submodule.span_le.2
    intro u hu
    obtain ⟨v, hv, rfl⟩ := hu
    exact hker v hv

/-! ## General steady-state invariants -/

/-- A function `g` is a **general steady-state invariant** of `N` at the rate constants
`κ` when it takes the same value at every mass-action steady state.  This is the
general (not necessarily linear) version of `CRNT.Network.IsSteadyStateInvariant`,
which is restricted to *linear* functionals `w ↦ ∑ i, w i * x i`. -/
def IsSteadyStateInvariantFun (N : Network S) (κ : N.RateConstants)
    (g : Concentration S → ℝ) : Prop :=
  ∀ x y : Concentration S, N.IsMassActionSteadyState κ x → N.IsMassActionSteadyState κ y →
    g x = g y

/-- A function `g` is a **general invariant of the positive steady states** of `N` at the
rate constants `κ` when it takes the same value at every *positive* mass-action steady
state. -/
def IsPositiveSteadyStateInvariant (N : Network S) (κ : N.RateConstants)
    (g : Concentration S → ℝ) : Prop :=
  ∀ x y : Concentration S, x.Positive → N.IsMassActionSteadyState κ x →
    y.Positive → N.IsMassActionSteadyState κ y → g x = g y

/-- **Steady-state invariants of a toric network.**  A function that is constant along
the torus orbit `x* · exp v` (with `v` in the log-kernel of the exponent differences)
is constant on the positive steady states: the positive steady states of a toric network
form a single torus orbit. -/
theorem steadyStateInvariant_of_log_orthogonal
    (N : Network S) (κ : N.RateConstants) {n : ℕ} (a b : Fin n → Complex S)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (g : Concentration S → ℝ)
    (horb : ∀ v ∈ expLogKernel a b, g (toricParametrization xs v) = g xs) :
    ∀ x y : Concentration S, x.Positive → N.IsMassActionSteadyState κ x →
      y.Positive → N.IsMassActionSteadyState κ y → g x = g y := by
  intro x y hx hxx hy hyy
  obtain ⟨v, hv, hxv⟩ :=
    N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss x hx hxx
  obtain ⟨w, hw, hyw⟩ :=
    N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss y hy hyy
  rw [hxv, hyw]
  calc g (toricParametrization xs v) = g xs := horb v (mem_expLogKernel.mpr hv)
    _ = g (toricParametrization xs w) := (horb w (mem_expLogKernel.mpr hw)).symm

/-- **Complete characterization of the general invariants of a toric network.**  A
function is an invariant of the positive steady states of a toric network if and only if
it is constant along the torus orbit of the reference steady state. -/
theorem steadyStateInvariant_iff_log_orthogonal
    (N : Network S) (κ : N.RateConstants) {n : ℕ} (a b : Fin n → Complex S)
    (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (g : Concentration S → ℝ) :
    (∀ x y : Concentration S, x.Positive → N.IsMassActionSteadyState κ x →
      y.Positive → N.IsMassActionSteadyState κ y → g x = g y) ↔
      ∀ v ∈ expLogKernel a b, g (toricParametrization xs v) = g xs := by
  constructor
  · intro h v hv
    have hmem : v ∈ expLogKernel a b := hv
    have hss := N.toric_parametrization_isSteadyState κ a b c hc htor hxs hxss v
      (mem_expLogKernel.mp hmem)
    exact h (toricParametrization xs v) xs hss.1 hss.2 hxs hxss
  · intro h x y hx hxx hy hyy
    obtain ⟨v, hv, hxv⟩ :=
      N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss x hx hxx
    obtain ⟨w, hw, hyw⟩ :=
      N.toric_steadyState_exists_parametrization κ a b c hc htor hxs hxss y hy hyy
    rw [hxv, hyw]
    calc g (toricParametrization xs v) = g xs := h v (mem_expLogKernel.mpr hv)
      _ = g (toricParametrization xs w) := (h w (mem_expLogKernel.mpr hw)).symm

/-- **The general invariants of a SingletonSource network are the functions constant on the
steady-state variety.**  The steady-state variety of a SingletonSource network is a linear
subspace, so the general invariants are exactly the functions that are constant on it. -/
theorem singletonSource_generalInvariant_iff_constantOnVariety (N : Network S) (κ : N.RateConstants)
    (hM : SingletonSource N) (g : Concentration S → ℝ) :
    IsSteadyStateInvariantFun N κ g ↔ ∀ x ∈ N.singletonSourceVariety κ, g x = g 0 := by
  constructor
  · intro h x hx
    have hx' : N.IsMassActionSteadyState κ x := (mem_singletonSourceVariety_iff N κ hM x).mp hx
    have h0 : N.IsMassActionSteadyState κ 0 := N.singletonSource_zero_isSteadyState κ hM
    have hval := h x 0 hx' h0
    simpa using hval
  · intro h x y hx hy
    have hx' : x ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM x).mpr hx
    have hy' : y ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM y).mpr hy
    rw [h x hx', h y hy']

/-- **The general invariants of a SingletonSource network are determined by their value at the
origin.**  Since the steady-state variety is a linear subspace containing the origin, a
function constant on it is determined by the single number `g 0`. -/
theorem singletonSource_generalInvariant_iff_valueAtOrigin (N : Network S) (κ : N.RateConstants)
    (hM : SingletonSource N) (g : Concentration S → ℝ) :
    IsSteadyStateInvariantFun N κ g ↔
      ∃ c : ℝ, ∀ x, N.IsMassActionSteadyState κ x → g x = c := by
  constructor
  · intro h
    refine ⟨g 0, ?_⟩
    intro x hx
    have hx' : x ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM x).mpr hx
    have h0 : N.IsMassActionSteadyState κ 0 := N.singletonSource_zero_isSteadyState κ hM
    have hval := h x 0 hx h0
    simpa using hval
  · rintro ⟨c, hc⟩ x y hx hy
    rw [hc x hx, hc y hy]

/-- **Algebraic characterization of the general invariants of a linear variety.**  With a
basis of the steady-state variety, a function is an invariant if and only if it is
constant on the linear parametrization of the variety; equivalently, it is determined by
its value at the origin. -/
theorem singletonSource_generalInvariant_iff_linearParametrization (N : Network S)
    (κ : N.RateConstants) (hM : SingletonSource N)
    (B : Module.Basis (Fin (Module.finrank ℝ (N.singletonSourceVariety κ))) ℝ (N.singletonSourceVariety κ))
    (g : Concentration S → ℝ) :
    IsSteadyStateInvariantFun N κ g ↔
      ∀ u : Fin (Module.finrank ℝ (N.singletonSourceVariety κ)) → ℝ,
        g (fun s => ∑ j, u j * (B j : S → ℝ) s) = g 0 := by
  rw [singletonSource_generalInvariant_iff_constantOnVariety N κ hM g]
  constructor
  · intro h u
    have hmem : ((∑ j, u j • B j : N.singletonSourceVariety κ) : S → ℝ) ∈ N.singletonSourceVariety κ := by
      rw [Submodule.coe_sum]
      exact Submodule.sum_mem _ fun j _ =>
        (N.singletonSourceVariety κ).smul_mem _ (N.singletonSourceVarietyBasis_mem κ B j)
    have hfun : (fun s => ∑ j, u j * (B j : S → ℝ) s)
        = ((∑ j, u j • B j : N.singletonSourceVariety κ) : S → ℝ) := by
      funext s
      exact (coe_sum_smul (N.singletonSourceVariety κ) B u s).symm
    rw [hfun]
    exact h _ hmem
  · intro h x hx
    obtain ⟨u, hu⟩ := (singletonSource_variety_eq_linearParametrization N κ B x).mp hx
    rw [hu]
    exact h u

/-- **The general invariants of the positive steady states of a SingletonSource network are the
functions constant on the positive part of the steady-state variety.** -/
theorem singletonSource_positiveInvariant_iff_constantOnPositiveVariety (N : Network S)
    (κ : N.RateConstants) (hM : SingletonSource N) (g : Concentration S → ℝ) :
    IsPositiveSteadyStateInvariant N κ g ↔
      ∀ x ∈ N.singletonSourceVariety κ, ∀ y ∈ N.singletonSourceVariety κ,
        Concentration.Positive x → Concentration.Positive y → g x = g y := by
  constructor
  · intro h x hx y hy hxp hyp
    have hxx : N.IsMassActionSteadyState κ x := (mem_singletonSourceVariety_iff N κ hM x).mp hx
    have hyy : N.IsMassActionSteadyState κ y := (mem_singletonSourceVariety_iff N κ hM y).mp hy
    exact h x y hxp hxx hyp hyy
  · intro h x y hxp hxx hyp hyy
    have hx' : x ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM x).mpr hxx
    have hy' : y ∈ N.singletonSourceVariety κ := (mem_singletonSourceVariety_iff N κ hM y).mpr hyy
    exact h x hx' y hy' hxp hyp


end Network

/-! ## A concrete instance: the reversible pair `X ⇌ Y` -/

namespace Examples.ToricParametrization

open CRNT

/-- The two species `X` and `Y` of the reversible pair. -/
abbrev Species : Type := CRNT.Examples.SingletonSource.Species

/-- The species `X`. -/
abbrev X : Species := CRNT.Examples.SingletonSource.X

/-- The species `Y`. -/
abbrev Y : Species := CRNT.Examples.SingletonSource.Y

/-- The network `X ⇌ Y`. -/
abbrev N : Network Species := CRNT.Examples.SingletonSource.N

/-- **The reversible pair `X ⇌ Y` at equal rate constants** `κ₁ = κ₂ = 1`.  At equal
rates the steady-state equation `κ₁ x_X = κ₂ x_Y` becomes the *homogeneous* binomial
`x_X = x_Y`, the simplest instance of the toric parametrization. -/
def rates : Network.RateConstants N :=
  CRNT.Examples.SingletonSource.rates 1 1 (by norm_num) (by norm_num)

/-- The forward rate constant is `1`. -/
theorem rates_k_fwd : rates.k CRNT.Examples.SingletonSource.fwd = 1 := by
  simp [rates, CRNT.Examples.SingletonSource.rates]

/-- The backward rate constant is `1`. -/
theorem rates_k_bwd : rates.k CRNT.Examples.SingletonSource.bwd = 1 := by
  simp [rates, CRNT.Examples.SingletonSource.rates]

/-- **The reversible pair at equal rates is a SingletonSource network.** -/
theorem N_singletonSource : N.SingletonSource := CRNT.Examples.SingletonSource.N_singletonSource

/-- **The steady states of `X ⇌ Y` at equal rates are the points with `x_X = x_Y`.** -/
theorem steadyState_iff (x : Concentration Species) :
    N.IsMassActionSteadyState rates x ↔ x X = x Y := by
  rw [CRNT.Examples.SingletonSource.steadyState_iff rates x]
  rw [rates_k_fwd, rates_k_bwd]
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- The mass-action monomial of the source complex `X` is `x_X`. -/
theorem massActionMonomial_cX (x : Concentration Species) :
    CRNT.Examples.SingletonSource.cX.massActionMonomial x = x X := by
  unfold Complex.massActionMonomial
  rw [Finset.prod_eq_single X]
  · simp [CRNT.Examples.SingletonSource.cX]
  · intro b _ hb
    fin_cases b
    · exact absurd rfl hb
    · simp [CRNT.Examples.SingletonSource.cX]
  · simp

/-- The mass-action monomial of the target complex `Y` is `x_Y`. -/
theorem massActionMonomial_cY (x : Concentration Species) :
    CRNT.Examples.SingletonSource.cY.massActionMonomial x = x Y := by
  unfold Complex.massActionMonomial
  rw [Finset.prod_eq_single Y]
  · simp [CRNT.Examples.SingletonSource.cY]
  · intro b _ hb
    fin_cases b
    · simp [CRNT.Examples.SingletonSource.cY]
    · exact absurd rfl hb
  · simp

/-- The exponent `a` of the homogeneous binomial `x ^ a = x ^ b`: the complex `X`. -/
def a : Fin 1 → Complex Species := fun _ => CRNT.Examples.SingletonSource.cX

/-- The exponent `b` of the homogeneous binomial `x ^ a = x ^ b`: the complex `Y`. -/
def b : Fin 1 → Complex Species := fun _ => CRNT.Examples.SingletonSource.cY

/-- The binomial coefficient: `1`, i.e. the binomial is *homogeneous*. -/
def c : Fin 1 → ℝ := fun _ => 1

/-- The pairing of the exponent differences of the binomial `x_X = x_Y` is `v_X − v_Y`. -/
theorem expPairing_cX_cY (v : Species → ℝ) :
    expPairing CRNT.Examples.SingletonSource.cX CRNT.Examples.SingletonSource.cY v = v X - v Y := by
  unfold expPairing
  simp [CRNT.Examples.SingletonSource.cX, CRNT.Examples.SingletonSource.cY, Fin.sum_univ_two]
  ring

/-- **The log-kernel of the binomial `x_X = x_Y`** is the set of log-vectors with
`v_X = v_Y`. -/
theorem mem_logKernel_iff (v : Species → ℝ) :
    v ∈ expLogKernel a b ↔ v X = v Y := by
  rw [mem_expLogKernel]
  constructor
  · intro h
    have h1 := h 0
    simp only [a, b] at h1
    rw [expPairing_cX_cY] at h1
    linarith
  · intro h i
    fin_cases i
    simp only [a, b]
    rw [expPairing_cX_cY]
    linarith

/-- **The binomial presentation of the steady-state equations of `X ⇌ Y` at equal
rates**: the positive steady states are exactly the solutions of the homogeneous
binomial `x ^ a = x ^ b` with `a = X`, `b = Y`. -/
theorem htor_binomial (x : Concentration Species) (_hx : Concentration.Positive x) :
    N.IsMassActionSteadyState rates x ↔
      ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x := by
  constructor
  · intro h
    have h1 := (steadyState_iff x).mp h
    intro i
    fin_cases i
    simp only [a, b, c, massActionMonomial_cX, massActionMonomial_cY]
    linarith
  · intro h
    have h1 := h 0
    simp only [a, b, c, massActionMonomial_cX, massActionMonomial_cY] at h1
    exact (steadyState_iff x).mpr (by linarith)

/-- The reference steady state `x* = (1, 1)`. -/
def xs : Concentration Species := fun _ => 1

/-- The reference steady state is positive. -/
theorem xs_positive : Concentration.Positive xs := by
  intro s
  simp [xs]

/-- The reference steady state is a steady state. -/
theorem xs_isSteadyState : N.IsMassActionSteadyState rates xs := by
  rw [steadyState_iff]
  simp [xs]

/-- **The exponential log-kernel parametrization of the steady-state variety of `X ⇌ Y` at equal
rates.**  The positive steady states are exactly the exponentials of the vectors in the
kernel of the exponent-difference matrix, i.e. of the vectors with `v_X = v_Y`. -/
theorem positiveSteadyStates_eq_exp_kernel :
    { x : Concentration Species | x.Positive ∧ N.IsMassActionSteadyState rates x }
      = { fun s => Real.exp (v s) | v ∈ expLogKernel a b } := by
  refine CRNT.Network.toric_steadyStates_eq_exp_kernel N rates a b c ?_ ?_ htor_binomial
    xs_positive xs_isSteadyState
  · intro i
    fin_cases i
    simp [c]
  · intro i
    fin_cases i
    rfl

/-- **The positive steady states of `X ⇌ Y` at equal rates are the diagonal ray.** -/
theorem positiveSteadyStates_eq_diagonal :
    { x : Concentration Species | x.Positive ∧ N.IsMassActionSteadyState rates x }
      = { x : Concentration Species | x.Positive ∧ x X = x Y } := by
  ext x
  constructor
  · rintro ⟨hx, hss⟩
    refine ⟨hx, ?_⟩
    exact (steadyState_iff x).mp hss
  · rintro ⟨hx, hxy⟩
    refine ⟨hx, ?_⟩
    exact (steadyState_iff x).mpr hxy

/-- **The torus of the reversible pair.**  The torus `exp (ker)` consists of the vectors
`(e^t, e^t)`: it is a one-dimensional torus. -/
theorem mem_toricTorus_iff (u : Species → ℝ) :
    u ∈ toricTorus a b ↔ ∃ t : ℝ, u = fun _ => Real.exp t := by
  constructor
  · rintro ⟨v, hv, rfl⟩
    have h1 : v X = v Y := (mem_logKernel_iff v).mp hv
    refine ⟨v X, ?_⟩
    funext s
    fin_cases s
    · simp [expVec]
    · rw [h1]
      simp [expVec]
  · rintro ⟨t, rfl⟩
    refine ⟨fun _ => t, ?_, rfl⟩
    exact (mem_logKernel_iff (fun _ => t)).mpr (by simp)

/-- **A nonlinear invariant of the positive steady states of `X ⇌ Y` at equal rates:**
the ratio `x_X / x_Y`, which is identically `1` on the diagonal ray. -/
noncomputable def ratio (x : Concentration Species) : ℝ := x X / x Y

/-- **The ratio is a general invariant of the positive steady states.** -/
theorem ratio_isPositiveSteadyStateInvariant :
    Network.IsPositiveSteadyStateInvariant N rates ratio := by
  intro x y hx hxx hy hyy
  have h1 := (steadyState_iff x).mp hxx
  have h2 := (steadyState_iff y).mp hyy
  simp only [ratio]
  rw [h1, h2]
  have hxY : x Y ≠ 0 := ne_of_gt (hx Y)
  have hyY : y Y ≠ 0 := ne_of_gt (hy Y)
  field_simp

/-- **The ratio is *not* an invariant of all steady states**: it is not defined (and not
constant) on the origin, which is a steady state of the linear variety.  This shows
that the general invariants of the positive steady states are strictly more numerous
than the invariants of the whole variety. -/
theorem ratio_notSteadyStateInvariantFun :
    ¬ Network.IsSteadyStateInvariantFun N rates ratio := by
  intro h
  have h0 : N.IsMassActionSteadyState rates 0 := by
    rw [steadyState_iff]
    simp
  have h1 : N.IsMassActionSteadyState rates (fun _ => 1) := by
    rw [steadyState_iff]
  have hval := h (fun _ => 1) 0 h1 h0
  simp only [ratio] at hval
  norm_num at hval

/-- **The linear invariant of `X ⇌ Y` at equal rates is `(1, −1)`**, in contrast with the
nonlinear invariant `x_X / x_Y`. -/
theorem linearInvariant_isSteadyStateInvariant :
    Network.IsSteadyStateInvariant N rates (fun s => if s = X then (1 : ℝ) else -1) := by
  rw [Network.singletonSource_linearInvariant_iff N rates N_singletonSource]
  intro x hx
  have hX := hx X
  simp only [Fin.sum_univ_two] at hX
  rw [CRNT.Examples.SingletonSource.singletonSourceCoeff_XX, CRNT.Examples.SingletonSource.singletonSourceCoeff_YX] at hX
  rw [rates_k_fwd, rates_k_bwd] at hX
  simp only [Fin.sum_univ_two]
  simp [X]
  linarith

end Examples.ToricParametrization

end CRNT
