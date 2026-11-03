import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Finset.Max
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-!
# Positive solutions of polynomial systems supported on a circuit (Bihan's bound)

A system of `n` equations in `n` positive unknowns, linear in `y` except for one extra monomial,

`C y + c₀ + c₁ y^μ = 0`  (`C` invertible, real exponents `μ`),

has at most `n + 1` positive solutions, unless a degenerate polynomial identity holds
(`card_circuit_solutions_le`). This is Bihan's bound for systems supported on a circuit of
`n + 2` monomials, in the normal form obtained after the monomial change of variables.

Solving the linear part, `y = p + t q` with `t = y^μ`, so positive solutions correspond injectively
to zeros `t` of `φ(t) = ∑_k μ_k log(p_k + t q_k) − log t` on the interval where all `p_k + t q_k`
and `t` are positive. Between two consecutive zeros Rolle's theorem gives a zero of
`φ'(t) = ∑_k μ_k q_k/(p_k + t q_k) − 1/t`, hence a root of the numerator polynomial
`P(t) = t ∑_k μ_k q_k ∏_{l ≠ k}(p_l + t q_l) − ∏_k (p_k + t q_k)` of degree at most `n`
(`circuitPoly`, `natDegree_circuitPoly_le`); `Finset.card_le_of_interleaved` turns this into the
count `#zeros ≤ #roots(P) + 1 ≤ n + 1` (`card_log_affine_zeros_le`).
-/

open Polynomial Finset Set

namespace CRNT
namespace Circuit

variable {n : ℕ}

/-- The numerator of `φ'`. -/
noncomputable def circuitPoly (p q μ : Fin n → ℝ) : ℝ[X] :=
  X * ∑ k, C (μ k * q k) * ∏ l ∈ univ.erase k, (C (p l) + C (q l) * X) -
    ∏ k, (C (p k) + C (q k) * X)

theorem natDegree_linear_le (a b : ℝ) : (C a + C b * X).natDegree ≤ 1 := by
  refine (natDegree_add_le _ _).trans (max_le ?_ ?_)
  · simp
  · exact (natDegree_C_mul_le _ _).trans (by simp)

theorem natDegree_prod_linear_le (p q : Fin n → ℝ) (s : Finset (Fin n)) :
    (∏ l ∈ s, (C (p l) + C (q l) * X)).natDegree ≤ s.card := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    have := natDegree_linear_le (p a) (q a)
    exact (natDegree_mul_le).trans (by omega)

theorem natDegree_circuitPoly_le (p q μ : Fin n → ℝ) : (circuitPoly p q μ).natDegree ≤ n := by
  unfold circuitPoly
  refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
  · rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · refine (natDegree_mul_le).trans ?_
      have h1 : (X : ℝ[X]).natDegree ≤ 1 := natDegree_X_le
      have h2 : (∑ k, C (μ k * q k) * ∏ l ∈ univ.erase k, (C (p l) + C (q l) * X)).natDegree ≤
          n - 1 := by
        refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
        refine (natDegree_C_mul_le _ _).trans ?_
        refine (natDegree_prod_linear_le p q _).trans ?_
        rw [Finset.card_erase_of_mem (mem_univ k), Finset.card_univ, Fintype.card_fin]
      omega
  · refine (natDegree_prod_linear_le p q univ).trans ?_
    simp

/-- The interval of admissible `t`. -/
def admissible (p q : Fin n → ℝ) : Set ℝ := {t | 0 < t ∧ ∀ k, 0 < p k + t * q k}

theorem convex_admissible (p q : Fin n → ℝ) : Convex ℝ (admissible p q) := by
  intro x hx y hy a b ha hb hab
  refine ⟨?_, fun k => ?_⟩
  · have := hx.1; have := hy.1
    simp only [smul_eq_mul]
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; simpa using hy.1
    · nlinarith [mul_pos h hx.1]
  · have h1 := hx.2 k
    have h2 := hy.2 k
    simp only [smul_eq_mul]
    have : p k + (a * x + b * y) * q k = a * (p k + x * q k) + b * (p k + y * q k) := by
      linear_combination (-(p k)) * hab
    rw [this]
    rcases eq_or_lt_of_le ha with h | h
    · subst h; simp at hab; subst hab; simpa using h2
    · nlinarith [mul_pos h h1, mul_nonneg hb h2.le]

/-- The function whose zeros are the solutions. -/
noncomputable def phi (p q μ : Fin n → ℝ) (t : ℝ) : ℝ :=
  ∑ k, μ k * Real.log (p k + t * q k) - Real.log t

theorem hasDerivAt_phi (p q μ : Fin n → ℝ) {t : ℝ} (ht : t ∈ admissible p q) :
    HasDerivAt (phi p q μ) (∑ k, μ k * (q k / (p k + t * q k)) - 1 / t) t := by
  unfold phi
  have hk : ∀ k, HasDerivAt (fun t => μ k * Real.log (p k + t * q k))
      (μ k * (q k / (p k + t * q k))) t := by
    intro k
    have h1 : HasDerivAt (fun t => p k + t * q k) (q k) t := by
      simpa using ((hasDerivAt_id t).mul_const (q k)).const_add (p k)
    have h2 := h1.log (ht.2 k).ne'
    exact h2.const_mul (μ k)
  have hsum := HasDerivAt.fun_sum (u := univ) (A := fun k t => μ k * Real.log (p k + t * q k))
    (A' := fun k => μ k * (q k / (p k + t * q k))) fun k _ => hk k
  have hlog := (Real.hasDerivAt_log ht.1.ne')
  convert hsum.sub hlog using 1
  simp [one_div]

/-- At a zero of `φ'`, the numerator vanishes. -/
theorem circuitPoly_eval_eq_zero (p q μ : Fin n → ℝ) {t : ℝ} (ht : t ∈ admissible p q)
    (h : ∑ k, μ k * (q k / (p k + t * q k)) - 1 / t = 0) : (circuitPoly p q μ).eval t = 0 := by
  have hpos : ∀ k, p k + t * q k ≠ 0 := fun k => (ht.2 k).ne'
  have ht0 : t ≠ 0 := ht.1.ne'
  have hprod : ∀ k, (∏ l ∈ univ.erase k, (p l + t * q l)) * (p k + t * q k) =
      ∏ l, (p l + t * q l) := fun k => Finset.prod_erase_mul _ _ (mem_univ k)
  have heval : (circuitPoly p q μ).eval t =
      t * ∑ k, μ k * q k * ∏ l ∈ univ.erase k, (p l + t * q l) - ∏ k, (p k + t * q k) := by
    unfold circuitPoly
    simp only [eval_sub, eval_mul, eval_X, eval_finset_sum, eval_prod, eval_add, eval_C]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 1
      exact Finset.prod_congr rfl fun l _ => by ring
    · exact Finset.prod_congr rfl fun l _ => by ring
  rw [heval]
  have h1 : ∑ k, μ k * (q k / (p k + t * q k)) = 1 / t := by linarith
  have h2 : ∑ k, μ k * q k * ∏ l ∈ univ.erase k, (p l + t * q l) =
      (∑ k, μ k * (q k / (p k + t * q k))) * ∏ l, (p l + t * q l) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hprod k]
    have hk := hpos k
    calc μ k * q k * ∏ l ∈ univ.erase k, (p l + t * q l)
        = μ k * q k * (∏ l ∈ univ.erase k, (p l + t * q l)) *
            ((p k + t * q k) / (p k + t * q k)) := by rw [div_self hk, mul_one]
      _ = μ k * (q k / (p k + t * q k)) *
            ((∏ l ∈ univ.erase k, (p l + t * q l)) * (p k + t * q k)) := by ring
  rw [h2, h1]
  field_simp
  ring

/-- **Counting zeros.** If `P ≠ 0`, `φ` has at most `n + 1` zeros in the admissible interval. -/
theorem card_log_affine_zeros_le (p q μ : Fin n → ℝ) (hP : circuitPoly p q μ ≠ 0)
    (Z : Finset ℝ) (hZ : ∀ t ∈ Z, t ∈ admissible p q ∧ phi p q μ t = 0) : Z.card ≤ n + 1 := by
  have h := Finset.card_le_of_interleaved (s := Z) (t := (circuitPoly p q μ).roots.toFinset)
    fun x hx y hy hxy _ => by
      have hxI := (hZ x hx).1
      have hyI := (hZ y hy).1
      have hseg : Icc x y ⊆ admissible p q :=
        (convex_admissible p q).segment_subset hxI hyI |>.trans' (by
          rw [segment_eq_Icc hxy.le])
      have hcont : ContinuousOn (phi p q μ) (Icc x y) := fun t ht =>
        (hasDerivAt_phi p q μ (hseg ht)).continuousAt.continuousWithinAt
      have heq : phi p q μ x = phi p q μ y := by rw [(hZ x hx).2, (hZ y hy).2]
      obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hxy hcont heq
      have hcI : c ∈ admissible p q := hseg (Ioo_subset_Icc_self hc)
      have hd := (hasDerivAt_phi p q μ hcI).deriv
      rw [hdc] at hd
      refine ⟨c, ?_, hc.1, hc.2⟩
      rw [Multiset.mem_toFinset, mem_roots hP, IsRoot]
      exact circuitPoly_eval_eq_zero p q μ hcI hd.symm
  have h2 : (circuitPoly p q μ).roots.toFinset.card ≤ n :=
    (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (natDegree_circuitPoly_le p q μ))
  omega

/-- The monomial `y^μ` with real exponents. -/
noncomputable def rmono (μ : Fin n → ℝ) (y : Fin n → ℝ) : ℝ := ∏ k, y k ^ μ k

/-- **Bihan's bound for circuit systems (normal form).** A system `C y + c₀ + y^μ c₁ = 0` with `C`
invertible has at most `n + 1` positive solutions, unless the numerator polynomial of
`p = −C⁻¹ c₀`, `q = −C⁻¹ c₁` vanishes identically. -/
theorem card_circuit_solutions_le (Cm : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit Cm.det)
    (c₀ c₁ μ : Fin n → ℝ)
    (hP : circuitPoly (-(Cm⁻¹.mulVec c₀)) (-(Cm⁻¹.mulVec c₁)) μ ≠ 0)
    (Y : Finset (Fin n → ℝ))
    (hY : ∀ y ∈ Y, (∀ k, 0 < y k) ∧ Cm.mulVec y + c₀ + rmono μ y • c₁ = 0) :
    Y.card ≤ n + 1 := by
  classical
  set p : Fin n → ℝ := -(Cm⁻¹.mulVec c₀) with hp
  set q : Fin n → ℝ := -(Cm⁻¹.mulVec c₁) with hq
  have hsol : ∀ y ∈ Y, y = p + rmono μ y • q := by
    intro y hy
    have h := (hY y hy).2
    have hy' : Cm.mulVec y = -(c₀ + rmono μ y • c₁) := by
      rw [eq_neg_iff_add_eq_zero, ← add_assoc]; exact h
    have hinv : Cm⁻¹ * Cm = 1 := Matrix.nonsing_inv_mul Cm hC
    calc y = (Cm⁻¹ * Cm).mulVec y := by rw [hinv, Matrix.one_mulVec]
      _ = Cm⁻¹.mulVec (Cm.mulVec y) := by rw [Matrix.mulVec_mulVec]
      _ = p + rmono μ y • q := by
          rw [hy', Matrix.mulVec_neg, Matrix.mulVec_add, Matrix.mulVec_smul, hp, hq]
          simp only [neg_add, smul_neg]
  have hpos : ∀ y ∈ Y, 0 < rmono μ y := fun y hy =>
    Finset.prod_pos fun k _ => Real.rpow_pos_of_pos ((hY y hy).1 k) _
  have hcoord : ∀ y ∈ Y, ∀ k, y k = p k + rmono μ y * q k := by
    intro y hy k
    have := congrFun (hsol y hy) k
    simpa using this
  have hinj : Set.InjOn (rmono μ) Y := by
    intro y hy y' hy' h
    rw [hsol y hy, hsol y' hy', h]
  have hZ : ∀ t ∈ Y.image (rmono μ), t ∈ admissible p q ∧ phi p q μ t = 0 := by
    intro t ht
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp ht
    refine ⟨⟨hpos y hy, fun k => ?_⟩, ?_⟩
    · rw [← hcoord y hy k]; exact (hY y hy).1 k
    · unfold phi
      have hlog : Real.log (rmono μ y) = ∑ k, μ k * Real.log (y k) := by
        unfold rmono
        rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos ((hY y hy).1 k) _).ne']
        exact Finset.sum_congr rfl fun k _ => by
          rw [Real.log_rpow ((hY y hy).1 k)]
      rw [hlog]
      have : ∀ k, Real.log (p k + rmono μ y * q k) = Real.log (y k) := fun k => by
        rw [← hcoord y hy k]
      simp only [this, sub_self]
  have h := card_log_affine_zeros_le p q μ hP (Y.image (rmono μ)) hZ
  rwa [Finset.card_image_of_injOn hinj] at h


/-- The monomials `x^{w_k}` with exponent vectors the rows of `E`. -/
noncomputable def monoMap (E : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) : Fin n → ℝ :=
  fun k => ∏ i, x i ^ E k i

theorem log_monoMap (E : Matrix (Fin n) (Fin n) ℝ) {x : Fin n → ℝ} (hx : ∀ i, 0 < x i) (k : Fin n) :
    Real.log (monoMap E x k) = (E.mulVec fun i => Real.log (x i)) k := by
  unfold monoMap
  rw [Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hx i) _).ne', Matrix.mulVec, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by rw [Real.log_rpow (hx i)]

theorem monoMap_injOn (E : Matrix (Fin n) (Fin n) ℝ) (hE : IsUnit E.det) {x x' : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) (hx' : ∀ i, 0 < x' i) (h : monoMap E x = monoMap E x') : x = x' := by
  have hlog : E.mulVec (fun i => Real.log (x i)) = E.mulVec (fun i => Real.log (x' i)) := by
    funext k
    rw [← log_monoMap E hx k, ← log_monoMap E hx' k, h]
  have hinv : E⁻¹ * E = 1 := Matrix.nonsing_inv_mul E hE
  have h2 : (fun i => Real.log (x i)) = (fun i => Real.log (x' i)) := by
    calc (fun i => Real.log (x i)) = (E⁻¹ * E).mulVec (fun i => Real.log (x i)) := by
          rw [hinv, Matrix.one_mulVec]
      _ = (E⁻¹ * E).mulVec (fun i => Real.log (x' i)) := by
          rw [← Matrix.mulVec_mulVec, hlog, Matrix.mulVec_mulVec]
      _ = fun i => Real.log (x' i) := by rw [hinv, Matrix.one_mulVec]
  funext i
  exact Real.log_injOn_pos (hx i) (hx' i) (congrFun h2 i)

/-- The extra monomial `x^{Eᵀ μ} = (x^{w})^μ`. -/
theorem rmono_monoMap (E : Matrix (Fin n) (Fin n) ℝ) (μ : Fin n → ℝ) {x : Fin n → ℝ}
    (hx : ∀ i, 0 < x i) :
    rmono μ (monoMap E x) = ∏ i, x i ^ (E.transpose.mulVec μ) i := by
  have hpos : 0 < rmono μ (monoMap E x) := Finset.prod_pos fun k _ =>
    Real.rpow_pos_of_pos (Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _) _
  have hpos' : 0 < ∏ i, x i ^ (E.transpose.mulVec μ) i :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
  have hmpos : ∀ k, 0 < monoMap E x k := fun k =>
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (hx i) _
  refine Real.log_injOn_pos hpos hpos' ?_
  unfold rmono
  rw [Real.log_prod fun k _ => (Real.rpow_pos_of_pos (hmpos k) _).ne',
    Real.log_prod fun i _ => (Real.rpow_pos_of_pos (hx i) _).ne']
  simp only [Real.log_rpow (hmpos _), Real.log_rpow (hx _), log_monoMap E hx, Matrix.mulVec,
    dotProduct, Matrix.transpose_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

/-- **Bihan's bound for systems supported on a circuit.** Let the monomials be `1`, `x^{w_1}`, …,
`x^{w_n}` (the rows of an invertible `E`) and `x^{w_{n+1}}` with `w_{n+1} = ∑_k μ_k w_k`. If the
coefficient matrix of `x^{w_1}, …, x^{w_n}` is invertible, the system has at most `n + 1` positive
solutions (unless the numerator polynomial vanishes identically). -/
theorem card_circuit_solutions_le_monomial (E : Matrix (Fin n) (Fin n) ℝ) (hE : IsUnit E.det)
    (Cm : Matrix (Fin n) (Fin n) ℝ) (hC : IsUnit Cm.det) (c₀ c₁ μ : Fin n → ℝ)
    (hP : circuitPoly (-(Cm⁻¹.mulVec c₀)) (-(Cm⁻¹.mulVec c₁)) μ ≠ 0)
    (Xs : Finset (Fin n → ℝ))
    (hX : ∀ x ∈ Xs, (∀ i, 0 < x i) ∧
      Cm.mulVec (monoMap E x) + c₀ + (∏ i, x i ^ (E.transpose.mulVec μ) i) • c₁ = 0) :
    Xs.card ≤ n + 1 := by
  classical
  have hinj : Set.InjOn (monoMap E) Xs := fun x hx x' hx' h =>
    monoMap_injOn E hE (hX x hx).1 (hX x' hx').1 h
  have hY : ∀ y ∈ Xs.image (monoMap E), (∀ k, 0 < y k) ∧
      Cm.mulVec y + c₀ + rmono μ y • c₁ = 0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    refine ⟨fun k => Finset.prod_pos fun i _ => Real.rpow_pos_of_pos ((hX x hx).1 i) _, ?_⟩
    rw [rmono_monoMap E μ (hX x hx).1]
    exact (hX x hx).2
  have h := card_circuit_solutions_le Cm hC c₀ c₁ μ hP (Xs.image (monoMap E)) hY
  rwa [Finset.card_image_of_injOn hinj] at h

end Circuit
end CRNT

namespace CRNT
namespace Circuit
namespace Example

/-! ### Sharpness for `n = 1`: `y − 2/3 − y²/3 = 0` has the two positive solutions `1` and `2`. -/

/-- The two solutions. -/
noncomputable def sols : Finset (Fin 1 → ℝ) := {fun _ => 1, fun _ => 2}

theorem hP : circuitPoly (-((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹.mulVec (fun _ => -(2 / 3))))
    (-((1 : Matrix (Fin 1) (Fin 1) ℝ)⁻¹.mulVec (fun _ => -(1 / 3)))) (fun _ => 2) ≠ 0 := by
  intro h
  have h0 := congrArg (Polynomial.eval 0) h
  simp [circuitPoly] at h0

theorem sols_solve : ∀ y ∈ sols, (∀ k, 0 < y k) ∧
    (1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec y + (fun _ => -(2 / 3)) +
      rmono (fun _ => 2) y • (fun _ => -(1 / 3)) = 0 := by
  intro y hy
  simp only [sols, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl
  · refine ⟨fun _ => one_pos, ?_⟩
    funext k
    simp [rmono]
    norm_num
  · refine ⟨fun _ => two_pos, ?_⟩
    funext k
    simp [rmono]
    norm_num

theorem card_sols : sols.card = 1 + 1 := by
  simp only [sols]
  rw [Finset.card_pair]
  intro h
  have := congrFun h 0
  norm_num at this

/-- The bound `n + 1 = 2` is attained. -/
theorem bound_attained : sols.card = 1 + 1 ∧ sols.card ≤ 1 + 1 :=
  ⟨card_sols, card_circuit_solutions_le 1 (by simp) _ _ _ hP sols sols_solve⟩

end Example
end Circuit
end CRNT
