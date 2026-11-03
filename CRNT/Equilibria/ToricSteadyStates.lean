import CRNT.Equilibria.SteadyState
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Toric steady states and their monomial parametrization

Following Pérez Millán, Dickenstein, Shiu and Conradi (*Chemical reaction systems with toric
steady states*, Bull. Math. Biol. 74 (2012)), a mass-action system **has toric steady states**
when its positive steady states are exactly the positive zeros of a finite family of
binomials `x ^ aᵢ - cᵢ x ^ bᵢ` with `cᵢ > 0`.

The basic structural theorem (loc. cit., Theorem 3.8 and §3.2) is that such a steady-state
set, if nonempty, is a log-affine set: fixing one positive steady state `x*`,
`x` is a positive steady state iff `log x - log x*` is orthogonal to every exponent difference
`aᵢ - bᵢ`, i.e. iff `x = x* · exp v` with `v ⊥ span{aᵢ - bᵢ}`. This gives the monomial
(rational) parametrization of the steady-state variety.

Main results:
* `CRNT.binomial_solution_iff_log_orthogonal`: the binomial system, solved in logarithms.
* `CRNT.Network.HasToricSteadyStates`.
* `CRNT.Network.toricSteadyState_iff_log_orthogonal`,
  `CRNT.Network.toricSteadyState_iff_exp_parametrization`.
-/

namespace CRNT

open scoped BigOperators

variable {S : Type} [Fintype S]

/-- The log of a mass-action monomial at a positive concentration. -/
theorem log_massActionMonomial {x : Concentration S} (hx : x.Positive) (y : Complex S) :
    Real.log (y.massActionMonomial x) = ∑ s, (y s : ℝ) * Real.log (x s) := by
  rw [Complex.massActionMonomial, Real.log_prod (fun s _ => (pow_pos (hx s) _).ne')]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.log_pow]

/-- The pairing `⟨a - b, v⟩` of an exponent difference with a log-concentration. -/
def expPairing (a b : Complex S) (v : S → ℝ) : ℝ := ∑ s, ((a s : ℝ) - (b s : ℝ)) * v s

/-- A binomial equation `x ^ a = c x ^ b` at a positive point, in logarithmic form. -/
theorem binomial_iff_log {x : Concentration S} (hx : x.Positive) (a b : Complex S) {c : ℝ}
    (hc : 0 < c) :
    a.massActionMonomial x = c * b.massActionMonomial x ↔
      expPairing a b (fun s => Real.log (x s)) = Real.log c := by
  have ha := Complex.massActionMonomial_pos hx a
  have hb := Complex.massActionMonomial_pos hx b
  constructor
  · intro h
    have := congrArg Real.log h
    rw [Real.log_mul hc.ne' hb.ne', log_massActionMonomial hx, log_massActionMonomial hx] at this
    unfold expPairing
    simp only [sub_mul, Finset.sum_sub_distrib]
    linarith
  · intro h
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr ha) (Set.mem_Ioi.mpr (mul_pos hc hb))
    rw [Real.log_mul hc.ne' hb.ne', log_massActionMonomial hx, log_massActionMonomial hx]
    unfold expPairing at h
    simp only [sub_mul, Finset.sum_sub_distrib] at h
    linarith

/-- **A binomial system is log-affine.** If `x*` is a positive solution of
`x ^ aᵢ = cᵢ x ^ bᵢ` (`i ∈ ι`), a positive `x` is a solution iff `log x - log x*` is
orthogonal to every `aᵢ - bᵢ`. -/
theorem binomial_solution_iff_log_orthogonal {ι : Type*} (a b : ι → Complex S) (c : ι → ℝ)
    (hc : ∀ i, 0 < c i) {xs x : Concentration S} (hxs : xs.Positive) (hx : x.Positive)
    (hsol : ∀ i, (a i).massActionMonomial xs = c i * (b i).massActionMonomial xs) :
    (∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x) ↔
      ∀ i, expPairing (a i) (b i) (fun s => Real.log (x s) - Real.log (xs s)) = 0 := by
  have hpair : ∀ i, expPairing (a i) (b i) (fun s => Real.log (x s) - Real.log (xs s)) =
      expPairing (a i) (b i) (fun s => Real.log (x s)) -
        expPairing (a i) (b i) (fun s => Real.log (xs s)) := by
    intro i
    unfold expPairing
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  constructor
  · intro h i
    rw [hpair, (binomial_iff_log hx _ _ (hc i)).mp (h i),
      (binomial_iff_log hxs _ _ (hc i)).mp (hsol i), sub_self]
  · intro h i
    rw [binomial_iff_log hx _ _ (hc i)]
    have := h i
    rw [hpair, (binomial_iff_log hxs _ _ (hc i)).mp (hsol i), sub_eq_zero] at this
    exact this

namespace Network

variable [DecidableEq S]

/-- A mass-action system **has toric steady states** if its positive steady states are the
positive solutions of finitely many binomial equations `x ^ aᵢ = cᵢ x ^ bᵢ`, `cᵢ > 0`. -/
def HasToricSteadyStates (N : Network S) (κ : RateConstants N) : Prop :=
  ∃ (n : ℕ) (a b : Fin n → Complex S) (c : Fin n → ℝ), (∀ i, 0 < c i) ∧
    ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x)

/-- **Toric steady states are log-affine** (Pérez Millán–Dickenstein–Shiu–Conradi 2012). If
the system has toric steady states with binomial exponents `(aᵢ, bᵢ)` and `x*` is a positive
steady state, then a positive `x` is a steady state iff `log x - log x* ⊥ aᵢ - bᵢ` for all
`i`. -/
theorem toricSteadyState_iff_log_orthogonal (N : Network S) (κ : RateConstants N)
    {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs x : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (hx : x.Positive) :
    N.IsMassActionSteadyState κ x ↔
      ∀ i, expPairing (a i) (b i) (fun s => Real.log (x s) - Real.log (xs s)) = 0 := by
  rw [htor x hx]
  exact binomial_solution_iff_log_orthogonal a b c hc hxs hx ((htor xs hxs).mp hxss)

/-- **Monomial parametrization of toric steady states.** Under the hypotheses of
`toricSteadyState_iff_log_orthogonal`, the positive steady states are exactly the points
`x* · exp v` with `v ⊥ aᵢ - bᵢ` for all `i`. -/
theorem toricSteadyState_iff_exp_parametrization (N : Network S) (κ : RateConstants N)
    {n : ℕ} (a b : Fin n → Complex S) (c : Fin n → ℝ) (hc : ∀ i, 0 < c i)
    (htor : ∀ x : Concentration S, x.Positive →
      (N.IsMassActionSteadyState κ x ↔
        ∀ i, (a i).massActionMonomial x = c i * (b i).massActionMonomial x))
    {xs : Concentration S} (hxs : xs.Positive) (hxss : N.IsMassActionSteadyState κ xs)
    (x : Concentration S) :
    (x.Positive ∧ N.IsMassActionSteadyState κ x) ↔
      ∃ v : S → ℝ, (∀ i, expPairing (a i) (b i) v = 0) ∧
        x = fun s => xs s * Real.exp (v s) := by
  constructor
  · rintro ⟨hx, hss⟩
    refine ⟨fun s => Real.log (x s) - Real.log (xs s),
      (toricSteadyState_iff_log_orthogonal N κ a b c hc htor hxs hxss hx).mp hss, ?_⟩
    funext s
    rw [Real.exp_sub, Real.exp_log (hx s), Real.exp_log (hxs s)]
    field_simp [(hxs s).ne']
  · rintro ⟨v, hv, rfl⟩
    have hx : Concentration.Positive (fun s => xs s * Real.exp (v s)) :=
      fun s => mul_pos (hxs s) (Real.exp_pos _)
    refine ⟨hx, (toricSteadyState_iff_log_orthogonal N κ a b c hc htor hxs hxss hx).mpr ?_⟩
    intro i
    have : (fun s => Real.log (xs s * Real.exp (v s)) - Real.log (xs s)) = v := by
      funext s
      rw [Real.log_mul (hxs s).ne' (Real.exp_pos _).ne', Real.log_exp]
      ring
    rw [this]
    exact hv i

/-- **Toric steady-state sets are closed under weighted geometric means.** If a system has
toric steady states, then for positive steady states `x, z` and any real `θ`, the point
`x ^ θ z ^ (1 - θ)` is again a positive steady state. -/
theorem HasToricSteadyStates.geomMean (N : Network S) (κ : RateConstants N)
    (htor : N.HasToricSteadyStates κ) {x z : Concentration S} (hx : x.Positive)
    (hz : z.Positive) (hxs : N.IsMassActionSteadyState κ x)
    (hzs : N.IsMassActionSteadyState κ z) (θ : ℝ) :
    N.IsMassActionSteadyState κ (fun s => x s ^ θ * z s ^ (1 - θ)) := by
  obtain ⟨n, a, b, c, hc, h⟩ := htor
  have hw : Concentration.Positive (fun s => x s ^ θ * z s ^ (1 - θ)) :=
    fun s => mul_pos (Real.rpow_pos_of_pos (hx s) _) (Real.rpow_pos_of_pos (hz s) _)
  rw [toricSteadyState_iff_log_orthogonal N κ a b c hc h hx hxs hw]
  have hzx := (toricSteadyState_iff_log_orthogonal N κ a b c hc h hx hxs hz).mp hzs
  intro i
  have : (fun s => Real.log (x s ^ θ * z s ^ (1 - θ)) - Real.log (x s)) =
      fun s => (1 - θ) * (Real.log (z s) - Real.log (x s)) := by
    funext s
    rw [Real.log_mul (Real.rpow_pos_of_pos (hx s) _).ne' (Real.rpow_pos_of_pos (hz s) _).ne',
      Real.log_rpow (hx s), Real.log_rpow (hz s)]
    ring
  rw [this]
  have hi := hzx i
  unfold expPairing at hi ⊢
  calc ∑ s, ((a i s : ℝ) - (b i s : ℝ)) * ((1 - θ) * (Real.log (z s) - Real.log (x s)))
      = (1 - θ) * ∑ s, ((a i s : ℝ) - (b i s : ℝ)) * (Real.log (z s) - Real.log (x s)) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
    _ = 0 := by rw [hi, mul_zero]

end Network

end CRNT
