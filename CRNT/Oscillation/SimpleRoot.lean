import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic

/-!
# Simple roots do not occur in both factors

One of the four contraction kernels the Floquet route needs, and the only one small enough to
close without the compiler in front of you. It is what rules out the transverse return derivative
inheriting the autonomous multiplier `1`: linear stability makes `1` a simple root of the Floquet
polynomial, and the factorization
`floquetPolynomial = (X - 1) * charpoly(derivative)` then forces
`1 ∉ charpoly(derivative).roots`.

Kept in its own module, depending on nothing but Mathlib's polynomial-roots API, so that it is
verifiable independently of `CRNT.Oscillation.ReturnMapContraction` (whose other contents are
still open obligations) and of `CRNT.Oscillation.MatrixCriteria` (which does not yet elaborate).
-/

namespace CRNT
namespace ReturnMapContraction

theorem simpleRoot_not_mem_both {p q : Polynomial ℂ} {a : ℂ}
    (hcount : (p * q).roots.count a = 1) : ¬ (a ∈ p.roots ∧ a ∈ q.roots) := by
  rintro ⟨hp, hq⟩
  have hpq : p * q ≠ 0 := by
    intro h
    rw [h, Polynomial.roots_zero, Multiset.count_zero] at hcount
    exact absurd hcount (by norm_num)
  have hp0 : p ≠ 0 := fun h => hpq (by rw [h, zero_mul])
  have hq0 : q ≠ 0 := fun h => hpq (by rw [h, mul_zero])
  have hadd : (p * q).roots.count a = p.roots.count a + q.roots.count a := by
    rw [Polynomial.roots_mul hpq, Multiset.count_add]
  have h1 : 1 ≤ p.roots.count a := Multiset.one_le_count_iff_mem.mpr hp
  have h2 : 1 ≤ q.roots.count a := Multiset.one_le_count_iff_mem.mpr hq
  omega

/-- Statement form, for consumers that take the kernel as a hypothesis. -/
def SimpleRootFactorTarget : Prop :=
  ∀ (p q : Polynomial ℂ) (a : ℂ),
    (p * q).roots.count a = 1 → ¬ (a ∈ p.roots ∧ a ∈ q.roots)

/-- The simple-root kernel is available unconditionally. -/
theorem simpleRootFactor_proved : SimpleRootFactorTarget :=
  fun _p _q _a h => simpleRoot_not_mem_both h

end ReturnMapContraction
end CRNT
