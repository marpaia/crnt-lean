import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Ring.Rat

/-!
# Clearing finitely many rational denominators

Reusable arithmetic infrastructure for turning a nonnegative rational vector on a
finite type into a natural-valued vector by one common positive scale factor.
-/

namespace CRNT
namespace Network

/-- One common natural denominator for a finite family of rationals. -/
def rationalCommonDenominator {A : Type} [Fintype A] (q : A → ℚ) : ℕ :=
  ∏ a : A, (q a).den

/-- Natural coordinates obtained by clearing a common denominator. -/
def clearRationalToNat {A : Type} [Fintype A] (q : A → ℚ) (a : A) : ℕ :=
  (rationalCommonDenominator q / (q a).den) * (q a).num.toNat

/-- Integer coordinates obtained by clearing a common denominator, allowing arbitrary signs. -/
def clearRationalToInt {A : Type} [Fintype A] (q : A → ℚ) (a : A) : ℤ :=
  ((rationalCommonDenominator q / (q a).den : ℕ) : ℤ) * (q a).num

/-- Every component denominator divides the chosen common denominator. -/
theorem denominator_dvd_common {A : Type} [DecidableEq A] [Fintype A]
    (q : A → ℚ) (a : A) : (q a).den ∣ rationalCommonDenominator q := by
  unfold rationalCommonDenominator
  exact Finset.dvd_prod_of_mem (fun z : A => (q z).den) (Finset.mem_univ a)

/-- Signed denominator clearing scales every rational component by the same positive integer. -/
theorem cast_clearRationalToInt {A : Type} [DecidableEq A] [Fintype A]
    (q : A → ℚ) (a : A) :
    ((clearRationalToInt q a : ℤ) : ℚ) = (rationalCommonDenominator q : ℚ) * q a := by
  let D := rationalCommonDenominator q
  let k := D / (q a).den
  have hdiv : (q a).den ∣ D := denominator_dvd_common q a
  have hD : (q a).den * k = D := by
    dsimp [k]
    exact Nat.mul_div_cancel' hdiv
  unfold clearRationalToInt
  change (((k : ℤ) * (q a).num : ℤ) : ℚ) = (D : ℚ) * q a
  rw [Int.cast_mul]
  rw [← Rat.den_mul_eq_num (q a)]
  push_cast
  rw [← mul_assoc]
  congr 1
  rw [mul_comm]
  exact_mod_cast hD

/-- Clearing denominators scales every nonnegative component by the same positive integer. -/
theorem cast_clearRationalToNat {A : Type} [DecidableEq A] [Fintype A]
    (q : A → ℚ) (hq : ∀ a, 0 ≤ q a) (a : A) :
    ((clearRationalToNat q a : ℕ) : ℚ) = (rationalCommonDenominator q : ℚ) * q a := by
  let D := rationalCommonDenominator q
  let k := D / (q a).den
  have hdiv : (q a).den ∣ D := denominator_dvd_common q a
  have hD : (q a).den * k = D := by
    dsimp [k]
    exact Nat.mul_div_cancel' hdiv
  have hnum_nonneg : 0 ≤ (q a).num := Rat.num_nonneg.mpr (hq a)
  have hnum_nat : (((q a).num.toNat : ℕ) : ℤ) = (q a).num :=
    Int.toNat_of_nonneg hnum_nonneg
  have hnum_rat : (((q a).num.toNat : ℕ) : ℚ) = ((q a).num : ℚ) := by
    exact_mod_cast hnum_nat
  unfold clearRationalToNat
  change (((k * (q a).num.toNat : ℕ) : ℚ)) = (D : ℚ) * q a
  rw [Nat.cast_mul, hnum_rat]
  rw [← Rat.den_mul_eq_num (q a)]
  rw [← mul_assoc]
  congr 1
  rw [mul_comm]
  exact_mod_cast hD

/-- The common denominator is strictly positive. -/
theorem rationalCommonDenominator_pos {A : Type} [Fintype A] (q : A → ℚ) :
    0 < rationalCommonDenominator q := by
  classical
  unfold rationalCommonDenominator
  induction (Finset.univ : Finset A) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha]
      exact Nat.mul_pos (Rat.pos (q a)) ih

end Network
end CRNT
