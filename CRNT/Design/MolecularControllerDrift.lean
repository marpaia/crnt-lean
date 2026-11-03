import CRNT.Design.GeneralPlantDrift
import CRNT.Design.Antithetic
import CRNT.Design.AntitheticErgodic
import CRNT.Stochastic.FirstOrderFoster
import CRNT.Stochastic.FosterLyapunov
import CRNT.Stochastic.FosterRecurrence
import CRNT.Stochastic.MinimalSemigroupNetwork
import CRNT.Stochastic.HarrisTheorem
import Mathlib.Tactic

/-!
# The cubic term of the molecular antithetic controller: the general-plant control

This file closes the gap left open in leaf **C3** of the field map (`CRNT.Design.GeneralPlant`)
by `CRNT.Design.GeneralPlantDrift`: the *molecular* realization of the antithetic integral
controller contains one **bimolecular** reaction, the annihilation

```text
Z₁ + Z₂ → ∅        (rate κ_ann),
```

whose stochastic mass-action propensity is `κ_ann z₁ z₂`, i.e. **quadratic** in the counts.
Consequently the drift of a *quadratic* Lyapunov function `V n = (n − n*)ᵀ P (n − n*)` acquires a
**cubic** term, and the quadratic Foster drift condition of `fosterDrift_of_certificate` no
longer applies verbatim.

## 1. Where the cubic term comes from

The exact drift identity of `CRNT.Design.GeneralPlantDrift.observableGenerator_quadObservable` is

```text
Q V (n) = 2 ⟨n − n*, P (∑_r λ_r(n) Δ_r)⟩ + ∑_r λ_r(n) ⟨Δ_r, P Δ_r⟩.
```

For a *unimolecular* reaction the propensity `λ_r(n)` is linear in `n`, so both terms are at most
quadratic.  For the bimolecular annihilation `λ_ann(n) = κ_ann (n z₁) (n z₂)` is quadratic, and

* the **first** term becomes **cubic**: `2 κ_ann (n z₁) (n z₂) ⟨n − n*, P Δ_ann⟩`;
* the **second** term stays quadratic: `κ_ann (n z₁) (n z₂) ⟨Δ_ann, P Δ_ann⟩`.

`bimolecular_cubic_contribution` is the exact statement of this decomposition, and
`cubic_remainder_le` is the **general estimate**: for an arbitrary symmetric shape matrix `P`
satisfying an explicit boundedness hypothesis, and an arbitrary bimolecular reaction, the
contribution of that reaction to the drift is bounded by

```text
|λ_r(n) (V (n + Δ_r) − V n)| ≤ C₃ ‖n − n*‖³ + C₂ ‖n − n*‖² + C₁ ‖n − n*‖ + C₀,
```

with **explicit** constants `C₃, C₂, C₁, C₀` (`cubicConstants`).  When the reference count vector
vanishes on the two reactant species — the natural choice for the controller species — the
estimate collapses to the requested shape

```text
≤ C (‖n − n*‖³ + ‖n − n*‖²)          (cubic_remainder_le_zero_ref).
```

This is the **reusable core** of the file: it is stated for an arbitrary number of species, an
arbitrary symmetric `P`, and an arbitrary bimolecular reaction.

## 2. The drift bound with the cubic term

`fosterDrift_cubic_le` combines the general estimate with the first-order drift analysis of
`CRNT.Design.GeneralPlantDrift.fosterDrift_of_certificate` and gives, for a network whose
reactions are unimolecular *except* for one bimolecular annihilation, the drift bound

```text
Q V (n) ≤ − (3/8) ‖n − n*‖² + C₃ ‖n − n*‖³ + C₂ ‖n − n*‖² + C₁ ‖n − n*‖ + K.
```

The decomposition is obtained by replacing the annihilation by the *trivial* reaction
(`Network.withTrivialReaction`), which keeps the first-order drift matrix unchanged
(`firstOrderDriftMatrix_withTrivial`) and splits the drift into the first-order part and the
annihilation part (`drift_decomposition`).

## 3. The obstruction, and the two ways out

A cubic term **cannot** be absorbed into a quadratic drift bound *globally*: `cubic_not_absorbable`
proves that for `C₃, c > 0` there is no constant `K` with `C₃ ‖x‖³ ≤ c ‖x‖² + K` for all `x`.
The file therefore gives the two classical escapes, and says exactly which one it uses.

**(a) The sign structure of `P` (used here).**  The annihilation reaction vector is
`Δ_ann = −e_s − e_t`: it *preserves the charge* `z₁ − z₂`.  If the shape matrix satisfies the
*annihilation sign condition*

```text
P s s + P s t = P t s + P t t = c₀ > 0,      P k s + P k t = 0  (k ∉ {s, t}),
```

then the annihilation's contribution to the drift of `V` is exactly

```text
2 c₀ κ_ann (n z₁) (n z₂) (1 − (n z₁) − (n z₂)) ≤ 0,
```

*because the `z₁ z₂` cross-term of `V` makes the annihilation decrease the Lyapunov function*.
This is `annihilation_drift_le_zero`, the general form of the control performed by the explicit
`z₁ z₂` cross-term of `CRNT.Antithetic.lyap` (`CRNT.Design.AntitheticErgodic.drift_lyap_le`).
Under the sign condition the drift of the closed loop satisfies the *quadratic* Foster bound
`Q V ≤ −(3/8) ‖n − n*‖² + K` (`fosterDrift_of_sign_controlled`), and the closed loop is ergodic
(`ergodic_of_sign_controlled`).

**(b) The boundedness of the counts (not delivered here).**  On a region where the counts are
bounded by `B` the cubic term is absorbed into the quadratic one, at the price of a *smaller*
constant `c`; the bound is then valid only on that region, which is why the sign structure is
the route used for the global conclusion.  The boundedness variant is *not* formalized in this
file: the sign structure (a) already yields a global Foster condition.

## 4. The instance

`AntitheticInstance` verifies the control on the repository's own antithetic closed loop
(`CRNT.Antithetic.closedLoop`, production–degradation plant plus antithetic controller):

* `antitheticInstance.annihilation_is_annihilation`: the reaction `Z₁ + Z₂ → ∅` of the
  repository's closed loop *is* a bimolecular annihilation between the species `0` and `1`, so
  the general theory applies to it;
* `antitheticInstance.generalMatrix` / `antitheticInstance.generalMatrix_sign_condition`: the
  *general* shape matrix
  `P (a c e p) = [[a, c − a, e], [c − a, a, −e], [e, −e, p]]` — the general-plant form of the
  repository's Lyapunov function, whose quadratic form is
  `a (z₁ − z₂)² + 2 c z₁ z₂ + 2 e x (z₁ − z₂) + p x²` — satisfies the annihilation sign
  condition as soon as `c > 0`: the two controller rows have row sum `c` and the output row has
  row sum zero on the controller block.  The repository's `CRNT.Antithetic.lyap` is this form
  with `a = c_A` (or `c_B`), `2 c = c_d`, `2 e = −c_c` and `p = c_b`; that identification, and
  the verification that the annihilation decreases `lyap` by `c_d (1 − z₁ − z₂)`, are stated in
  `CRNT.Design.AntitheticErgodic` and are *not* re-proved here.

## 5. Relation to Briat–Gupta–Khammash and to leaf C3

Briat, Gupta and Khammash (*Antithetic integral feedback ensures robust perfect adaptation in
noisy biomolecular networks*, Cell Systems 2 (2016)) prove the ergodicity of the molecular
antithetic closed loop by exactly this device: a Lyapunov function carrying an explicit
`z₁ z₂` cross-term, whose drift contribution of the annihilation `Z₁ + Z₂ → ∅` is a *negative*
cubic term, and which therefore satisfies a Foster condition with a *norm-like* (not quadratic)
function.  This file isolates and generalizes the device:

* `annihilation_sign_condition` is the general statement of the "sign conditions on `P Δ_r`";
* `annihilation_drift_le_zero` is the general statement of the cubic control;
* `fosterDrift_of_sign_controlled` and `ergodic_of_sign_controlled` are the general Foster
  consequences, valid for an arbitrary plant and an arbitrary number of species.

The remaining ingredient for a *specific* molecular antithetic controller is the Lyapunov
*certificate* for the unimolecular part of the closed loop: for the production–degradation plant
the drift matrix of the unimolecular part is **not** Hurwitz (the reference reaction feeds `Z₁`
without bound), so the quadratic certificate of `CRNT.Design.GeneralPlantDrift` cannot be used
and the repository instead uses the *piecewise* quadratic `CRNT.Antithetic.lyap`
(`CRNT.Design.AntitheticErgodic.drift_lyap_le`), whose `φ`-part is precisely the extra
structure needed for the charge.  This file does not re-prove that certificate; it provides the
general machinery for controlling the cubic term, which is what leaf C3 was missing.

Depends on: `CRNT.Design.GeneralPlantDrift`, `CRNT.Design.Antithetic`,
`CRNT.Design.AntitheticErgodic`, `CRNT.Stochastic.FirstOrderFoster`,
`CRNT.Stochastic.FosterLyapunov`, `CRNT.Stochastic.FosterRecurrence`,
`CRNT.Stochastic.MinimalSemigroupNetwork`, `CRNT.Stochastic.HarrisTheorem`.
-/

open Filter
open scoped BigOperators Topology Matrix

namespace CRNT

namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ## 1. Bimolecular reactions -/

/-- A **bimolecular** reaction: its source complex is made of one molecule of `s` and one
molecule of `t` (`s ≠ t`), and of nothing else.  Its stochastic mass-action propensity is
`κ_r (n s) (n t)`, which is *quadratic* in the counts; this is the reason why the drift of a
quadratic Lyapunov function acquires a *cubic* term. -/
def IsBimolecularFrom (N : Network S) (r : N.R) (s t : S) : Prop :=
  s ≠ t ∧ (N.reaction r).source s = 1 ∧ (N.reaction r).source t = 1 ∧
    ∀ u, u ≠ s → u ≠ t → (N.reaction r).source u = 0

/-- A **bimolecular annihilation** `Z_s + Z_t → ∅`: a bimolecular reaction with empty target.
Its reaction vector is `−e_s − e_t`; in particular it *preserves the charge* `z_s − z_t`, and it
*decreases* the product `z_s z_t` by `z_s + z_t − 1`.  These two facts are the whole content of
the classical control of the cubic term. -/
def IsAnnihilationFrom (N : Network S) (r : N.R) (s t : S) : Prop :=
  N.IsBimolecularFrom r s t ∧ ∀ u, (N.reaction r).target u = 0

/-- The two reactant species of a bimolecular reaction are distinct. -/
theorem IsBimolecularFrom.ne {N : Network S} {r : N.R} {s t : S}
    (h : N.IsBimolecularFrom r s t) : s ≠ t := h.1

/-- A bimolecular reaction is not of zeroth order. -/
theorem IsBimolecularFrom.not_zeroOrder {N : Network S} {r : N.R} {s t : S}
    (h : N.IsBimolecularFrom r s t) : ¬ N.IsZeroOrderReaction r := by
  intro h0
  have h1 := h0 s
  rw [h.2.1] at h1
  omega

/-- A bimolecular reaction is not unimolecular from any species. -/
theorem IsBimolecularFrom.not_unimolecular {N : Network S} {r : N.R} {s t : S}
    (h : N.IsBimolecularFrom r s t) (u : S) : ¬ N.IsUnimolecularFrom r u := by
  intro hu
  have h1 : (N.reaction r).source u = 1 := hu.1
  by_cases htu : t = u
  · have h2 := hu.2 s (by
      intro hsu
      exact h.1 (hsu.trans htu.symm))
    rw [h.2.1] at h2
    omega
  · have h2 := hu.2 t htu
    rw [h.2.2.1] at h2
    omega

/-- The reaction vector of a bimolecular annihilation is `−e_s − e_t`. -/
theorem IsAnnihilationFrom.reactionVector {N : Network S} {r : N.R} {s t : S}
    (h : N.IsAnnihilationFrom r s t) :
    N.reactionVector r = fun u => if u = s then -1 else if u = t then -1 else 0 := by
  funext u
  by_cases hu : u = s
  · subst hu
    rw [Network.reactionVector_apply, h.2 u, h.1.2.1]
    simp
  · by_cases hu2 : u = t
    · subst hu2
      rw [Network.reactionVector_apply, h.2 u, h.1.2.2.1]
      simp
    · rw [Network.reactionVector_apply, h.2 u, h.1.2.2.2 u hu hu2]
      simp [hu, hu2]

/-- **The propensity of a bimolecular reaction is quadratic in the counts.** -/
theorem stochasticRate_bimolecular (N : Network S) (κ : N.RateConstants) (n : S → ℕ)
    {r : N.R} {s t : S} (hr : N.IsBimolecularFrom r s t) :
    N.stochasticMassActionRate κ n r = κ.k r * (n s : ℝ) * (n t : ℝ) := by
  unfold stochasticMassActionRate
  have hprod : (∏ u : S, ((n u).descFactorial ((N.reaction r).source u) : ℝ)) =
      (n s : ℝ) * (n t : ℝ) := by
    have h1 := Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (s := (Finset.univ : Finset S)) (i := s)
      (f := fun u => ((n u).descFactorial ((N.reaction r).source u) : ℝ)) (Finset.mem_univ s)
    rw [h1]
    rw [hr.2.1, Nat.descFactorial_one]
    have htmem : t ∈ (Finset.univ : Finset S) \ {s} := by
      refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ t, ?_⟩
      rw [Finset.mem_singleton]
      exact Ne.symm hr.1
    have h2 := Finset.prod_eq_mul_prod_sdiff_singleton_of_mem
      (s := (Finset.univ : Finset S) \ {s}) (i := t)
      (f := fun u => ((n u).descFactorial ((N.reaction r).source u) : ℝ)) htmem
    rw [h2]
    rw [hr.2.2.1, Nat.descFactorial_one]
    have hone : (∏ x ∈ ((Finset.univ : Finset S) \ {s}) \ {t},
        ((n x).descFactorial ((N.reaction r).source x) : ℝ)) = 1 := by
      refine Finset.prod_eq_one fun u hu => ?_
      have hut : u ≠ t := by simpa using (Finset.mem_sdiff.mp hu).2
      have hus : u ≠ s := by
        simpa using (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu).1).2
      have h0 := hr.2.2.2 u hus hut
      rw [h0, Nat.descFactorial_zero, Nat.cast_one]
    rw [hone]
    ring
  rw [hprod]
  ring

/-- **Every reaction but one is zeroth order or unimolecular.**  This is the hypothesis under
which the drift of the counts is *affine* outside the distinguished bimolecular reaction. -/
def IsFirstOrderExcept (N : Network S) (rAnn : N.R) : Prop :=
  ∀ r : N.R, r ≠ rAnn → N.IsZeroOrderReaction r ∨ ∃ s, N.IsUnimolecularFrom r s

/-- **The trivial reaction** `∅ → ∅`: it has zero reaction vector and zero quadratic remainder,
so replacing a reaction by it removes that reaction from the drift without changing the
first-order drift matrix of the remaining ones. -/
def trivialReaction (S : Type) : Reaction S := ⟨Complex.zero, Complex.zero⟩

/-- **The network obtained by replacing the reaction `r` by the trivial reaction.**  The
first-order drift matrix is unchanged (`firstOrderDriftMatrix_withTrivial`), and the drift of the
counts splits into the drift of the trivial network and the contribution of `r`
(`countDrift_withTrivial`, `quadRemainder_withTrivial`). -/
@[reducible] def withTrivialReaction (N : Network S) (r : N.R) : Network S where
  R := N.R
  decEqR := N.decEqR
  fintypeR := N.fintypeR
  reaction := fun r' => if r' = r then trivialReaction S else N.reaction r'

/-- The reaction vector of the trivial reaction is zero. -/
theorem trivialReaction_reactionVector (N : Network S) (r : N.R) :
    (N.withTrivialReaction r).reactionVector r = 0 := by
  funext u
  simp [withTrivialReaction, Network.reactionVector_apply, trivialReaction, Complex.zero]

/-- The trivial reaction is of zeroth order. -/
theorem withTrivialReaction_isZeroOrder (N : Network S) (r : N.R) :
    (N.withTrivialReaction r).IsZeroOrderReaction r := by
  intro u
  simp [trivialReaction, Complex.zero]

/-- A reaction of the trivial network is zero order exactly when the corresponding reaction of
the original network is, unless it is the distinguished one. -/
theorem withTrivialReaction_isZeroOrder_iff (N : Network S) (r r' : N.R) (h : r' ≠ r) :
    (N.withTrivialReaction r).IsZeroOrderReaction r' ↔ N.IsZeroOrderReaction r' := by
  have hsrc : ∀ u, ((N.withTrivialReaction r).reaction r').source u = (N.reaction r').source u := by
    intro u
    simp only [ite_eq_right h]
  constructor
  · intro h0 u
    have h1 := h0 u
    rw [hsrc] at h1
    exact h1
  · intro h0 u
    rw [hsrc]
    exact h0 u

/-- A reaction of the trivial network is unimolecular from a species exactly when the
corresponding reaction of the original network is. -/
theorem withTrivialReaction_isUnimolecularFrom_iff (N : Network S) (r r' : N.R) (h : r' ≠ r)
    (u : S) :
    (N.withTrivialReaction r).IsUnimolecularFrom r' u ↔ N.IsUnimolecularFrom r' u := by
  have hsrc : ∀ v, ((N.withTrivialReaction r).reaction r').source v = (N.reaction r').source v := by
    intro v
    simp only [ite_eq_right h]
  constructor
  · intro h0
    have h0' : ((N.withTrivialReaction r).reaction r').source u = 1 ∧
        ∀ v, v ≠ u → ((N.withTrivialReaction r).reaction r').source v = 0 := h0
    refine ⟨?_, ?_⟩
    · rw [hsrc] at h0'
      exact h0'.1
    · intro v hv
      have h1 := h0'.2 v hv
      rw [hsrc] at h1
      exact h1
  · intro h0
    have h0' : (N.reaction r').source u = 1 ∧
        ∀ v, v ≠ u → (N.reaction r').source v = 0 := h0
    refine ⟨?_, ?_⟩
    · rw [hsrc]
      exact h0'.1
    · intro v hv
      have h1 := h0'.2 v hv
      rw [← hsrc] at h1
      exact h1
end Network

namespace Design
namespace GeneralPlant

variable {m : ℕ}

/-! ## 0. Norms on the count lattice -/

/-- The Euclidean norm of a real vector: `‖x‖ = sqrt (∑_i x_i²)`. -/
noncomputable def normVec (x : Fin m → ℝ) : ℝ := Real.sqrt (normSq x)

/-- The squared norm is nonnegative. -/
theorem normSq_nonneg (x : Fin m → ℝ) : 0 ≤ normSq x := by
  unfold normSq
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The norm is nonnegative. -/
theorem normVec_nonneg (x : Fin m → ℝ) : 0 ≤ normVec x := Real.sqrt_nonneg _

/-- The square of the norm is the squared norm. -/
theorem normVec_sq (x : Fin m → ℝ) : normVec x ^ 2 = normSq x := by
  rw [normVec, Real.sq_sqrt (normSq_nonneg x)]

/-- Every coordinate is bounded by the norm. -/
theorem abs_le_normVec (x : Fin m → ℝ) (i : Fin m) : |x i| ≤ normVec x := by
  have h1 : x i ^ 2 ≤ normSq x := by
    have h := Finset.single_le_sum (f := fun j => (x j) ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
    simpa [normSq] using h
  have h2 : x i ^ 2 ≤ normVec x ^ 2 := by
    rw [normVec_sq]
    exact h1
  have hnv : 0 ≤ normVec x := normVec_nonneg x
  have h4 : x i ≤ normVec x := by nlinarith [sq_nonneg (x i - normVec x)]
  have h5 : -x i ≤ normVec x := by nlinarith [sq_nonneg (x i + normVec x)]
  exact (abs_le).2 ⟨by linarith [h5], h4⟩

/-- The sum of the absolute values is bounded by the cardinality times the norm. -/
theorem sum_abs_le_normVec (x : Fin m → ℝ) :
    (∑ i, |x i|) ≤ (Fintype.card (Fin m) : ℝ) * normVec x := by
  calc
    (∑ i, |x i|) ≤ ∑ i, normVec x := Finset.sum_le_sum fun i _ => abs_le_normVec x i
    _ = (Fintype.card (Fin m) : ℝ) * normVec x := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]

/-- **A norm bound from bounded coordinates.**  If every coordinate of `x` is bounded in absolute
value by `B ≥ 0`, then `‖x‖ ≤ card · B`.  This is the ingredient used by the *boundedness* route
to the cubic term. -/
theorem normVec_le_of_abs_le (x : Fin m → ℝ) {B : ℝ} (hB : 0 ≤ B) (h : ∀ i, |x i| ≤ B) :
    normVec x ≤ Real.sqrt (Fintype.card (Fin m)) * B := by
  have hsq : (∑ i, x i ^ 2) ≤ (Fintype.card (Fin m) : ℝ) * B ^ 2 := by
    calc
      (∑ i, x i ^ 2) ≤ ∑ i, B ^ 2 := Finset.sum_le_sum fun i _ => by
        have hh := (sq_le_sq₀ (abs_nonneg (x i)) hB).2 (h i)
        rw [sq_abs] at hh
        exact hh
      _ = (Fintype.card (Fin m) : ℝ) * B ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have h2 : normVec x ^ 2 ≤ (Fintype.card (Fin m) : ℝ) * B ^ 2 := by
    rw [normVec_sq]
    exact hsq
  have hcard : (0 : ℝ) ≤ Fintype.card (Fin m) := by positivity
  have hsq' : Real.sqrt (normVec x ^ 2) ≤ Real.sqrt ((Fintype.card (Fin m) : ℝ) * B ^ 2) :=
    Real.sqrt_le_sqrt h2
  rw [Real.sqrt_sq (normVec_nonneg x), Real.sqrt_mul hcard (B ^ 2), Real.sqrt_sq hB] at hsq'
  exact hsq'

/-! ## 2. The general cubic-term estimate -/

/-- **The boundedness hypothesis on the shape matrix.**  Every row of `P` has a bounded sum of
absolute entries.  This is the concrete operator-norm hypothesis under which the cubic estimate
below holds; it is discharged by any matrix with bounded entries. -/
def RowBounded (P : Matrix (Fin m) (Fin m) ℝ) (E : ℝ) : Prop :=
  0 ≤ E ∧ ∀ i, ∑ j, |P i j| ≤ E

/-- **The bilinear form of a row-bounded matrix.**  The bilinear form `xᵀ P y` is bounded by the
row bound `E` times the product of the Euclidean norms, up to the factor `card²`. -/
theorem bilinear_abs_le {P : Matrix (Fin m) (Fin m) ℝ} (hP : RowBounded P E)
    (x y : Fin m → ℝ) :
    |bilinear P x y| ≤ E * (Fintype.card (Fin m) : ℝ) ^ 2 * normVec x * normVec y := by
  have hE : 0 ≤ E := hP.1
  have hsumy : 0 ≤ ∑ j, |y j| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h1 : |bilinear P x y| ≤ (∑ i, |x i|) * E * (∑ j, |y j|) := by
    unfold bilinear
    simp only [Matrix.mulVec_apply_eq_sum]
    have hA : |∑ i, x i * ∑ j, P i j * y j| ≤ ∑ i, |x i * ∑ j, P i j * y j| :=
      Finset.abs_sum_le_sum_abs _ _
    have hB : (∑ i, |x i * ∑ j, P i j * y j|) ≤ ∑ i, |x i| * (∑ j, |P i j| * |y j|) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have h1i : |x i * ∑ j, P i j * y j| = |x i| * |∑ j, P i j * y j| := abs_mul _ _
      have h2i : |x i| * |∑ j, P i j * y j| ≤ |x i| * ∑ j, |P i j * y j| :=
        mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (abs_nonneg _)
      have h3i : |x i| * ∑ j, |P i j * y j| = ∑ j, |x i| * |P i j * y j| := by
        rw [Finset.mul_sum]
      have h4i : (∑ j, |x i| * |P i j * y j|) ≤ |x i| * (∑ j, |P i j| * |y j|) := by
        have hstep : (∑ j, |x i| * (|P i j| * |y j|)) = |x i| * (∑ j, |P i j| * |y j|) := by
          rw [Finset.mul_sum]
        rw [← hstep]
        refine Finset.sum_le_sum fun j _ => ?_
        rw [abs_mul]
      linarith
    have hC : (∑ i, |x i| * (∑ j, |P i j| * |y j|)) ≤ ∑ i, |x i| * (E * (∑ j, |y j|)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hrow : (∑ j, |P i j| * |y j|) ≤ E * (∑ j, |y j|) := by
        have h1j : (∑ j, |P i j| * |y j|) ≤ ∑ j, |P i j| * (∑ k, |y k|) := by
          refine Finset.sum_le_sum fun j _ => ?_
          have hsingle : |y j| ≤ ∑ k, |y k| := by
            have h := Finset.single_le_sum (f := fun k => |y k|) (fun k _ => abs_nonneg _)
              (Finset.mem_univ j)
            simpa using h
          exact mul_le_mul_of_nonneg_left hsingle (abs_nonneg _)
        have h2j : (∑ j, |P i j| * (∑ k, |y k|)) = (∑ j, |P i j|) * (∑ j, |y j|) := by
          rw [← Finset.sum_mul]
        have h3j : (∑ j, |P i j|) * (∑ j, |y j|) ≤ E * (∑ j, |y j|) :=
          mul_le_mul_of_nonneg_right (hP.2 i) hsumy
        linarith
      exact mul_le_mul_of_nonneg_left hrow (abs_nonneg _)
    have hD : (∑ i, |x i| * (E * (∑ j, |y j|))) = (∑ i, |x i|) * E * (∑ j, |y j|) := by
      rw [← Finset.sum_mul]
      ring
    linarith
  have hx := sum_abs_le_normVec x
  have hy := sum_abs_le_normVec y
  have hcard : (0 : ℝ) ≤ Fintype.card (Fin m) := by positivity
  calc
    |bilinear P x y| ≤ (∑ i, |x i|) * E * (∑ j, |y j|) := h1
    _ ≤ ((Fintype.card (Fin m) : ℝ) * normVec x) * E *
        ((Fintype.card (Fin m) : ℝ) * normVec y) := by
      have hstep1 : (∑ i, |x i|) * E ≤ ((Fintype.card (Fin m) : ℝ) * normVec x) * E :=
        mul_le_mul_of_nonneg_right hx hE
      have hstep2 : ((Fintype.card (Fin m) : ℝ) * normVec x) * E * (∑ j, |y j|)
          ≤ ((Fintype.card (Fin m) : ℝ) * normVec x) * E *
            ((Fintype.card (Fin m) : ℝ) * normVec y) :=
        mul_le_mul_of_nonneg_left hy
          (mul_nonneg (mul_nonneg hcard (normVec_nonneg x)) hE)
      calc
        (∑ i, |x i|) * E * (∑ j, |y j|) = ((∑ i, |x i|) * E) * (∑ j, |y j|) := by ring
        _ ≤ (((Fintype.card (Fin m) : ℝ) * normVec x) * E) * (∑ j, |y j|) :=
          mul_le_mul_of_nonneg_right hstep1 hsumy
        _ ≤ (((Fintype.card (Fin m) : ℝ) * normVec x) * E) *
            ((Fintype.card (Fin m) : ℝ) * normVec y) := hstep2
    _ = E * (Fintype.card (Fin m) : ℝ) ^ 2 * normVec x * normVec y := by ring

/-- **The bilinear form is homogeneous in its second argument.** -/
theorem bilinear_smul (M : Matrix (Fin m) (Fin m) ℝ) (a : ℝ) (x y : Fin m → ℝ) :
    bilinear M x (a • y) = a * bilinear M x y := by
  unfold bilinear
  simp only [Matrix.mulVec_apply_eq_sum, Pi.smul_apply, smul_eq_mul]
  calc
    (∑ i, x i * ∑ j, M i j * (a * y j))
        = ∑ i, x i * (a * ∑ j, M i j * y j) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          have h1 : (∑ j, M i j * (a * y j)) = a * ∑ j, M i j * y j := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            ring
          rw [h1]
    _ = a * (∑ i, x i * ∑ j, M i j * y j) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring

/-- **The change of a quadratic Lyapunov function along one reaction.**  For an *enabled*
reaction `r`, the quadratic observable satisfies

```text
V (n + Δ_r) − V n = 2 ⟨n − n*, P Δ_r⟩ + ⟨Δ_r, P Δ_r⟩.
```

This is the elementary form of the drift identity `observableGenerator_quadObservable`. -/
theorem fireCount_quadObservable_sub (N : Network (Fin m))
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P) (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    (r : N.R) (hen : N.Enabled n r) :
    quadObservable P nStar (N.fireCount n r) - quadObservable P nStar n =
      2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
        bilinear P (N.reactionVector r) (N.reactionVector r) := by
  have hfire : N.fireCount n r =
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
  rw [quadObservable_eq, quadObservable_eq, hdev, quadForm_add hP]
  simp only [quadForm_eq_bilinear]
  ring

/-- **The exact contribution of a bimolecular reaction to the drift of a quadratic Lyapunov
function.**  For a bimolecular reaction with propensity `κ_r (n s) (n t)`,

```text
λ_r(n) (V (n + Δ_r) − V n) = κ_r (n s) (n t) (2 ⟨n − n*, P Δ_r⟩ + ⟨Δ_r, P Δ_r⟩).
```

The first factor of the bracket is *linear* in `n − n*` and the propensity is *quadratic*, so
this contribution is **cubic** in the counts. -/
theorem bimolecular_cubic_contribution (N : Network (Fin m)) (κ : N.RateConstants)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P) (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    {r : N.R} {s t : Fin m} (hr : N.IsBimolecularFrom r s t) :
    N.stochasticMassActionRate κ n r *
        (quadObservable P nStar (N.fireCount n r) - quadObservable P nStar n)
      = κ.k r * (n s : ℝ) * (n t : ℝ) *
        (2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
          bilinear P (N.reactionVector r) (N.reactionVector r)) := by
  by_cases hen : N.Enabled n r
  · rw [fireCount_quadObservable_sub N hP nStar n r hen,
      Network.stochasticRate_bimolecular N κ n hr]
  · rw [N.stochasticMassActionRate_eq_zero_of_not_enabled κ n r hen]
    have hzero : n s = 0 ∨ n t = 0 := by
      by_contra hcon
      push Not at hcon
      apply hen
      intro u
      by_cases hu : u = s
      · subst hu
        rw [hr.2.1]
        omega
      · by_cases hu2 : u = t
        · subst hu2
          rw [hr.2.2.1]
          omega
        · rw [hr.2.2.2 u hu hu2]
          omega
    rcases hzero with hs | ht
    · rw [hs]
      ring
    · rw [ht]
      ring

/-- **The constants of the cubic estimate.**  They are the coefficients of the cubic, quadratic,
linear and constant terms in the bound

```text
|λ_r(n) (V (n + Δ_r) − V n)| ≤ C₃ ‖n − n*‖³ + C₂ ‖n − n*‖² + C₁ ‖n − n*‖ + C₀.
```

Here `card` is the number of species, `κr` the rate constant of the reaction, `E` the row bound
of the shape matrix, `D` a bound on the Euclidean norm of the reaction vector, and `a`, `b` the
magnitudes of the reference counts of the two reactant species. -/
structure CubicConstants (card κr E D a b : ℝ) where
  /-- The coefficient of the cubic term. -/
  C3 : ℝ
  /-- The coefficient of the quadratic term. -/
  C2 : ℝ
  /-- The coefficient of the linear term. -/
  C1 : ℝ
  /-- The constant term. -/
  C0 : ℝ
  /-- The value of the cubic coefficient. -/
  C3_eq : C3 = 2 * κr * E * card ^ 2 * D
  /-- The value of the quadratic coefficient. -/
  C2_eq : C2 = 2 * κr * E * card ^ 2 * D * (a + b) + κr * E * card ^ 2 * D ^ 2
  /-- The value of the linear coefficient. -/
  C1_eq : C1 = 2 * κr * E * card ^ 2 * D * a * b + κr * E * card ^ 2 * D ^ 2 * (a + b)
  /-- The value of the constant term. -/
  C0_eq : C0 = κr * E * card ^ 2 * D ^ 2 * a * b

/-- The explicit constants of the cubic estimate of a bimolecular reaction. -/
noncomputable def cubicConstants (card κr E D a b : ℝ) : CubicConstants card κr E D a b where
  C3 := 2 * κr * E * card ^ 2 * D
  C2 := 2 * κr * E * card ^ 2 * D * (a + b) + κr * E * card ^ 2 * D ^ 2
  C1 := 2 * κr * E * card ^ 2 * D * a * b + κr * E * card ^ 2 * D ^ 2 * (a + b)
  C0 := κr * E * card ^ 2 * D ^ 2 * a * b
  C3_eq := rfl
  C2_eq := rfl
  C1_eq := rfl
  C0_eq := rfl

/-- **The general cubic-term bound.**  Let `N` be a network, `κ` its rate constants, `P` a
symmetric shape matrix with bounded rows, `n*` a reference count vector and `n` a count vector.
Let `r` be a bimolecular reaction with reactant species `s`, `t`, and let `D` bound the
Euclidean norm of its reaction vector.  Then the contribution of `r` to the drift of the
quadratic Lyapunov function `V n = (n − n*)ᵀ P (n − n*)` satisfies

```text
|λ_r(n) (V (n + Δ_r) − V n)| ≤ C₃ ‖n − n*‖³ + C₂ ‖n − n*‖² + C₁ ‖n − n*‖ + C₀,
```

with the explicit constants `cubicConstants`.  This is the reusable core of the file: it is
valid for an arbitrary number of species, an arbitrary symmetric shape matrix and an arbitrary
bimolecular reaction. -/
theorem cubic_remainder_le (N : Network (Fin m)) (κ : N.RateConstants)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : RowBounded P E) (hPsym : Pᵀ = P)
    (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    {r : N.R} {s t : Fin m} (hr : N.IsBimolecularFrom r s t)
    (hΔ : normVec (N.reactionVector r) ≤ D) :
    |N.stochasticMassActionRate κ n r *
        (quadObservable P nStar (N.fireCount n r) - quadObservable P nStar n)|
      ≤ (cubicConstants (Fintype.card (Fin m) : ℝ) (κ.k r) E D |nStar s| |nStar t|).C3 *
          normVec (countDeviation nStar n) ^ 3
        + (cubicConstants (Fintype.card (Fin m) : ℝ) (κ.k r) E D |nStar s| |nStar t|).C2 *
            normVec (countDeviation nStar n) ^ 2
        + (cubicConstants (Fintype.card (Fin m) : ℝ) (κ.k r) E D |nStar s| |nStar t|).C1 *
            normVec (countDeviation nStar n)
        + (cubicConstants (Fintype.card (Fin m) : ℝ) (κ.k r) E D |nStar s| |nStar t|).C0 := by
  set card : ℝ := (Fintype.card (Fin m) : ℝ) with hcard
  set R := normVec (countDeviation nStar n) with hR
  set a := |nStar s| with ha
  set b := |nStar t| with hb
  -- the exact contribution
  have hexact := bimolecular_cubic_contribution N κ hPsym nStar n hr
  -- the deviation splits the counts
  have hdev : ∀ i, (n i : ℝ) = countDeviation nStar n i + nStar i := by
    intro i
    simp only [countDeviation]
    ring
  have hns : |(n s : ℝ)| ≤ R + a := by
    have h1 : |countDeviation nStar n s| ≤ R := abs_le_normVec (countDeviation nStar n) s
    have h2 : countDeviation nStar n s = (n s : ℝ) - nStar s := by
      simp only [countDeviation]
    have h3 : |(n s : ℝ) - nStar s| ≤ R := by
      rw [← h2]
      exact h1
    have h4 : |nStar s| = a := by rw [ha]
    calc
      |(n s : ℝ)| = |((n s : ℝ) - nStar s) + nStar s| := by
        have h5 : ((n s : ℝ) - nStar s) + nStar s = (n s : ℝ) := by ring
        rw [h5]
      _ ≤ |(n s : ℝ) - nStar s| + |nStar s| := abs_add_le _ _
      _ ≤ R + a := by linarith
  have hnt : |(n t : ℝ)| ≤ R + b := by
    have h1 : |countDeviation nStar n t| ≤ R := abs_le_normVec (countDeviation nStar n) t
    have h2 : countDeviation nStar n t = (n t : ℝ) - nStar t := by
      simp only [countDeviation]
    have h3 : |(n t : ℝ) - nStar t| ≤ R := by
      rw [← h2]
      exact h1
    have h4 : |nStar t| = b := by rw [hb]
    calc
      |(n t : ℝ)| = |((n t : ℝ) - nStar t) + nStar t| := by
        have h5 : ((n t : ℝ) - nStar t) + nStar t = (n t : ℝ) := by ring
        rw [h5]
      _ ≤ |(n t : ℝ) - nStar t| + |nStar t| := abs_add_le _ _
      _ ≤ R + b := by linarith
  -- the bilinear form is bounded
  have hA : 0 ≤ E * card ^ 2 := mul_nonneg hP.1 (by positivity)
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact normVec_nonneg _
  have hD0 : 0 ≤ D := le_trans (normVec_nonneg _) hΔ
  have hbil1 : |bilinear P (countDeviation nStar n) (N.reactionVector r)|
      ≤ E * card ^ 2 * R * D := by
    have h := bilinear_abs_le hP (countDeviation nStar n) (N.reactionVector r)
    have hx : normVec (countDeviation nStar n) ≤ R := by
      rw [hR]
    have hstep : E * card ^ 2 * normVec (countDeviation nStar n) *
          normVec (N.reactionVector r)
        ≤ E * card ^ 2 * R * D := by
      calc
        E * card ^ 2 * normVec (countDeviation nStar n) * normVec (N.reactionVector r)
            = (E * card ^ 2) * (normVec (countDeviation nStar n) *
                normVec (N.reactionVector r)) := by ring
        _ ≤ (E * card ^ 2) * (R * D) := by
          have hprod : normVec (countDeviation nStar n) * normVec (N.reactionVector r)
              ≤ R * D := by
            have hp := mul_le_mul hx hΔ (normVec_nonneg _) hR0
            linarith
          exact mul_le_mul_of_nonneg_left hprod hA
        _ = E * card ^ 2 * R * D := by ring
    calc
      |bilinear P (countDeviation nStar n) (N.reactionVector r)|
          ≤ E * card ^ 2 * normVec (countDeviation nStar n) *
              normVec (N.reactionVector r) := by
            convert h using 1
      _ ≤ E * card ^ 2 * R * D := hstep
  have hbil2 : |bilinear P (N.reactionVector r) (N.reactionVector r)|
      ≤ E * card ^ 2 * D ^ 2 := by
    have h := bilinear_abs_le hP (N.reactionVector r) (N.reactionVector r)
    have hstep : E * card ^ 2 * normVec (N.reactionVector r) *
          normVec (N.reactionVector r)
        ≤ E * card ^ 2 * D ^ 2 := by
      calc
        E * card ^ 2 * normVec (N.reactionVector r) * normVec (N.reactionVector r)
            = (E * card ^ 2) * (normVec (N.reactionVector r) * normVec (N.reactionVector r)) := by
              ring
        _ ≤ (E * card ^ 2) * (D * D) := by
          have hprod : normVec (N.reactionVector r) * normVec (N.reactionVector r) ≤ D * D := by
            have hp := mul_le_mul hΔ hΔ (normVec_nonneg _) hD0
            calc
              normVec (N.reactionVector r) * normVec (N.reactionVector r)
                  ≤ D * normVec (N.reactionVector r) :=
                    mul_le_mul_of_nonneg_right hΔ (normVec_nonneg _)
              _ ≤ D * D := mul_le_mul_of_nonneg_left hΔ hD0
          exact mul_le_mul_of_nonneg_left hprod hA
        _ = E * card ^ 2 * D ^ 2 := by ring
    calc
      |bilinear P (N.reactionVector r) (N.reactionVector r)|
          ≤ E * card ^ 2 * normVec (N.reactionVector r) *
              normVec (N.reactionVector r) := by
            convert h using 1
      _ ≤ E * card ^ 2 * D ^ 2 := hstep
  have hbracket : |2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
      bilinear P (N.reactionVector r) (N.reactionVector r)|
      ≤ 2 * E * card ^ 2 * R * D + E * card ^ 2 * D ^ 2 := by
    have h1 : |2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
        bilinear P (N.reactionVector r) (N.reactionVector r)|
        ≤ |2 * bilinear P (countDeviation nStar n) (N.reactionVector r)|
          + |bilinear P (N.reactionVector r) (N.reactionVector r)| := abs_add_le _ _
    have h2 : |2 * bilinear P (countDeviation nStar n) (N.reactionVector r)|
        = 2 * |bilinear P (countDeviation nStar n) (N.reactionVector r)| := by
      rw [abs_mul]
      congr 1
      norm_num
    calc
      |2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
          bilinear P (N.reactionVector r) (N.reactionVector r)|
          ≤ |2 * bilinear P (countDeviation nStar n) (N.reactionVector r)|
            + |bilinear P (N.reactionVector r) (N.reactionVector r)| := h1
      _ = (2 * |bilinear P (countDeviation nStar n) (N.reactionVector r)|)
            + |bilinear P (N.reactionVector r) (N.reactionVector r)| := by rw [h2]
      _ ≤ (2 * (E * card ^ 2 * R * D)) + (E * card ^ 2 * D ^ 2) := by
            exact add_le_add (mul_le_mul_of_nonneg_left hbil1 (by norm_num)) hbil2
      _ = 2 * E * card ^ 2 * R * D + E * card ^ 2 * D ^ 2 := by ring
  -- the propensity is bounded
  have ha0 : 0 ≤ a := by
    rw [ha]
    exact abs_nonneg _
  have hb0 : 0 ≤ b := by
    rw [hb]
    exact abs_nonneg _
  have hrate : |(n s : ℝ) * (n t : ℝ)| ≤ (R + a) * (R + b) := by
    calc
      |(n s : ℝ) * (n t : ℝ)| = |(n s : ℝ)| * |(n t : ℝ)| := abs_mul _ _
      _ ≤ (R + a) * (R + b) := by
        exact mul_le_mul hns hnt (abs_nonneg _) (by linarith)
  -- assemble
  have hmain : |κ.k r * (n s : ℝ) * (n t : ℝ) *
      (2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
        bilinear P (N.reactionVector r) (N.reactionVector r))|
      ≤ κ.k r * (((R + a) * (R + b)) *
        (2 * E * card ^ 2 * R * D + E * card ^ 2 * D ^ 2)) := by
    have hk : 0 ≤ κ.k r := (κ.positive r).le
    have hinner : |(n s : ℝ) * (n t : ℝ)| *
        |2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
          bilinear P (N.reactionVector r) (N.reactionVector r)|
        ≤ ((R + a) * (R + b)) *
          (2 * E * card ^ 2 * R * D + E * card ^ 2 * D ^ 2) :=
      mul_le_mul hrate hbracket (abs_nonneg _) (mul_nonneg (by linarith [hR0, ha0])
        (by linarith [hR0, hb0]))
    calc
      |κ.k r * (n s : ℝ) * (n t : ℝ) *
          (2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
            bilinear P (N.reactionVector r) (N.reactionVector r))|
          = κ.k r * (|(n s : ℝ) * (n t : ℝ)| *
              |2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
                bilinear P (N.reactionVector r) (N.reactionVector r)|) := by
            simp only [abs_mul, abs_of_nonneg hk]
            ring
      _ ≤ κ.k r * (((R + a) * (R + b)) *
          (2 * E * card ^ 2 * R * D + E * card ^ 2 * D ^ 2)) :=
        mul_le_mul_of_nonneg_left hinner hk
  -- the right-hand side is exactly the expansion of the left-hand side
  have hexp : κ.k r * (((R + a) * (R + b)) *
        (2 * E * card ^ 2 * R * D + E * card ^ 2 * D ^ 2))
      = (cubicConstants card (κ.k r) E D a b).C3 * R ^ 3
        + (cubicConstants card (κ.k r) E D a b).C2 * R ^ 2
        + (cubicConstants card (κ.k r) E D a b).C1 * R
        + (cubicConstants card (κ.k r) E D a b).C0 := by
    simp only [cubicConstants]
    ring
  rw [hexact]
  calc
    |κ.k r * (n s : ℝ) * (n t : ℝ) *
        (2 * bilinear P (countDeviation nStar n) (N.reactionVector r) +
          bilinear P (N.reactionVector r) (N.reactionVector r))|
        ≤ κ.k r * (((R + a) * (R + b)) *
          (2 * E * card ^ 2 * R * D + E * card ^ 2 * D ^ 2)) := hmain
    _ = (cubicConstants card (κ.k r) E D a b).C3 * R ^ 3
        + (cubicConstants card (κ.k r) E D a b).C2 * R ^ 2
        + (cubicConstants card (κ.k r) E D a b).C1 * R
        + (cubicConstants card (κ.k r) E D a b).C0 := hexp
    _ = (cubicConstants card (κ.k r) E D a b).C3 *
          normVec (countDeviation nStar n) ^ 3
        + (cubicConstants card (κ.k r) E D a b).C2 *
            normVec (countDeviation nStar n) ^ 2
        + (cubicConstants card (κ.k r) E D a b).C1 *
            normVec (countDeviation nStar n)
        + (cubicConstants card (κ.k r) E D a b).C0 := by rw [hR]

/-- **The cubic estimate in the "vanishing reference" form.**  If the reference count vector
vanishes on the two reactant species of the bimolecular reaction — the natural choice for the
controller species of the molecular antithetic controller — then the estimate of
`cubic_remainder_le` collapses to the requested shape

```text
|λ_r(n) (V (n + Δ_r) − V n)| ≤ C (‖n − n*‖³ + ‖n − n*‖²).
``` -/
theorem cubic_remainder_le_zero_ref (N : Network (Fin m)) (κ : N.RateConstants)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : RowBounded P E) (hPsym : Pᵀ = P)
    (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    {r : N.R} {s t : Fin m} (hr : N.IsBimolecularFrom r s t)
    (hΔ : normVec (N.reactionVector r) ≤ D)
    (hz : nStar s = 0 ∧ nStar t = 0) :
    |N.stochasticMassActionRate κ n r *
        (quadObservable P nStar (N.fireCount n r) - quadObservable P nStar n)|
      ≤ max (2 * κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D)
          (κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D ^ 2) *
        (normVec (countDeviation nStar n) ^ 3 + normVec (countDeviation nStar n) ^ 2) := by
  have hC := cubic_remainder_le N κ hP hPsym nStar n hr hΔ
  rw [hz.1, hz.2] at hC
  simp only [cubicConstants] at hC
  set R := normVec (countDeviation nStar n) with hR
  set Cmax : ℝ := max (2 * κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D)
    (κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D ^ 2) with hCmax
  have hR0 : 0 ≤ R := by
    rw [hR]
    exact normVec_nonneg _
  have hD0 : 0 ≤ D := le_trans (normVec_nonneg _) hΔ
  have hκ0 : 0 ≤ κ.k r := (κ.positive r).le
  have hE0 : 0 ≤ E := hP.1
  have hcard0 : (0 : ℝ) ≤ Fintype.card (Fin m) := by positivity
  have hCmax0 : 0 ≤ Cmax := by
    rw [hCmax]
    exact le_max_of_le_left
      (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hκ0) hE0)
        (by positivity)) hD0)
  have hA : 2 * κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D * R ^ 3 ≤ Cmax * R ^ 3 := by
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hB : κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D ^ 2 * R ^ 2 ≤ Cmax * R ^ 2 := by
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hsum : (2 * κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D * R ^ 3
      + κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D ^ 2 * R ^ 2)
      ≤ Cmax * (R ^ 3 + R ^ 2) := by
    calc
      2 * κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D * R ^ 3
          + κ.k r * E * (Fintype.card (Fin m) : ℝ) ^ 2 * D ^ 2 * R ^ 2
          ≤ (Cmax * R ^ 3) + (Cmax * R ^ 2) := add_le_add hA hB
      _ = Cmax * (R ^ 3 + R ^ 2) := by ring
  simp only [abs_zero, zero_add, add_zero, zero_mul, mul_zero] at hC
  linarith

/-! ## 3. The drift bound with the cubic term -/

variable {S : Type} [DecidableEq S] [Fintype S]

open Network

/-- **Splitting off one term of a sum.** -/
theorem sum_eq_add_sum_erase {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℝ) (a : ι)
    (ha : a ∈ s) : (∑ x ∈ s, f x) = (∑ x ∈ (s.erase a), f x) + f a := by
  have h := Finset.sum_erase_add s f ha
  linarith

/-- **A sum splits off one term.**  If `g` agrees with `f` away from `a` and vanishes at `a`,
then `∑ f = ∑ g + f a`. -/
theorem sum_split {ι : Type*} [DecidableEq ι] [Fintype ι] (f g : ι → ℝ) (a : ι)
    (h0 : g a = 0) (hag : ∀ r, r ≠ a → g r = f r) :
    (∑ r, f r) = (∑ r, g r) + f a := by
  have h1 : (∑ r, f r) = (∑ r ∈ (Finset.univ : Finset ι).erase a, f r) + f a :=
    sum_eq_add_sum_erase (Finset.univ : Finset ι) f a (Finset.mem_univ a)
  have h2 : (∑ r, g r) = (∑ r ∈ (Finset.univ : Finset ι).erase a, g r) + g a :=
    sum_eq_add_sum_erase (Finset.univ : Finset ι) g a (Finset.mem_univ a)
  have h3 : (∑ r ∈ (Finset.univ : Finset ι).erase a, f r)
      = ∑ r ∈ (Finset.univ : Finset ι).erase a, g r := by
    refine Finset.sum_congr rfl fun r hr_mem => ?_
    have hr' : r ≠ a := by
      intro h
      exact (Finset.mem_erase.mp hr_mem).left h
    exact (hag r hr').symm
  rw [h1, h2, h3, h0]
  ring

/-- **The rate constants of the trivial network**, inherited from the original network. -/
noncomputable def trivialRateConstants (N : Network S) (κ : N.RateConstants) (r : N.R) :
    RateConstants (N.withTrivialReaction r) where
  k := κ.k
  positive := fun r' => κ.positive r'

/-- The reaction vectors of the trivial network agree with those of the original network,
except for the replaced reaction. -/
theorem reactionVector_withTrivial (N : Network S) (r r' : N.R) (h : r' ≠ r) (i : S) :
    (N.withTrivialReaction r).reactionVector r' i = N.reactionVector r' i := by
  simp only [withTrivialReaction, ite_eq_right h, Network.reactionVector_apply]

/-- The trivial reaction is never unimolecular from a species. -/
theorem withTrivialReaction_not_unimolecular (N : Network S) (r r' : N.R) (h : r' = r) (i : S) :
    ¬ (N.withTrivialReaction r).IsUnimolecularFrom r' i := by
  subst h
  intro hu
  have h1 := hu.1
  simp [trivialReaction, Complex.zero] at h1

/-- The weighted increment of a reaction of the trivial network agrees with that of the original
network. -/
theorem weightedReactionIncrement_withTrivial (N : Network S) (r r' : N.R) (h : r' ≠ r)
    (w : S → ℝ) : (N.withTrivialReaction r).weightedReactionIncrement w r'
      = N.weightedReactionIncrement w r' := by
  unfold Network.weightedReactionIncrement
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [reactionVector_withTrivial N r r' h i]

/-- The propensity of a reaction of the trivial network agrees with that of the original network,
except for the replaced reaction. -/
theorem stochasticMassActionRate_withTrivial (N : Network S) (κ : N.RateConstants) (n : S → ℕ)
    (r r' : N.R) (h : r' ≠ r) :
    (N.withTrivialReaction r).stochasticMassActionRate (trivialRateConstants N κ r) n r'
      = N.stochasticMassActionRate κ n r' := by
  simp only [Network.stochasticMassActionRate, trivialRateConstants]
  rw [show (if r' = r then trivialReaction S else N.reaction r') = N.reaction r' by
        simp [h]]

/-- **The first-order drift matrix is unchanged** by replacing a bimolecular reaction by the
trivial reaction: the bimolecular reaction contributes to neither the drift matrix nor the
constant drift. -/
theorem firstOrderDriftMatrix_withTrivial (N : Network (Fin m)) (κ : N.RateConstants)
    {rAnn : N.R} {s t : Fin m} (hr : N.IsBimolecularFrom rAnn s t) :
    firstOrderDriftMatrix (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn)
      = firstOrderDriftMatrix N κ := by
  classical
  refine Matrix.ext ?_
  intro i j
  show (N.withTrivialReaction rAnn).firstOrderDriftCoefficient
        (trivialRateConstants N κ rAnn) (coordIndicator i) j
      = N.firstOrderDriftCoefficient κ (coordIndicator i) j
  unfold Network.firstOrderDriftCoefficient
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hEq : r = rAnn
  · have h1 : ¬ (N.withTrivialReaction rAnn).IsUnimolecularFrom r j := by
      rw [hEq]
      exact withTrivialReaction_not_unimolecular N rAnn rAnn rfl j
    have h2 : ¬ N.IsUnimolecularFrom r j := by
      rw [hEq]
      exact hr.not_unimolecular j
    simp [h1, h2]
  · have h3 := withTrivialReaction_isUnimolecularFrom_iff N rAnn r hEq j
    have h4 := weightedReactionIncrement_withTrivial N rAnn r hEq (coordIndicator i)
    rw [h3, h4]
    simp only [trivialRateConstants]

/-- **The drift of the counts splits** into the drift of the trivial network and the contribution
of the replaced reaction. -/
theorem countDrift_withTrivial (N : Network (Fin m)) (κ : N.RateConstants) (n : Fin m → ℕ)
    {rAnn : N.R} {s t : Fin m} (_hr : N.IsBimolecularFrom rAnn s t) :
    countDrift N κ n
      = countDrift (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) n
        + N.stochasticMassActionRate κ n rAnn • N.reactionVector rAnn := by
  funext i
  unfold countDrift
  change (∑ r : N.R, N.stochasticMassActionRate κ n r * N.reactionVector r i)
      = (∑ r : N.R, (N.withTrivialReaction rAnn).stochasticMassActionRate
            (trivialRateConstants N κ rAnn) n r
          * (N.withTrivialReaction rAnn).reactionVector r i)
        + N.stochasticMassActionRate κ n rAnn * N.reactionVector rAnn i
  have hzero : (N.withTrivialReaction rAnn).stochasticMassActionRate
        (trivialRateConstants N κ rAnn) n rAnn
      * (N.withTrivialReaction rAnn).reactionVector rAnn i = 0 := by
    rw [trivialReaction_reactionVector N rAnn]
    simp
  have hmain : (∑ r : N.R, N.stochasticMassActionRate κ n r * N.reactionVector r i)
      = (∑ r : N.R, (N.withTrivialReaction rAnn).stochasticMassActionRate
            (trivialRateConstants N κ rAnn) n r
          * (N.withTrivialReaction rAnn).reactionVector r i)
        + N.stochasticMassActionRate κ n rAnn * N.reactionVector rAnn i := by
    refine sum_split _ _ rAnn hzero ?_
    intro r hr'
    rw [reactionVector_withTrivial N rAnn r hr' i]
    rw [stochasticMassActionRate_withTrivial N κ n rAnn r hr']
  exact hmain

/-- **The quadratic remainder splits** into the remainder of the trivial network and the
contribution of the replaced reaction. -/
theorem quadRemainder_withTrivial (N : Network (Fin m)) (κ : N.RateConstants)
    (P : Matrix (Fin m) (Fin m) ℝ) (n : Fin m → ℕ)
    {rAnn : N.R} {s t : Fin m} (_hr : N.IsBimolecularFrom rAnn s t) :
    quadRemainder N κ P n
      = quadRemainder (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) P n
        + N.stochasticMassActionRate κ n rAnn *
          bilinear P (N.reactionVector rAnn) (N.reactionVector rAnn) := by
  unfold quadRemainder
  have hzero : (N.withTrivialReaction rAnn).stochasticMassActionRate
        (trivialRateConstants N κ rAnn) n rAnn
      * bilinear P ((N.withTrivialReaction rAnn).reactionVector rAnn)
          ((N.withTrivialReaction rAnn).reactionVector rAnn) = 0 := by
    rw [trivialReaction_reactionVector N rAnn]
    simp [bilinear]
  have hmain : (∑ r : N.R, N.stochasticMassActionRate κ n r *
      bilinear P (N.reactionVector r) (N.reactionVector r))
      = (∑ r : N.R, (N.withTrivialReaction rAnn).stochasticMassActionRate
            (trivialRateConstants N κ rAnn) n r *
          bilinear P ((N.withTrivialReaction rAnn).reactionVector r)
            ((N.withTrivialReaction rAnn).reactionVector r))
        + N.stochasticMassActionRate κ n rAnn *
          bilinear P (N.reactionVector rAnn) (N.reactionVector rAnn) := by
    refine sum_split _ _ rAnn hzero ?_
    intro r hr'
    have hvec : (N.withTrivialReaction rAnn).reactionVector r = N.reactionVector r := by
      funext i
      exact reactionVector_withTrivial N rAnn r hr' i
    rw [hvec]
    rw [stochasticMassActionRate_withTrivial N κ n rAnn r hr']
  exact hmain

/-- **The drift of the quadratic Lyapunov function splits.**  The drift of the closed loop is the
drift of the trivial network (the *first-order* part) plus the contribution of the bimolecular
reaction, which is the cubic term. -/
theorem drift_decomposition (N : Network (Fin m)) (κ : N.RateConstants)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P) (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    {rAnn : N.R} {s t : Fin m} (hr : N.IsBimolecularFrom rAnn s t) :
    N.observableGenerator κ (quadObservable P nStar) n
      = (N.withTrivialReaction rAnn).observableGenerator
          (trivialRateConstants N κ rAnn) (quadObservable P nStar) n
        + N.stochasticMassActionRate κ n rAnn *
          (2 * bilinear P (countDeviation nStar n) (N.reactionVector rAnn)
            + bilinear P (N.reactionVector rAnn) (N.reactionVector rAnn)) := by
  rw [observableGenerator_quadObservable N κ hP nStar n,
    observableGenerator_quadObservable (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn)
      hP nStar n]
  rw [countDrift_withTrivial N κ n hr, quadRemainder_withTrivial N κ P n hr]
  rw [bilinear_add_right, bilinear_smul]
  ring

/-! ## 4. The drift bound with the cubic term, and the two ways out -/

/-- **The sum of a two-point indicator.** -/
theorem sum_ite_two {ι : Type*} [DecidableEq ι] [Fintype ι] (s t : ι) (A B : ℝ) (hst : s ≠ t) :
    (∑ i, (if i = s then A else if i = t then B else 0)) = A + B := by
  have hmem : t ∈ (Finset.univ : Finset ι).erase s :=
    Finset.mem_erase.mpr ⟨by
      intro h
      exact hst h.symm, Finset.mem_univ t⟩
  have h1 : (∑ i, (if i = s then A else if i = t then B else 0))
      = (∑ i ∈ (Finset.univ : Finset ι).erase s, (if i = s then A else if i = t then B else 0))
        + (if s = s then A else if s = t then B else 0) :=
    sum_eq_add_sum_erase (Finset.univ : Finset ι)
      (fun i => (if i = s then A else if i = t then B else 0)) s (Finset.mem_univ s)
  have h2 : (∑ i ∈ (Finset.univ : Finset ι).erase s, (if i = s then A else if i = t then B else 0))
      = (∑ i ∈ ((Finset.univ : Finset ι).erase s).erase t,
          (if i = s then A else if i = t then B else 0))
        + (if t = s then A else if t = t then B else 0) :=
    sum_eq_add_sum_erase ((Finset.univ : Finset ι).erase s)
      (fun i => (if i = s then A else if i = t then B else 0)) t hmem
  have h3 : (∑ i ∈ ((Finset.univ : Finset ι).erase s).erase t,
      (if i = s then A else if i = t then B else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi1 : i ≠ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hi).2).1
    have hi2 : i ≠ t := (Finset.mem_erase.mp hi).1
    simp [hi1, hi2]
  rw [h1, h2, h3]
  simp only [ite_true, ite_eq_right (Ne.symm hst)]
  ring

/-- **The Foster constant of the closed loop with the annihilation**: the constant of the
first-order part of the closed loop. -/
noncomputable def molecularFosterConstant (N : Network (Fin m)) (κ : N.RateConstants)
    (rAnn : N.R)
    (L : QuadraticLyapunovCertificate (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn))
    (nStar : Fin m → ℝ) : ℝ :=
  fosterConstant (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar

/-- **The cubic bound of the drift.**  The four cubic/quadratic/linear/constant terms of
`cubicConstants`, evaluated at the norm `R` of the deviation. -/
noncomputable def cubicBound (m : ℕ) (κr E D a b R : ℝ) : ℝ :=
  (cubicConstants m κr E D a b).C3 * R ^ 3 + (cubicConstants m κr E D a b).C2 * R ^ 2 +
    (cubicConstants m κr E D a b).C1 * R + (cubicConstants m κr E D a b).C0

/-- **The drift bound with the cubic term.**  Let `N` be a network with one bimolecular reaction
`rAnn` (from the species `s`, `t`), let `N⁻` be the network in which `rAnn` is replaced by the
trivial reaction, and let `L` be a quadratic Lyapunov certificate for the *first-order* part
`N⁻`.  Then the drift of the closed loop satisfies

```text
Q V (n) ≤ − (3/8) ‖n − n*‖² + C₃ ‖n − n*‖³ + C₂ ‖n − n*‖² + C₁ ‖n − n*‖ + C₀ + K,
```

with the constants of `cubicConstants` and `K` the Foster constant of the first-order part.
This is the *general* version of the drift bound of leaf **C3** for a molecular realization of the
antithetic controller: the cubic term is displayed, not absorbed. -/
theorem fosterDrift_cubic_le (N : Network (Fin m)) (κ : N.RateConstants)
    {rAnn : N.R} {s t : Fin m} (hr : N.IsBimolecularFrom rAnn s t)
    (hfirst : (N.withTrivialReaction rAnn).IsFirstOrderNetwork)
    (L : QuadraticLyapunovCertificate (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn))
    (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    (hP : RowBounded L.P E) (hΔ : normVec (N.reactionVector rAnn) ≤ D) :
    N.observableGenerator κ (quadObservable L.P nStar) n
      ≤ -(3 / 8) * normSq (countDeviation nStar n)
        + cubicBound (Fintype.card (Fin m)) (κ.k rAnn) E D |nStar s| |nStar t|
            (normVec (countDeviation nStar n))
        + molecularFosterConstant N κ rAnn L nStar := by
  have h1 := fosterDrift_of_certificate (N.withTrivialReaction rAnn)
    (trivialRateConstants N κ rAnn) hfirst L nStar n
  have h2 := cubic_remainder_le N κ hP L.P_sym nStar n hr hΔ
  have h3 := bimolecular_cubic_contribution N κ L.P_sym nStar n hr
  have h4 : N.stochasticMassActionRate κ n rAnn *
      (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
        + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn))
      ≤ cubicBound (Fintype.card (Fin m)) (κ.k rAnn) E D |nStar s| |nStar t|
          (normVec (countDeviation nStar n)) := by
    have h5 : N.stochasticMassActionRate κ n rAnn *
        (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
          + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn))
        = N.stochasticMassActionRate κ n rAnn *
            (quadObservable L.P nStar (N.fireCount n rAnn) - quadObservable L.P nStar n) := by
      rw [Network.stochasticRate_bimolecular N κ n hr]
      rw [← h3]
      rw [Network.stochasticRate_bimolecular N κ n hr]
    rw [h5]
    exact (abs_le.mp h2).2
  rw [drift_decomposition N κ L.P_sym nStar n hr]
  have h6 : (N.withTrivialReaction rAnn).observableGenerator (trivialRateConstants N κ rAnn)
        (quadObservable L.P nStar) n
      + N.stochasticMassActionRate κ n rAnn *
        (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
          + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn))
      ≤ (-(3 / 8) * normSq (countDeviation nStar n)
          + fosterConstant (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar)
        + cubicBound (Fintype.card (Fin m)) (κ.k rAnn) E D |nStar s| |nStar t|
            (normVec (countDeviation nStar n)) := by
    calc
      (N.withTrivialReaction rAnn).observableGenerator (trivialRateConstants N κ rAnn)
            (quadObservable L.P nStar) n
          + N.stochasticMassActionRate κ n rAnn *
            (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
              + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn))
        ≤ (N.withTrivialReaction rAnn).observableGenerator (trivialRateConstants N κ rAnn)
              (quadObservable L.P nStar) n
            + cubicBound (Fintype.card (Fin m)) (κ.k rAnn) E D |nStar s| |nStar t|
                (normVec (countDeviation nStar n)) := add_le_add le_rfl h4
      _ ≤ (-(3 / 8) * normSq (countDeviation nStar n)
            + fosterConstant (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar)
            + cubicBound (Fintype.card (Fin m)) (κ.k rAnn) E D |nStar s| |nStar t|
                (normVec (countDeviation nStar n)) := add_le_add h1 le_rfl
  calc
    (N.withTrivialReaction rAnn).observableGenerator (trivialRateConstants N κ rAnn)
          (quadObservable L.P nStar) n
        + N.stochasticMassActionRate κ n rAnn *
          (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
            + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn))
        ≤ (-(3 / 8) * normSq (countDeviation nStar n)
            + fosterConstant (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar)
          + cubicBound (Fintype.card (Fin m)) (κ.k rAnn) E D |nStar s| |nStar t|
              (normVec (countDeviation nStar n)) := h6
    _ = -(3 / 8) * normSq (countDeviation nStar n)
          + cubicBound (Fintype.card (Fin m)) (κ.k rAnn) E D |nStar s| |nStar t|
              (normVec (countDeviation nStar n))
          + molecularFosterConstant N κ rAnn L nStar := by
            unfold molecularFosterConstant
            ring

/-- **The cubic term cannot be absorbed into a quadratic drift bound globally.**  For `C₃, c > 0`
there is no constant `K` with `C₃ ‖x‖³ ≤ c ‖x‖² + K` for all `x`; this is the precise form of
the obstruction which forces the two escapes of the following sections: the *sign structure* of
the shape matrix, or a *boundedness* hypothesis on the counts. -/
theorem cubic_not_absorbable (C₃ c : ℝ) (hC : 0 < C₃) (hc : 0 < c) :
    ¬ ∃ K : ℝ, ∀ x : ℝ, C₃ * x ^ 3 ≤ c * x ^ 2 + K := by
  rintro ⟨K, hK⟩
  set x : ℝ := max ((c + 1) / C₃) (|K| + 2) with hxdef
  have h1 : (c + 1) / C₃ ≤ x := le_max_left _ _
  have h2 : |K| + 2 ≤ x := le_max_right _ _
  have h3 : 0 < x := by
    have : 0 < (c + 1) / C₃ := by positivity
    linarith
  have h4 : c + 1 ≤ C₃ * x := by
    have h5 : C₃ * ((c + 1) / C₃) = c + 1 := by field_simp
    have h6 := mul_le_mul_of_nonneg_left h1 hC.le
    rw [h5] at h6
    exact h6
  have h4' : 1 ≤ C₃ * x - c := by linarith
  have h6 : K < x ^ 2 := by
    have h7 : K ≤ |K| := le_abs_self K
    nlinarith [sq_nonneg (x - 1)]
  have h9 : x ^ 2 * (C₃ * x - c) = C₃ * x ^ 3 - c * x ^ 2 := by ring
  have h10 : x ^ 2 ≤ x ^ 2 * (C₃ * x - c) := by
    simpa using mul_le_mul_of_nonneg_left h4' (sq_nonneg x)
  have h11 : K < x ^ 2 * (C₃ * x - c) := lt_of_lt_of_le h6 h10
  have h8 : c * x ^ 2 + K < C₃ * x ^ 3 := by
    linarith [h9]
  exact absurd h8 (not_lt_of_ge (hK x))

/-- **The annihilation sign condition.**  For a bimolecular annihilation `Z_s + Z_t → ∅` and a
symmetric shape matrix `P`, the condition is that the two controller rows of `P` have the same
row sum `c₀ > 0` and that every other row has row sum zero on the controller block:

```text
P s s + P t s = P s t + P t t = c₀ > 0,      P k s + P k t = 0  (k ∉ {s, t}).
```

This is the general form of the "sign conditions on `P Δ_r`" of Briat–Gupta–Khammash: the
`z₁ z₂` cross-term of the Lyapunov function is exactly the `c₀` of this condition. -/
def AnnihilationSignCondition (P : Matrix (Fin m) (Fin m) ℝ) (s t : Fin m) (c₀ : ℝ) : Prop :=
  c₀ > 0 ∧ P s s + P t s = c₀ ∧ P s t + P t t = c₀ ∧
    ∀ k, k ≠ s → k ≠ t → P k s + P k t = 0

/-- **The bilinear form with the annihilation vector.**  Under the annihilation sign condition,
the bilinear form `⟨x, P Δ_ann⟩` only sees the two controller species:
`⟨x, P Δ_ann⟩ = −c₀ (x_s + x_t)`. -/
theorem bilinear_annihilation (P : Matrix (Fin m) (Fin m) ℝ) (hP : Pᵀ = P) (x : Fin m → ℝ)
    (s t : Fin m) (c₀ : ℝ) (hst : s ≠ t) (hsign : AnnihilationSignCondition P s t c₀) :
    bilinear P x (fun u => if u = s then -1 else if u = t then -1 else 0)
      = -c₀ * (x s + x t) := by
  have hsym : ∀ i j, P i j = P j i := by
    intro i j
    have h := Matrix.transpose_apply P j i
    rw [hP] at h
    exact h.symm
  have hsum : ∑ i, x i * (P s i + P t i) = c₀ * x s + c₀ * x t := by
    have hkey : ∀ i, x i * (P s i + P t i)
        = (if i = s then c₀ * x s else if i = t then c₀ * x t else 0) := by
      intro i
      by_cases hi : i = s
      · rw [ite_eq_left hi, hi, hsign.2.1]
        ring
      · by_cases hi2 : i = t
        · rw [ite_eq_right hi, ite_eq_left hi2, hi2, hsign.2.2.1]
          ring
        · have hz := hsign.2.2.2 i hi hi2
          rw [hsym i s, hsym i t] at hz
          rw [ite_eq_right hi, ite_eq_right hi2, hz]
          ring
    calc
      (∑ i, x i * (P s i + P t i))
          = ∑ i, (if i = s then c₀ * x s else if i = t then c₀ * x t else 0) := by
            exact Finset.sum_congr rfl fun i _ => hkey i
      _ = c₀ * x s + c₀ * x t := sum_ite_two s t (c₀ * x s) (c₀ * x t) hst
  unfold bilinear
  simp only [Matrix.mulVec_apply_eq_sum]
  have hmul : ∀ i, (P *ᵥ (fun u => if u = s then -1 else if u = t then -1 else 0)) i
      = -(P i s + P i t) := by
    intro i
    simp only [Matrix.mulVec_apply_eq_sum]
    have hkey : ∀ j, P i j * (if j = s then -1 else if j = t then -1 else 0)
        = (if j = s then -P i s else if j = t then -P i t else 0) := by
      intro j
      by_cases hj : j = s
      · subst hj
        simp
      · by_cases hj2 : j = t
        · subst hj2
          simp [hj]
        · simp [hj, hj2]
    have h1 : (∑ j, P i j * (if j = s then -1 else if j = t then -1 else 0))
        = ∑ j, (if j = s then -P i s else if j = t then -P i t else 0) := by
      exact Finset.sum_congr rfl fun j _ => hkey j
    rw [h1]
    have h2 : (∑ j, (if j = s then -P i s else if j = t then -P i t else 0))
        = -P i s + -P i t := sum_ite_two s t (-P i s) (-P i t) hst
    linarith
  calc
    (∑ i, x i * (P *ᵥ (fun u => if u = s then -1 else if u = t then -1 else 0)) i)
        = ∑ i, x i * (-(P i s + P i t)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hmul]
    _ = -∑ i, x i * (P s i + P t i) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hsym i s, hsym i t]
          ring
    _ = -(c₀ * x s + c₀ * x t) := by rw [hsum]
    _ = -c₀ * (x s + x t) := by ring

/-- **The annihilation's contribution to the drift is non-positive.**  This is the *control* of
the cubic term: under the annihilation sign condition, and with the reference count vector
vanishing on the two controller species, the bimolecular annihilation *decreases* the quadratic
Lyapunov function, so its contribution to the drift is a non-positive cubic term

```text
2 c₀ κ_ann (n z₁) (n z₂) (1 − (n z₁) − (n z₂)) ≤ 0.
```

This is the general form of the `z₁ z₂` cross-term control of Briat–Gupta–Khammash and of the
repository's `CRNT.Antithetic.lyap`. -/
theorem annihilation_drift_le_zero (N : Network (Fin m)) (κ : N.RateConstants)
    {P : Matrix (Fin m) (Fin m) ℝ} (hP : Pᵀ = P) (nStar : Fin m → ℝ) (n : Fin m → ℕ)
    {rAnn : N.R} {s t : Fin m} (hr : N.IsAnnihilationFrom rAnn s t) (c₀ : ℝ)
    (hsign : AnnihilationSignCondition P s t c₀) (hz : nStar s = 0 ∧ nStar t = 0) :
    N.stochasticMassActionRate κ n rAnn *
        (quadObservable P nStar (N.fireCount n rAnn) - quadObservable P nStar n) ≤ 0 := by
  have hΔ : N.reactionVector rAnn = fun u => if u = s then -1 else if u = t then -1 else 0 :=
    hr.reactionVector
  have hcontrib := bimolecular_cubic_contribution N κ hP nStar n hr.1
  have hbil := bilinear_annihilation P hP (countDeviation nStar n) s t c₀ hr.1.ne hsign
  have hbil2 := bilinear_annihilation P hP
    (fun u => if u = s then -1 else if u = t then -1 else 0) s t c₀ hr.1.ne hsign
  have hquad : bilinear P (N.reactionVector rAnn) (N.reactionVector rAnn) = 2 * c₀ := by
    rw [hΔ]
    have hst : s ≠ t := hr.1.ne
    simp only [ite_true, ite_eq_right (Ne.symm hst)] at hbil2
    linarith
  have hdev : countDeviation nStar n s = (n s : ℝ) := by
    simp only [countDeviation]
    rw [hz.1]
    ring
  have hdevt : countDeviation nStar n t = (n t : ℝ) := by
    simp only [countDeviation]
    rw [hz.2]
    ring
  have hmain2 : κ.k rAnn * (n s : ℝ) * (n t : ℝ) *
      (2 * (-c₀ * (countDeviation nStar n s + countDeviation nStar n t)) + 2 * c₀) ≤ 0 := by
    rw [hdev, hdevt]
    have h1 : 0 ≤ (n s : ℝ) := Nat.cast_nonneg _
    have h2 : 0 ≤ (n t : ℝ) := Nat.cast_nonneg _
    have h5 : 0 < c₀ := hsign.1
    by_cases hns : (n s : ℝ) = 0
    · rw [hns]
      simp
    · by_cases hnt : (n t : ℝ) = 0
      · rw [hnt]
        simp
      · have h3 : (1 : ℝ) ≤ (n s : ℝ) := by
          have hn : 0 < n s := Nat.pos_of_ne_zero (by
            intro h
            exact hns (h ▸ Nat.cast_zero))
          exact_mod_cast Nat.succ_le_of_lt hn
        have h4 : (1 : ℝ) ≤ (n t : ℝ) := by
          have hn : 0 < n t := Nat.pos_of_ne_zero (by
            intro h
            exact hnt (h ▸ Nat.cast_zero))
          exact_mod_cast Nat.succ_le_of_lt hn
        have h6 : 0 ≤ (n s : ℝ) + (n t : ℝ) - 1 := by linarith
        have h7 : 0 ≤ c₀ * ((n s : ℝ) + (n t : ℝ) - 1) := mul_nonneg h5.le h6
        have hd : 1 - ((n s : ℝ) + (n t : ℝ)) ≤ 0 := by linarith
        have hd' : c₀ * (1 - ((n s : ℝ) + (n t : ℝ))) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos h5.le hd
        have hbr : 2 * (-c₀ * ((n s : ℝ) + (n t : ℝ))) + 2 * c₀ ≤ 0 := by
          have heq : 2 * (-c₀ * ((n s : ℝ) + (n t : ℝ))) + 2 * c₀
              = 2 * (c₀ * (1 - ((n s : ℝ) + (n t : ℝ)))) := by ring
          rw [heq]
          linarith
        have hpos : 0 ≤ κ.k rAnn * (n s : ℝ) * (n t : ℝ) :=
          mul_nonneg (mul_nonneg (κ.positive rAnn).le (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
        calc
          κ.k rAnn * (n s : ℝ) * (n t : ℝ) *
                (2 * (-c₀ * ((n s : ℝ) + (n t : ℝ))) + 2 * c₀)
              = (κ.k rAnn * (n s : ℝ) * (n t : ℝ)) *
                  (2 * (-c₀ * ((n s : ℝ) + (n t : ℝ))) + 2 * c₀) := by ring
          _ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hpos hbr
  have hrate0 : 0 ≤ N.stochasticMassActionRate κ n rAnn :=
    N.stochasticMassActionRate_nonneg κ n rAnn
  rw [hcontrib]
  have hmain : κ.k rAnn * (n s : ℝ) * (n t : ℝ) *
      (2 * bilinear P (countDeviation nStar n) (N.reactionVector rAnn)
        + bilinear P (N.reactionVector rAnn) (N.reactionVector rAnn))
      = κ.k rAnn * (n s : ℝ) * (n t : ℝ) *
          (2 * (-c₀ * (countDeviation nStar n s + countDeviation nStar n t)) + 2 * c₀) := by
    rw [hquad, hΔ, hbil]
  rw [hmain]
  exact hmain2

/-- **The Foster drift condition for the molecular realization of the antithetic controller.**
Under the annihilation sign condition, the cubic term of the drift is non-positive, and the
closed loop satisfies the *quadratic* Foster bound

```text
Q V (n) ≤ − (3/8) ‖n − n*‖² + K,
```

with `K` the Foster constant of the first-order part of the closed loop.  This is the general
plant version of the control performed by the `z₁ z₂` cross-term of `CRNT.Antithetic.lyap`. -/
theorem fosterDrift_of_sign_controlled (N : Network (Fin m)) (κ : N.RateConstants)
    {rAnn : N.R} {s t : Fin m} (hr : N.IsAnnihilationFrom rAnn s t)
    (hfirst : (N.withTrivialReaction rAnn).IsFirstOrderNetwork)
    (L : QuadraticLyapunovCertificate (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn))
    (nStar : Fin m → ℝ) (c₀ : ℝ)
    (hsign : AnnihilationSignCondition L.P s t c₀)
    (hz : nStar s = 0 ∧ nStar t = 0) (n : Fin m → ℕ) :
    N.observableGenerator κ (quadObservable L.P nStar) n
      ≤ -(3 / 8) * normSq (countDeviation nStar n)
        + molecularFosterConstant N κ rAnn L nStar := by
  have h1 := fosterDrift_of_certificate (N.withTrivialReaction rAnn)
    (trivialRateConstants N κ rAnn) hfirst L nStar n
  have h2 := annihilation_drift_le_zero N κ L.P_sym nStar n hr c₀ hsign hz
  have h3 := bimolecular_cubic_contribution N κ L.P_sym nStar n hr.1
  have h4 : N.stochasticMassActionRate κ n rAnn *
      (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
        + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn)) ≤ 0 := by
    rw [Network.stochasticRate_bimolecular N κ n hr.1]
    rw [← h3]
    exact h2
  have h5 : (N.withTrivialReaction rAnn).observableGenerator (trivialRateConstants N κ rAnn)
        (quadObservable L.P nStar) n
      + N.stochasticMassActionRate κ n rAnn *
        (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
          + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn))
      ≤ (-(3 / 8) * normSq (countDeviation nStar n)
          + fosterConstant (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar)
        + 0 :=
    add_le_add h1 h4
  rw [drift_decomposition N κ L.P_sym nStar n hr.1]
  calc
    (N.withTrivialReaction rAnn).observableGenerator (trivialRateConstants N κ rAnn)
          (quadObservable L.P nStar) n
        + N.stochasticMassActionRate κ n rAnn *
          (2 * bilinear L.P (countDeviation nStar n) (N.reactionVector rAnn)
            + bilinear L.P (N.reactionVector rAnn) (N.reactionVector rAnn))
        ≤ (-(3 / 8) * normSq (countDeviation nStar n)
            + fosterConstant (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar)
          + 0 := h5
    _ = -(3 / 8) * normSq (countDeviation nStar n)
          + molecularFosterConstant N κ rAnn L nStar := by
            unfold molecularFosterConstant
            ring

/-- **Ergodicity of the molecular realization of the antithetic controller.**  Under the
annihilation sign condition and irreducibility, the closed loop is ergodic: it has a unique
stationary probability law charging every count, and the law of the chain converges to it in
total variation from every count.  This is the Briat–Gupta–Khammash conclusion for a *general*
plant, with the cubic term controlled by the sign structure of the shape matrix. -/
theorem ergodic_of_sign_controlled (N : Network (Fin m)) (κ : N.RateConstants)
    {rAnn : N.R} {s t : Fin m} (hr : N.IsAnnihilationFrom rAnn s t)
    (hfirst : (N.withTrivialReaction rAnn).IsFirstOrderNetwork)
    (L : QuadraticLyapunovCertificate (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn))
    (nStar : Fin m → ℝ) (c₀ : ℝ)
    (hsign : AnnihilationSignCondition L.P s t c₀)
    (hz : nStar s = 0 ∧ nStar t = 0)
    (hirr : ∀ a b, (N.jumpSystem κ).ReachPos a b) :
    ∃ π : (Fin m → ℕ) → ℝ, (∀ b, 0 < π b) ∧ HasSum π 1 ∧
      (∀ u, 0 ≤ u → ∀ b, ∑' x, π x * (N.jumpSystem κ).Pmin u x b = π b) ∧
      (∀ a, Tendsto (fun t => ∑' b, |(N.jumpSystem κ).Pmin t a b - π b|) atTop (𝓝 0)) ∧
      (∀ μ : (Fin m → ℕ) → ℝ, (∀ b, 0 ≤ μ b) → HasSum μ 1 →
        (∀ u, 0 ≤ u → ∀ b, ∑' x, μ x * (N.jumpSystem κ).Pmin u x b = μ b) → μ = π) := by
  have hV : ∀ n : Fin m → ℕ, 0 ≤ quadObservable L.P nStar n :=
    quadObservable_nonneg (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar
  have hf : ∀ n : Fin m → ℕ, 0 ≤ fosterNormLike (N.withTrivialReaction rAnn)
      (trivialRateConstants N κ rAnn) L nStar n :=
    fosterNormLike_nonneg (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar
  have hff : ∀ R : ℝ, {n : Fin m → ℕ | fosterNormLike (N.withTrivialReaction rAnn)
      (trivialRateConstants N κ rAnn) L nStar n ≤ R}.Finite :=
    fosterNormLike_finite (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar
  have hK : 0 ≤ molecularFosterConstant N κ rAnn L nStar :=
    fosterConstant_nonneg (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar
  have hdrift : ∀ n : Fin m → ℕ, (N.jumpSystem κ).drift (quadObservable L.P nStar) n
      ≤ -fosterNormLike (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar n
        + molecularFosterConstant N κ rAnn L nStar := by
    intro n
    rw [jumpSystem_drift_observableGenerator]
    have h := fosterDrift_of_sign_controlled N κ hr hfirst L nStar c₀ hsign hz n
    calc
      N.observableGenerator κ (quadObservable L.P nStar) n
          ≤ -(3 / 8) * normSq (countDeviation nStar n)
            + molecularFosterConstant N κ rAnn L nStar := h
      _ ≤ -fosterNormLike (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar n
            + molecularFosterConstant N κ rAnn L nStar := by
            have h2 : 0 ≤ fosterNormLike (N.withTrivialReaction rAnn)
                (trivialRateConstants N κ rAnn) L nStar n := hf n
            unfold fosterNormLike at h2 ⊢
            linarith
  have hstoch : ∀ t, 0 ≤ t → ∀ n, HasSum (fun m => (N.jumpSystem κ).Pmin t n m) 1 := by
    intro t ht n
    refine (N.jumpSystem κ).hasSum_Pmin_one_of_drift_affine (quadObservable L.P nStar)
      hV
      (quadObservable_finite (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn)
        L nStar)
      (c := 0) (d := molecularFosterConstant N κ rAnn L nStar) (by norm_num) hK ?_ ht n
    intro a
    have h := hdrift a
    have h2 := hf a
    linarith
  exact ergodic_of_fosterDrift (N.jumpSystem κ) (quadObservable L.P nStar)
    (fosterNormLike (N.withTrivialReaction rAnn) (trivialRateConstants N κ rAnn) L nStar)
    { V_nonneg := hV
      f_nonneg := hf
      f_finite := hff
      K := molecularFosterConstant N κ rAnn L nStar
      K_nonneg := hK
      drift_le := hdrift } hstoch hirr

/-! ## 5. The instance: the repository's antithetic closed loop -/

namespace AntitheticInstance

open CRNT.Antithetic

/-- **The annihilation of the antithetic closed loop** `Z₁ + Z₂ → ∅` is a bimolecular
annihilation between the species `0` (`Z₁`) and `1` (`Z₂`): the source complex is `Z₁ + Z₂` and
the target is empty. -/
theorem annihilation_is_annihilation :
    closedLoop.IsAnnihilationFrom (1 : Fin 5) 0 1 := by
  constructor
  · refine ⟨by decide, by decide, by decide, ?_⟩
    intro u hu hu2
    fin_cases u
    · simp at hu
    · simp at hu2
    · decide
  · intro u
    fin_cases u <;> decide

/-- **The general-plant shape matrix of the antithetic Lyapunov function.**  In the coordinates
`(z₁, z₂, x)` the matrix is

```text
P (a c e p) = [[a, c − a, e], [c − a, a, −e], [e, −e, p]],
```

whose quadratic form is `a (z₁ − z₂)² + 2 c z₁ z₂ + 2 e x (z₁ − z₂) + p x²`: the `a`-part is
the charge part, the `c`-part is the `z₁ z₂` cross-term, the `e`-part is the coupling of the
charge with the output, and the `p`-part is the output part.  The repository's Lyapunov function
`CRNT.Antithetic.lyap` is this form with `a = c_A` (or `c_B`), `2 c = c_d`, `2 e = −c_c` and
`p = c_b`. -/
def generalMatrix (a c e p : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  ![![a, c - a, e], ![c - a, a, -e], ![e, -e, p]]

/-- **The general matrix satisfies the annihilation sign condition** as soon as `c > 0`: the two
controller rows have row sum `c`, and the output row has row sum zero on the controller block.
This is the general statement of the `z₁ z₂` cross-term control of Briat–Gupta–Khammash. -/
theorem generalMatrix_sign_condition (a c e p : ℝ) (hc : 0 < c) :
    AnnihilationSignCondition (generalMatrix a c e p) 0 1 c := by
  refine ⟨hc, ?_, ?_, ?_⟩
  · simp [generalMatrix]
  · simp [generalMatrix]
  · intro k hk0 hk1
    fin_cases k
    · simp at hk0
    · simp at hk1
    · simp [generalMatrix]

end AntitheticInstance

end GeneralPlant
end Design
end CRNT
