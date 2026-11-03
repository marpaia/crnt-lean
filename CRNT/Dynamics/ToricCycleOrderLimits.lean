import CRNT.Dynamics.ToricEmbeddingOrder
import CRNT.Dynamics.ToricCycleSortedBase

/-!
# How far the monotone-cycle kernel can be relaxed

`cycle_velocity_mem_polarCone` (`CRNT.Dynamics.ToricEmbeddingOrder`) proves
`∑_{i<n} a i • (u (i+1) − u i) ∈ Cᵒ` from `Monotone a` together with `CMinimal C u`.  Through the
Abel kernel `cycle_velocity_eq_nonneg_combination` the velocity is
`∑_{i<n-1} (a (i+1) − a i) • (u 0 − u (i+1))`, so all that is really needed is that each summand
pair off nonpositively against every `z ∈ C`.  That is the hypothesis `CycleSignCompatible` below, and
`cycle_velocity_mem_polarCone_of_signCompatible` proves the conclusion from it; `Monotone` plus
`CMinimal` is the special case where the two factors are separately nonnegative and nonpositive
(`signCompatible_of_monotone_of_cminimal`).

The point of isolating it is negative.  `Examples/CycleRateNonMonotone.lean` shows `Monotone a` is
unattainable when the cycle is traversed in graph order, so one would like to relax it.
`CycleSignCompatible` is the natural candidate — and
`monotone_of_signCompatible_of_cminimal_strict` shows it is not a relaxation at all: as soon as some
`z ∈ C` separates `u 0` strictly from `u (i+1)`, sign compatibility at `i` *forces*
`a i ≤ a (i+1)`.  Because `CMinimal` already makes `⟪z, u 0 − u (i+1)⟫ ≤ 0` for every `z ∈ C`, the
two hypotheses cannot be traded against each other: keeping `CMinimal` and the Abel kernel pins the
coefficients to be monotone wherever the minimality is strict.

Consequence for `docs/persistence-gac.md` item 3: repairing `NetworkCycleDecomposition` cannot be
done by weakening its ordering hypothesis.  Everything in the Abel expansion is referred to the
single base vertex `u 0`, so the repair has to change the *decomposition* — splitting a cycle at its
coefficient descents, or expanding about several bases — rather than the hypothesis on `a`.
-/

open scoped InnerProductSpace
open Finset

namespace CRNT

section CycleSignCompatible

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Each Abel summand of the cyclic velocity pairs nonpositively with every `z ∈ C`. -/
def CycleSignCompatible (C : Set E) (u : ℕ → E) (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i ∈ range (n - 1), ∀ z ∈ C, (a (i + 1) - a i) * ⟪z, u 0 - u (i + 1)⟫_ℝ ≤ 0

/-- **Monotone coefficients with a `C`-minimal base are sign compatible.**  The first factor is
nonnegative by monotonicity, the second nonpositive by minimality. -/
theorem signCompatible_of_monotone_of_cminimal {C : Set E} {u : ℕ → E} {a : ℕ → ℝ} {n : ℕ}
    (hmono : Monotone a) (hmin : CMinimal C u) :
    CycleSignCompatible C u a n := by
  intro i _ z hz
  have hc : (0 : ℝ) ≤ a (i + 1) - a i := sub_nonneg.mpr (hmono (Nat.le_succ i))
  have hd : ⟪z, u 0 - u (i + 1)⟫_ℝ ≤ 0 := by
    rw [inner_sub_right, sub_nonpos]
    exact hmin hz (i + 1)
  exact mul_nonpos_of_nonneg_of_nonpos hc hd

/-- **Sign compatibility suffices for the cyclic velocity to be polar.**  A strict generalization
of `cycle_velocity_mem_polarCone`: only the Abel summands' pairing matters, not the sign of either
factor separately. -/
theorem cycle_velocity_mem_polarCone_of_signCompatible {C : Set E} (u : ℕ → E) (a : ℕ → ℝ)
    (n : ℕ) (hcyc : u n = u 0) (hsign : CycleSignCompatible C u a n) :
    (∑ i ∈ range n, a i • (u (i + 1) - u i)) ∈ polarCone C := by
  rw [cycle_velocity_eq_nonneg_combination u a n hcyc, mem_polarCone]
  intro z hz
  rw [inner_sum]
  refine Finset.sum_nonpos ?_
  intro i hi
  rw [real_inner_smul_right]
  exact hsign i hi z hz

/-- **Sign compatibility is not a relaxation.**  Given a `C`-minimal base, sign compatibility at
`i` *forces* the coefficients to increase there, as soon as some `z ∈ C` separates `u 0` from
`u (i+1)` at all.  So the ordering hypothesis of `cycle_velocity_mem_polarCone` cannot be traded
against its minimality hypothesis: everything in the Abel expansion is referred to the single base
vertex `u 0`, and minimality already fixes the sign of the second factor. -/
theorem monotone_of_signCompatible_of_cminimal_strict {C : Set E} {u : ℕ → E} {a : ℕ → ℝ}
    {n i : ℕ} (hi : i ∈ range (n - 1)) (hsign : CycleSignCompatible C u a n)
    (hmin : CMinimal C u) {z : E} (hz : z ∈ C)
    (hne : ⟪z, u 0⟫_ℝ ≠ ⟪z, u (i + 1)⟫_ℝ) :
    a i ≤ a (i + 1) := by
  have hle : ⟪z, u 0⟫_ℝ ≤ ⟪z, u (i + 1)⟫_ℝ := hmin hz (i + 1)
  have hd : ⟪z, u 0 - u (i + 1)⟫_ℝ < 0 := by
    rw [inner_sub_right, sub_neg]
    exact lt_of_le_of_ne hle hne
  have hmul := hsign i hi z hz
  nlinarith [hmul, hd]


/-- **Assembly form: a closed step family with monotone coefficients and nonnegative partial sums
has polar velocity.**  The caller supplies the ordering; nothing here needs a permutation.  Given
steps `e` whose first `n` sum to zero, coefficients `c` nondecreasing in that order, and partial
sums that pair nonnegatively with every `z ∈ C`, the velocity `∑_{i<n} c i • e i` lies in `Cᵒ`.

This is the form a cycle decomposition can actually be fed to.  The walk is built here as the
partial-sum sequence, so `vec` and `closed` are discharged internally, `mono` is the caller's
`hmono`, and `cmin` is the caller's `hmin`.  Since `∑ c i • e i` depends only on the multiset of
pairs `(c i, e i)`, the caller is free to permute the steps into increasing-`c` order; the partial
sums for the sorted order are supplied by `inner_cyclicStep_sum_nonneg_of_orderRefines`
(`Dynamics/ToricCycleSortedBase.lean`) under the chamber condition `OrderRefines`. -/
theorem sum_smul_mem_polarCone_of_monotone_partialSums {C : Set E} {n : ℕ}
    (e : ℕ → E) (c : ℕ → ℝ) (hzero : ∑ j ∈ range n, e j = 0) (hmono : Monotone c)
    (hmin : ∀ z ∈ C, ∀ k, 0 ≤ ⟪z, ∑ j ∈ range k, e j⟫_ℝ) :
    (∑ i ∈ range n, c i • e i) ∈ polarCone C := by
  set u : ℕ → E := fun k => ∑ j ∈ range k, e j with hu
  have hstep : ∀ i, u (i + 1) - u i = e i := by
    intro i
    simp [hu, Finset.sum_range_succ]
  have hcyc : u n = u 0 := by simp [hu, hzero]
  have hcmin : CMinimal C u := by
    intro z hz i
    have h0 : ⟪z, u 0⟫_ℝ = 0 := by simp [hu]
    rw [h0]
    exact hmin z hz i
  have hvel := cycle_velocity_mem_polarCone u c n hcyc hmono hcmin
  have hrw : ∑ i ∈ range n, c i • (u (i + 1) - u i) = ∑ i ∈ range n, c i • e i :=
    Finset.sum_congr rfl fun i _ => by rw [hstep i]
  rwa [hrw] at hvel

end CycleSignCompatible

section Capstone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `range k` is the `Fin.val`-image of the positions below `k`, when `k ≤ n`. -/
theorem range_eq_image_val {n k : ℕ} (hk : k ≤ n) :
    Finset.image (Fin.val) (Finset.univ.filter fun p : Fin n => (p : ℕ) < k)
      = Finset.range k := by
  classical
  ext j
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact hp
  · intro hj
    exact ⟨⟨j, lt_of_lt_of_le hj hk⟩, hj, rfl⟩

/-- **Cyclic velocity is polar under the chamber condition, with no ordering hypothesis on the
coefficients.**  For a cycle of vertices `y : Fin n → E` traversed in graph order, coefficients
`a : Fin n → ℝ`, and a cone `C` on which the coefficient order refines the vertex order
(`OrderRefines`), the velocity `∑ i, a i • (y (i+1) - y i)` lies in `Cᵒ`.

This is the assembled replacement for `cycle_velocity_mem_polarCone` at cycle level.  It needs
neither `Monotone a` — unattainable in graph order, see `Examples/CycleRateNonMonotone.lean` — nor a
separate `CMinimal` hypothesis.  Both are produced internally: the steps are permuted into
increasing-coefficient order by `Tuple.sort` (legitimate because the velocity depends only on the
multiset of pairs `(a i, step i)`), the prefixes of that sort are downward closed
(`downwardClosed_sortedPrefix`), and their partial sums pair nonnegatively with every `z ∈ C`
(`inner_cyclicStep_sum_nonneg_of_orderRefines`). -/
theorem cycle_velocity_mem_polarCone_of_orderRefines {C : Set E} {n : ℕ} [NeZero n]
    (y : Fin n → E) (a : Fin n → ℝ) (hrefine : OrderRefines C y a) :
    (∑ i, a i • (y (i + 1) - y i)) ∈ polarCone C := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set σ : Equiv.Perm (Fin n) := Tuple.sort a with hσ
  set f : Fin n → E := fun i => y (i + 1) - y i with hf
  set cl : ℕ → Fin n := fun j => ⟨min j (n - 1), by omega⟩ with hcl
  set e : ℕ → E := fun j => if h : j < n then f (σ ⟨j, h⟩) else 0 with he
  set c : ℕ → ℝ := fun j => a (σ (cl j)) with hc
  have hclmono : Monotone cl := by
    intro j j' hjj'
    simp only [hcl, Fin.mk_le_mk]
    omega
  have hcmono : Monotone c := fun j j' h => Tuple.monotone_sort a (hclmono h)
  -- the ℕ-indexed velocity is the original velocity
  have hvel : ∑ i ∈ Finset.range n, c i • e i = ∑ i, a i • f i := by
    have hstep : ∑ i ∈ Finset.range n, c i • e i = ∑ k : Fin n, a (σ k) • f (σ k) := by
      rw [← Fin.sum_univ_eq_sum_range (fun j : ℕ => c j • e j) n]
      refine Finset.sum_congr rfl ?_
      intro k _
      have hklt : (k : ℕ) < n := k.isLt
      have hclk : cl (k : ℕ) = k := by
        apply Fin.ext
        simp only [hcl, Fin.val_mk]
        omega
      simp only [hc, he, dif_pos hklt, hclk]
    rw [hstep]
    exact Equiv.sum_comp σ (fun i => a i • f i)
  -- prefix sums, for k ≤ n, are the sorted-prefix cyclic step sums
  have hpre : ∀ k, k ≤ n → ∑ j ∈ Finset.range k, e j = ∑ i ∈ sortedPrefix a k, f i := by
    intro k hk
    rw [sortedPrefix, Finset.sum_image (fun p _ q _ h => σ.injective h),
      ← range_eq_image_val hk,
      Finset.sum_image (fun p _ q _ h => Fin.val_injective h)]
    refine Finset.sum_congr rfl ?_
    intro p hp
    have hplt : (p : ℕ) < n := p.isLt
    simp only [he, dif_pos hplt]
  -- the total is zero: the steps telescope round the cycle
  have hzero : ∑ j ∈ Finset.range n, e j = 0 := by
    rw [hpre n le_rfl]
    have hall : sortedPrefix a n = Finset.univ := by
      rw [sortedPrefix]
      apply Finset.eq_univ_of_card
      rw [Finset.card_image_of_injective _ σ.injective]
      have : (Finset.univ.filter fun p : Fin n => (p : ℕ) < n) = Finset.univ := by
        apply Finset.filter_true_of_mem
        intro p _
        exact p.isLt
      rw [this, Finset.card_univ]
    rw [hall, hf]
    rw [Finset.sum_sub_distrib]
    have : ∑ i : Fin n, y (i + 1) = ∑ i : Fin n, y i :=
      Equiv.sum_comp (Equiv.addRight (1 : Fin n)) y
    rw [this, sub_self]
  -- partial sums pair nonnegatively with every direction of `C`
  have hmin : ∀ z ∈ C, ∀ k, 0 ≤ ⟪z, ∑ j ∈ Finset.range k, e j⟫_ℝ := by
    intro z hz k
    by_cases hk : k ≤ n
    · rw [hpre k hk]
      exact inner_cyclicStep_sum_nonneg_of_orderRefines y a hrefine
        (downwardClosed_sortedPrefix a k) hz
    · have hsub : Finset.range n ⊆ Finset.range k :=
        fun j hj => Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) (le_of_not_ge hk))
      have hout : ∀ j ∈ Finset.range k, j ∉ Finset.range n → e j = 0 := by
        intro j _ hjn
        rw [Finset.mem_range] at hjn
        simp only [he, dif_neg hjn]
      rw [← Finset.sum_subset hsub hout, hzero, inner_zero_right]
  have hres := sum_smul_mem_polarCone_of_monotone_partialSums e c hzero hcmono hmin
  rwa [hvel] at hres

end Capstone

section OrderChamber

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The order chamber of a coefficient vector.**  The directions along which the vertex ordering
is consistent with the coefficient ordering.  It is cut out by the half-spaces
`⟪z, y j - y i⟫ ≥ 0` over the pairs with `a i ≤ a j`, so it is a closed convex cone, and it is the
largest set for which `OrderRefines` holds by construction. -/
def OrderChamber {n : ℕ} (y : Fin n → E) (a : Fin n → ℝ) : Set E :=
  {z | ∀ i j, a i ≤ a j → ⟪z, y i⟫_ℝ ≤ ⟪z, y j⟫_ℝ}

theorem orderRefines_orderChamber {n : ℕ} (y : Fin n → E) (a : Fin n → ℝ) :
    OrderRefines (OrderChamber y a) y a :=
  fun _ hz i j hij => hz i j hij

/-- **Unconditional cycle-level toric inclusion.**  With no hypotheses at all, the cyclic velocity
lies in the polar cone of its own order chamber.  This is `cycle_velocity_mem_polarCone_of_orderRefines`
instantiated at the largest admissible cone, and it is the cycle-level form of the toric
differential inclusion: the velocity is dual to every direction whose vertex ordering agrees with
the coefficient ordering. -/
theorem cycle_velocity_mem_polarCone_orderChamber {n : ℕ} [NeZero n]
    (y : Fin n → E) (a : Fin n → ℝ) :
    (∑ i, a i • (y (i + 1) - y i)) ∈ polarCone (OrderChamber y a) :=
  cycle_velocity_mem_polarCone_of_orderRefines y a (orderRefines_orderChamber y a)

/-- **The mass-action direction lies in the order chamber.**  If the coefficients are the
mass-action rates at `x` with a common rate constant — `a i = κ · exp ⟪z, y i⟫` with `z = log x` —
then `z` itself belongs to `OrderChamber y a`, since `exp` is strictly monotone.  So
`cycle_velocity_mem_polarCone_orderChamber` is non-vacuous at exactly the point whose dynamics it
describes. -/
theorem mem_orderChamber_of_massAction {n : ℕ} (y : Fin n → E) (z : E) {κ : ℝ} (hκ : 0 < κ)
    (a : Fin n → ℝ) (ha : ∀ i, a i = κ * Real.exp ⟪z, y i⟫_ℝ) :
    z ∈ OrderChamber y a := by
  intro i j hij
  rw [ha i, ha j] at hij
  have hexp : Real.exp ⟪z, y i⟫_ℝ ≤ Real.exp ⟪z, y j⟫_ℝ :=
    le_of_mul_le_mul_left hij hκ
  exact Real.exp_le_exp.mp hexp



/-- **General form: any strictly monotone reparametrisation of a linear functional lies in its own
order chamber.**  If `a i = g ⟪z, y i⟫` for a strictly monotone `g`, then `z ∈ OrderChamber y a`.
`mem_orderChamber_of_massAction` is the case `g = (κ * Real.exp ·)`. -/
theorem mem_orderChamber_of_strictMono {n : ℕ} (y : Fin n → E) (z : E) (a : Fin n → ℝ)
    {g : ℝ → ℝ} (hg : StrictMono g) (ha : ∀ i, a i = g ⟪z, y i⟫_ℝ) :
    z ∈ OrderChamber y a := by
  intro i j hij
  rw [ha i, ha j] at hij
  exact hg.le_iff_le.mp hij

/-- **Non-uniform rate constants break the chamber membership.**  With `a i = κ i * exp ⟪z, y i⟫`
the coefficient ordering is the ordering of `log (κ i) + ⟪z, y i⟫`, not of `⟪z, y i⟫`, so `z` need
not lie in `OrderChamber y a`.  What survives is the reparametrised statement: `z` lies in the
chamber of the *shifted* values.  Concretely, `a i ≤ a j` is equivalent to
`Real.log (κ i) + ⟪z, y i⟫ ≤ Real.log (κ j) + ⟪z, y j⟫`.

This is the exact obstruction to extending `cycle_velocity_mem_polarCone_orderChamber` to
non-uniform kinetics: `cycle_velocity_mem_polarCone_orderChamber` itself holds for every `a`, but
the direction `z = log x` is only guaranteed to be in the chamber when the rate constants are
uniform.  The standard repair is to homogenise, replacing `y i` by `(y i, log (κ i))` and `z` by
`(z, 1)` in `E × ℝ`; that requires the `WithLp 2 (E × ℝ)` inner-product structure and is left to the
network-level packaging. -/
theorem le_iff_shifted_le_of_massAction {n : ℕ} (y : Fin n → E) (z : E) (κ : Fin n → ℝ)
    (hκ : ∀ i, 0 < κ i) (a : Fin n → ℝ) (ha : ∀ i, a i = κ i * Real.exp ⟪z, y i⟫_ℝ)
    (i j : Fin n) :
    a i ≤ a j ↔
      Real.log (κ i) + ⟪z, y i⟫_ℝ ≤ Real.log (κ j) + ⟪z, y j⟫_ℝ := by
  have hi : a i = Real.exp (Real.log (κ i) + ⟪z, y i⟫_ℝ) := by
    rw [ha i, Real.exp_add, Real.exp_log (hκ i)]
  have hj : a j = Real.exp (Real.log (κ j) + ⟪z, y j⟫_ℝ) := by
    rw [ha j, Real.exp_add, Real.exp_log (hκ j)]
  rw [hi, hj, Real.exp_le_exp]

end OrderChamber



section Scalar

/-- **Scalar core: a closed loop's left-endpoint sum is nonpositive.**  For a cyclic value function
`s` and weights `a` whose ordering is consistent with `s`'s, `∑ i, a i * (s (i+1) - s i) ≤ 0`.

This is `cycle_velocity_mem_polarCone_orderChamber` at `E = ℝ` paired with the direction `1`, and it
is the discrete form of `∮ g(s) ds = 0` evaluated with left endpoints: an increasing weight
underestimates on the rising steps and overestimates on the falling ones, so the loop sum cannot be
positive. -/
theorem sum_mul_cyclicDiff_nonpos_of_monotone {n : ℕ} [NeZero n] (s : Fin n → ℝ) (a : Fin n → ℝ)
    (hord : ∀ i j, a i ≤ a j → s i ≤ s j) :
    ∑ i, a i * (s (i + 1) - s i) ≤ 0 := by
  have hz : (1 : ℝ) ∈ OrderChamber s a := by
    intro i j hij
    simpa using hord i j hij
  have hmem := cycle_velocity_mem_polarCone_orderChamber s a
  have h := (mem_polarCone.mp hmem) hz
  simpa [smul_eq_mul] using h

end Scalar

section MassAction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Uniform rate constants: the cycle velocity opposes the log-concentration direction.**  If the
coefficients are a strictly monotone reparametrisation of `⟪z, y i⟫` — mass action at `z = log x`
with a common rate constant — then `⟪z, velocity⟫ ≤ 0`. -/
theorem inner_cycle_velocity_nonpos_of_strictMono {n : ℕ} [NeZero n]
    (y : Fin n → E) (z : E) (a : Fin n → ℝ) {g : ℝ → ℝ} (hg : StrictMono g)
    (ha : ∀ i, a i = g ⟪z, y i⟫_ℝ) :
    ⟪z, ∑ i, a i • (y (i + 1) - y i)⟫_ℝ ≤ 0 :=
  (mem_polarCone.mp (cycle_velocity_mem_polarCone_orderChamber y a))
    (mem_orderChamber_of_strictMono y z a hg ha)

/-- **Non-uniform rate constants: the homogenised inequality, with its correction term explicit.**
For `a i = κ i * exp ⟪z, y i⟫` with every `κ i > 0`,

  `⟪z, velocity⟫ ≤ - ∑ i, a i * (log (κ (i+1)) - log (κ i))`.

The proof applies `sum_mul_cyclicDiff_nonpos_of_monotone` to the *shifted* values
`log (κ i) + ⟪z, y i⟫`, for which the coefficient ordering is consistent
(`le_iff_shifted_le_of_massAction`); the shift is exactly the homogenisation
`y i ↦ (y i, log (κ i))`.

The correction term has **no determined sign**: the increments `log (κ (i+1)) - log (κ i))` sum to
zero around the cycle, but they are weighted by the rates `a i`, so the weighted sum can go either
way.  Hence `inner_cycle_velocity_nonpos_of_strictMono` does *not* extend to non-uniform kinetics,
and a single cycle's velocity need not oppose `log x`.  This is what the slack parameter `δ` of
`Geometry/ToricFan.lean`'s `toricGenerators` is for: the cone must be fattened by an amount
controlled by the spread of the rate constants. -/
theorem massAction_cycle_inner_le_kappaCorrection {n : ℕ} [NeZero n]
    (y : Fin n → E) (z : E) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (a : Fin n → ℝ) (ha : ∀ i, a i = κ i * Real.exp ⟪z, y i⟫_ℝ) :
    ⟪z, ∑ i, a i • (y (i + 1) - y i)⟫_ℝ
      ≤ - ∑ i, a i * (Real.log (κ (i + 1)) - Real.log (κ i)) := by
  set sh : Fin n → ℝ := fun i => Real.log (κ i) + ⟪z, y i⟫_ℝ with hsh
  have hord : ∀ i j, a i ≤ a j → sh i ≤ sh j := by
    intro i j hij
    exact (le_iff_shifted_le_of_massAction y z κ hκ a ha i j).mp hij
  have hloop := sum_mul_cyclicDiff_nonpos_of_monotone sh a hord
  have hsplit : ∀ i : Fin n, a i * (sh (i + 1) - sh i)
      = a i * (⟪z, y (i + 1)⟫_ℝ - ⟪z, y i⟫_ℝ)
        + a i * (Real.log (κ (i + 1)) - Real.log (κ i)) := by
    intro i
    simp only [hsh]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib] at hloop
  have hinner : ⟪z, ∑ i, a i • (y (i + 1) - y i)⟫_ℝ
      = ∑ i, a i * (⟪z, y (i + 1)⟫_ℝ - ⟪z, y i⟫_ℝ) := by
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [real_inner_smul_right, inner_sub_right]
  rw [hinner]
  linarith


/-- **Quantitative form: the correction is controlled by the rate-constant spread.**  If successive
log rate constants around the cycle differ by at most `M`, then

  `⟪z, velocity⟫ ≤ M * ∑ i, a i`.

So the failure of `inner_cycle_velocity_nonpos_of_strictMono` under non-uniform kinetics is bounded
by the spread of the rate constants times the total rate, and it degrades continuously: at `M = 0`
the uniform result is recovered.  This is the shape the slack parameter `δ` of
`Geometry/ToricFan.lean`'s `toricGenerators` needs — a fattening of the cone proportional to the
`κ`-spread rather than an unquantified relaxation. -/
theorem massAction_cycle_inner_le_kappaSpread {n : ℕ} [NeZero n]
    (y : Fin n → E) (z : E) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (a : Fin n → ℝ) (ha : ∀ i, a i = κ i * Real.exp ⟪z, y i⟫_ℝ)
    {M : ℝ} (hM : ∀ i, |Real.log (κ (i + 1)) - Real.log (κ i)| ≤ M) :
    ⟪z, ∑ i, a i • (y (i + 1) - y i)⟫_ℝ ≤ M * ∑ i, a i := by
  have hapos : ∀ i, 0 < a i := by
    intro i
    rw [ha i]
    exact mul_pos (hκ i) (Real.exp_pos _)
  have hstep : ∀ i : Fin n,
      a i * (-(Real.log (κ (i + 1)) - Real.log (κ i))) ≤ M * a i := by
    intro i
    have hbound : -(Real.log (κ (i + 1)) - Real.log (κ i)) ≤ M :=
      le_trans (neg_le_abs _) (hM i)
    calc a i * (-(Real.log (κ (i + 1)) - Real.log (κ i)))
        ≤ a i * M := by
          exact mul_le_mul_of_nonneg_left hbound (hapos i).le
      _ = M * a i := by ring
  have hsum : - ∑ i, a i * (Real.log (κ (i + 1)) - Real.log (κ i)) ≤ M * ∑ i, a i := by
    have hneg : - ∑ i, a i * (Real.log (κ (i + 1)) - Real.log (κ i))
        = ∑ i, a i * (-(Real.log (κ (i + 1)) - Real.log (κ i))) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hneg, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => hstep i
  exact le_trans
    (massAction_cycle_inner_le_kappaCorrection y z κ hκ a ha) hsum


/-- **Non-uniform rate constants are a translation of the evaluation point, when realizable.**  If
some `w` realizes the log rate constants as `⟪w, y i⟫ = log (κ i)`, then
`a i = exp ⟪z + w, y i⟫`, so the cycle velocity opposes the *shifted* direction `z + w`:

  `⟪z + w, velocity⟫ ≤ 0`.

This is the correct relationship to the slack `δ` of `Geometry/ToricFan.lean`'s `toricGenerators`.
That `δ` is a **spatial** tolerance — it admits the cones of the fan whose `infDist` to the
evaluation point is below `δ`, not an additive slack in the polar inequality.  Non-uniform kinetics
therefore does not need the conclusion weakened; it needs the evaluation point moved, by `w`, and
`‖w‖` is the displacement `δ` must cover.

When `log ∘ κ` is *not* of the form `⟪w, y ·⟫` — i.e. not in the image of the complex matrix — no
translation realizes it and the residual is genuine; `massAction_cycle_inner_le_kappaSpread` bounds
that residual by the `κ`-spread. -/
theorem inner_cycle_velocity_nonpos_of_realizable_kappa {n : ℕ} [NeZero n]
    (y : Fin n → E) (z w : E) (κ : Fin n → ℝ) (hκ : ∀ i, 0 < κ i)
    (a : Fin n → ℝ) (ha : ∀ i, a i = κ i * Real.exp ⟪z, y i⟫_ℝ)
    (hw : ∀ i, ⟪w, y i⟫_ℝ = Real.log (κ i)) :
    ⟪z + w, ∑ i, a i • (y (i + 1) - y i)⟫_ℝ ≤ 0 := by
  refine inner_cycle_velocity_nonpos_of_strictMono y (z + w) a Real.exp_strictMono ?_
  intro i
  rw [ha i, inner_add_left, hw i, Real.exp_add, Real.exp_log (hκ i)]
  ring


/-- **A linear relation among the cycle's complexes obstructs realizability.**  If
`∑ i, c i • y i = 0` while `∑ i, c i * v i ≠ 0`, then no `w` satisfies `⟪w, y i⟫ = v i`.

Consequence for `inner_cycle_velocity_nonpos_of_realizable_kappa`: its hypothesis is a *circuit
condition* on the rate constants.  Whenever the cycle's source complexes are linearly dependent —
which happens as soon as the cycle is longer than the stoichiometric rank — every relation
`∑ c i • y i = 0` forces `∑ c i * log (κ i) = 0` on any realizable `κ`, i.e. a multiplicative
condition `∏ κ i ^ c i = 1`.  Generic rate constants violate it, so the residual case is not
exceptional but typical, and the translation route alone does not cover non-uniform kinetics.

Concretely, for the triangle `A → B → A + B → A` of `Examples/CycleRateNonMonotone.lean` the source
complexes satisfy `y 0 + y 1 - y 2 = 0`, so realizability demands `κ 0 * κ 1 = κ 2`.  That network
has deficiency `3 - 1 - 2 = 0`, hence is complex-balanced at *every* rate vector, so the obstruction
is not an artefact of choosing non-complex-balanced rates.  What remains available in that case is
the quantitative bound `massAction_cycle_inner_le_kappaSpread`. -/
theorem not_exists_realizing_of_relation {n : ℕ} (y : Fin n → E) (c : Fin n → ℝ) (v : Fin n → ℝ)
    (hrel : ∑ i, c i • y i = 0) (hsum : ∑ i, c i * v i ≠ 0) :
    ¬ ∃ w : E, ∀ i, ⟪w, y i⟫_ℝ = v i := by
  rintro ⟨w, hw⟩
  apply hsum
  have h : ⟪w, ∑ i, c i • y i⟫_ℝ = ∑ i, c i * v i := by
    rw [inner_sum]
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [real_inner_smul_right, hw i]
  rw [hrel, inner_zero_right] at h
  exact h.symm

end MassAction

end CRNT
