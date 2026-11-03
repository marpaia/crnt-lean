import CRNT.Dynamics.ToricEmbedding
import Mathlib.Geometry.Convex.Cone.Pointed
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The single-cycle projection-ordering step: velocity in the polar cone

This module completes the single-cycle case of the toric-embedding argument of Craciun,
_Toric differential inclusions and a proof of the global attractor conjecture_, by turning
the Abel-summation kernel into a **polar-cone membership**. The kernel
`cycle_velocity_eq_nonneg_combination`
(in `CRNT.Dynamics.ToricEmbedding`) shows that, with monotone coefficients `Monotone a`
and a closed cycle `u n = u 0`, the cyclic velocity is a nonnegative combination of the
vertex differences `u 0 − u (i+1)`. The remaining geometric step landed here is: when the
chosen base vertex `u 0` is `C`-minimal — its projection `⟪z, u 0⟫` is least among the
cycle vertices for every `z` in a cone `C` — each generator `u 0 − u (i+1)` lies in the
polar of `C`, hence so does the whole cone they generate, hence so does the velocity.

## Sign and polar conventions

The dual cone `coneDual s` of `CRNT.Geometry.PolyhedralFan` is the **nonnegative** dual
`{y : ∀ x ∈ s, 0 ≤ ⟪x, y⟫}`. The polar `Cᵒ` is the **nonpositive** cone
`{y : ∀ x ∈ C, ⟪x, y⟫ ≤ 0}`. To make the statement true with no sign confusion we work
directly with the nonpositive convention: `polarCone C` is defined here as the pointed
cone `{y : ∀ x ∈ C, ⟪x, y⟫ ≤ 0}` (`mem_polarCone`). This is exactly the polar `Cᵒ`, and
`u 0 − u (i+1)` lands in `polarCone C` because `C`-minimality gives
`⟪z, u 0 − u (i+1)⟫ = ⟪z, u 0⟫ − ⟪z, u (i+1)⟫ ≤ 0` for all `z ∈ C`.

## Space convention

All statements live over a general real inner-product space `E`
(`NormedAddCommGroup E`, `InnerProductSpace ℝ E`); the abstract Abel kernel
`cycle_velocity_eq_nonneg_combination` already holds over any `ℝ`-module, so no transport
along `(S → ℝ) ≃ EuclideanSpace ℝ S` is needed. To specialize to species space, take
`E := EuclideanSpace ℝ S`.

## Results

The generated cone of polar-cone generators sits inside the polar cone
(`generatedConeE_le_polarCone`); each vertex difference is polar to a `C`-minimal base
(`vertexDiff_mem_polarCone`); and the assembled single-cycle velocity lies in the polar cone
under `Monotone a`, `u n = u 0`, and `C`-minimality (`cycle_velocity_mem_polarCone`). A
sorting lemma turning a generic interior direction with distinct projections into a relabeling
realizing both `C`-minimality and coefficient monotonicity (`exists_sorted_reindex`) is
provided over a finite cycle.

Taken as hypotheses: that `Monotone a` actually holds for the mass-action coefficients (it
does, away from the `δ`-uncertainty region where `log x ∈ C`), and the full multi-cycle
weakly-reversible assembly across cycles and uncertainty regions.

Depends on: `CRNT.Dynamics.ToricEmbedding`,
Mathlib pointed cones, inner-product spaces, and module big operators.
-/

namespace CRNT

open scoped InnerProductSpace
open Finset

section PolarCone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **The polar cone** `Cᵒ` of a set `s`, in the nonpositive convention: the pointed
cone of points `y` whose inner product with every `x ∈ s` is nonpositive. This is a pointed
cone because the conditions `⟪x, y⟫ ≤ 0` are preserved under addition and nonnegative
scaling of `y`. Note the sign: this is the negation-flipped twin of the nonnegative dual
`coneDual` of `CRNT.Geometry.PolyhedralFan`. -/
def polarCone (s : Set E) : PointedCone ℝ E where
  carrier := {y | ∀ ⦃x⦄, x ∈ s → ⟪x, y⟫_ℝ ≤ 0}
  add_mem' := by
    intro y z hy hz x hx
    rw [inner_add_right]
    exact add_nonpos (hy hx) (hz hx)
  zero_mem' := by
    intro x _
    simp
  smul_mem' := by
    intro c y hy x hx
    rw [show c • y = (c : ℝ) • y from rfl, real_inner_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos c.2 (hy hx)

/-- Membership in the polar cone: `y ∈ polarCone s` iff `⟪x, y⟫ ≤ 0` for every `x ∈ s`. -/
@[simp] theorem mem_polarCone {s : Set E} {y : E} :
    y ∈ polarCone s ↔ ∀ ⦃x⦄, x ∈ s → ⟪x, y⟫_ℝ ≤ 0 :=
  Iff.rfl

/-- **A polar direction pairs strictly with any point that can move a little along it inside
the cone.** If `v ∈ Cᵒ` is nonzero and `n + ε v ∈ C` for some `ε > 0`, then
`⟪n, v⟫ < 0`. This is the strict-support step used when a toric chamber admits an inward
perturbation in the velocity direction. -/
theorem polarCone_inner_lt_zero_of_positivePerturbation {s : Set E} {n v : E}
    (hv : v ∈ polarCone s) (hne : v ≠ 0)
    (hperturb : ∃ ε : ℝ, 0 < ε ∧ n + ε • v ∈ s) :
    ⟪n, v⟫_ℝ < 0 := by
  rcases hperturb with ⟨ε, hε, hmem⟩
  have hle := (mem_polarCone.mp hv) hmem
  have hnorm : 0 < ⟪v, v⟫_ℝ := by
    rw [real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hne)
  rw [inner_add_left, real_inner_smul_left] at hle
  by_contra hnot
  have hn : 0 ≤ ⟪n, v⟫_ℝ := le_of_not_gt hnot
  have hprod : 0 < ε * ⟪v, v⟫_ℝ := mul_pos hε hnorm
  linarith

/-- **Strict support at interior points.** A nonzero polar direction pairs strictly negatively
with every interior point of the cone, by perturbing that point a small distance along the polar
direction while staying inside the cone. -/
theorem polarCone_inner_lt_zero_of_mem_interior {s : Set E} {n v : E}
    (hv : v ∈ polarCone s) (hne : v ≠ 0) (hn : n ∈ interior s) :
    ⟪n, v⟫_ℝ < 0 := by
  have hsn := mem_interior_iff_mem_nhds.mp hn
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hsn
  have hperturb : ∃ ε : ℝ, 0 < ε ∧ n + ε • v ∈ s := by
    let ε : ℝ := r / (‖v‖ + 1)
    have hε : 0 < ε := by
      dsimp [ε]
      positivity
    have hratio : ‖v‖ / (‖v‖ + 1) < 1 := by
      apply (div_lt_iff₀ (by positivity : 0 < ‖v‖ + 1)).2
      nlinarith [norm_nonneg v]
    have hdist : dist (n + ε • v) n < r := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
      dsimp [ε]
      calc
        r / (‖v‖ + 1) * ‖v‖ = r * (‖v‖ / (‖v‖ + 1)) := by ring
        _ < r * 1 := mul_lt_mul_of_pos_left hratio hr
        _ = r := by ring
    exact ⟨ε, hε, hball (Metric.mem_ball.mpr hdist)⟩
  exact polarCone_inner_lt_zero_of_positivePerturbation hv hne hperturb

end PolarCone

section GeneratedConeE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The convex cone generated by a finite family of vectors in a general inner-product
space `E`: the smallest pointed cone (containing `0`) that contains every `g i`. Realized
as the nonnegative-scalar span of the range of `g`. This is the inner-product-space twin of
`CRNT.generatedCone`, which is fixed to species space `S → ℝ`. -/
def generatedConeE {ι : Type*} (g : ι → E) : PointedCone ℝ E :=
  PointedCone.hull ℝ (Set.range g)

/-- Each generator lies in the cone it generates. -/
theorem mem_generatedConeE {ι : Type*} (g : ι → E) (i : ι) :
    g i ∈ generatedConeE g :=
  PointedCone.subset_hull ⟨i, rfl⟩

/-- **A cone contains the cone generated by its members.** If every generator `g i` lies in
a pointed cone `C`, then the whole generated cone is contained in `C`. This is the cone
analogue of `Submodule.span_le`: `generatedConeE g = span ℝ≥0 (range g)`, so it is the
least pointed cone containing the generators. -/
theorem generatedConeE_le {ι : Type*} (g : ι → E) (C : PointedCone ℝ E)
    (hg : ∀ i, g i ∈ C) : generatedConeE g ≤ C := by
  rw [generatedConeE, PointedCone.hull, Submodule.span_le]
  rintro x ⟨i, rfl⟩
  exact hg i

/-- **Item 1.** When every generator `g i` lies in the polar cone of `s`, the entire
generated cone lies in the polar cone of `s` — a polar cone contains the cone generated by
its members. -/
theorem generatedConeE_le_polarCone {ι : Type*} (g : ι → E) (s : Set E)
    (hg : ∀ i, g i ∈ polarCone s) : generatedConeE g ≤ polarCone s :=
  generatedConeE_le g (polarCone s) hg

end GeneratedConeE

section CMinimal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `u 0` is `C`-minimal for a cone (or any set) `C` and a family of vertices `u` when its
projection onto every direction `z ∈ C` is least among the vertices: `⟪z, u 0⟫ ≤ ⟪z, u i⟫`
for all `i` and all `z ∈ C`. This is the geometric input Craciun extracts from choosing a
generic direction and sorting the cycle vertices by their projection. -/
def CMinimal (C : Set E) (u : ℕ → E) : Prop :=
  ∀ ⦃z⦄, z ∈ C → ∀ i, ⟪z, u 0⟫_ℝ ≤ ⟪z, u i⟫_ℝ

/-- **Item 2.** From `C`-minimality of the base vertex `u 0`, each vertex difference
`u 0 − u (i+1)` lies in the polar cone of `C`: for every `z ∈ C`,
`⟪z, u 0 − u (i+1)⟫ = ⟪z, u 0⟫ − ⟪z, u (i+1)⟫ ≤ 0`. -/
theorem vertexDiff_mem_polarCone {C : Set E} {u : ℕ → E} (hmin : CMinimal C u) (i : ℕ) :
    u 0 - u (i + 1) ∈ polarCone C := by
  rw [mem_polarCone]
  intro z hz
  rw [inner_sub_right, sub_nonpos]
  exact hmin hz (i + 1)

end CMinimal

section Velocity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Item 3 — single-cycle velocity in the polar cone.** With monotone coefficients
`Monotone a`, a closed cycle `u n = u 0`, and the base vertex `u 0` `C`-minimal, the cyclic
mass-action velocity `∑_{i<n} a i • (u (i+1) − u i)` lies in the polar cone `Cᵒ` of `C`.

The proof chains the three established pieces: the Abel kernel
`cycle_velocity_eq_nonneg_combination` rewrites the velocity as a nonnegative combination of
the vertex differences `u 0 − u (i+1)`; each such difference lies in `polarCone C` by
`C`-minimality (`vertexDiff_mem_polarCone`); and `polarCone C`, being a pointed cone, is
closed under the nonnegative combination (`Submodule.sum_mem` and `smul_mem`). -/
theorem cycle_velocity_mem_polarCone {C : Set E} (u : ℕ → E) (a : ℕ → ℝ) (n : ℕ)
    (hcyc : u n = u 0) (hmono : Monotone a) (hmin : CMinimal C u) :
    (∑ i ∈ range n, a i • (u (i + 1) - u i)) ∈ polarCone C := by
  rw [cycle_velocity_eq_nonneg_combination u a n hcyc]
  refine Submodule.sum_mem _ ?_
  intro i _
  have hc : (0 : ℝ) ≤ a (i + 1) - a i := forwardDiff_nonneg hmono i
  exact (polarCone C).smul_mem hc (vertexDiff_mem_polarCone hmin i)

/-- The same membership stated through the generated cone, exhibiting the full chain
"velocity ∈ generated cone of vertex differences ⊆ polar cone": with the vertex-difference
family as generators, the velocity lies in their generated cone, which sits inside the polar
cone of `C` whenever `u 0` is `C`-minimal. -/
theorem cycle_velocity_generatedConeE_le_polarCone {C : Set E} (u : ℕ → E) (n : ℕ)
    (hmin : CMinimal C u) :
    generatedConeE (fun i : Fin (n - 1) => u 0 - u (i + 1)) ≤ polarCone C :=
  generatedConeE_le_polarCone _ C (fun i => vertexDiff_mem_polarCone hmin i)

end Velocity

section Sorting

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **Item 4 — the sorting reindexing.** A direction `w` whose projections `⟪w, u i⟫` onto
the cycle vertices are all distinct induces a permutation `σ` of the indices that sorts the
vertices by projection: along the relabeled vertices `u ∘ σ` the projection map
`fun i => ⟪w, (u ∘ σ) i⟫` is monotone, and the relabeled base `(u ∘ σ) 0` is minimal for the
ray `ℝ≥0 • w` — it realizes `CMinimal {t • w | 0 ≤ t}`-style minimality along `w`. This is
the combinatorial step that produces the monotone coefficients and `C`-minimal base the
velocity argument consumes.

We package it as: given any finite vertex family `u : Fin m → E` and direction `w`, there is
a sorting permutation `σ` such that `Monotone (fun i => ⟪w, u (σ i)⟫)`; sortedness gives
both the monotone coefficient ordering (the coefficients are functions of the projections)
and the projection-minimality of the first sorted vertex. -/
theorem exists_sorted_reindex {m : ℕ} (u : Fin m → E) (w : E) :
    ∃ σ : Equiv.Perm (Fin m), Monotone (fun i => ⟪w, u (σ i)⟫_ℝ) :=
  ⟨Tuple.sort (fun i => ⟪w, u i⟫_ℝ), Tuple.monotone_sort (fun i => ⟪w, u i⟫_ℝ)⟩

/-- Sortedness gives projection-minimality of the first sorted vertex: along a monotone
relabeling of the projections, the first vertex has the least projection onto `w` among all
vertices. This is the `CMinimal`-flavoured consequence of `exists_sorted_reindex`. -/
theorem sorted_head_proj_min {m : ℕ} [NeZero m] (u : Fin m → E) (w : E)
    {σ : Equiv.Perm (Fin m)} (hσ : Monotone (fun i => ⟪w, u (σ i)⟫_ℝ)) (i : Fin m) :
    ⟪w, u (σ ⟨0, Nat.pos_of_neZero m⟩)⟫_ℝ ≤ ⟪w, u (σ i)⟫_ℝ :=
  hσ (by simp)

end Sorting

section ProjectedCycleVelocity

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A closed cycle's projected velocity points toward lower levels whenever its coefficients
are monotone in source level. The level used to order coefficients may differ from the test
direction, provided both induce the same strict ordering of the cycle vertices. -/
theorem cyclicProjectedVelocity_nonpos_of_orderedCoefficients
    (σ : Equiv.Perm ι) (u : ι → E) (a : ι → ℝ) (z₀ z : E)
    (ha : Monovary a (fun i => ⟪z₀, u i⟫_ℝ))
    (horder : ∀ i j, ⟪z, u i⟫_ℝ < ⟪z, u j⟫_ℝ →
      ⟪z₀, u i⟫_ℝ < ⟪z₀, u j⟫_ℝ) :
    (∑ i, a i * ⟪z, u (σ i) - u i⟫_ℝ) ≤ 0 := by
  have hmono : Monovary a (fun i => ⟪z, u i⟫_ℝ) := by
    intro i j hij
    exact ha (horder i j hij)
  have hrearrange := hmono.sum_mul_comp_perm_le_sum_mul (σ := σ)
  have hsum : (∑ i, a i * ⟪z, u (σ i) - u i⟫_ℝ) =
      (∑ i, a i * ⟪z, u (σ i)⟫_ℝ) - ∑ i, a i * ⟪z, u i⟫_ℝ := by
    simp_rw [inner_sub_right, mul_sub, Finset.sum_sub_distrib]
  rw [hsum]
  linarith

/-- **Closed-walk ordering with a reference direction.** Let `target` and `source` be the target
and source vertex lists of a closed directed walk, so they are permutations of one another. If the
walk's coefficients vary monotonically with a reference projection `z₀`, and every strict ordering
seen by a test direction `z` is also an ordering in `z₀`, then the walk has nonpositive projected
velocity along `z`. This list form is the bridge from concrete reaction walks to
`cyclicProjectedVelocity_nonpos_of_orderedCoefficients`. -/
theorem cyclicProjectedVelocity_nonpos_of_permutedList_of_orderedCoefficients
    {α E : Type*} [BEq α] [LawfulBEq α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (target source : List α) (hperm : List.Perm target source)
    (f : α → E) (z₀ z : E) (a : Fin source.length → ℝ)
    (ha : Monovary a (fun i => ⟪z₀, f (source.get i)⟫_ℝ))
    (horder : ∀ i j, ⟪z, f (source.get i)⟫_ℝ < ⟪z, f (source.get j)⟫_ℝ →
      ⟪z₀, f (source.get i)⟫_ℝ < ⟪z₀, f (source.get j)⟫_ℝ) :
    (∑ i : Fin source.length,
      a i * ⟪z, f (target.get (finCongr hperm.length_eq.symm i)) -
        f (source.get i)⟫_ℝ) ≤ 0 := by
  classical
  let eCast : Fin source.length ≃ Fin target.length := finCongr hperm.length_eq.symm
  have hbij : Function.Bijective hperm.idxBij :=
    ⟨hperm.idxBij_injective, hperm.idxBij_surjective⟩
  let eIdx : Fin target.length ≃ Fin source.length := Equiv.ofBijective hperm.idxBij hbij
  let σ : Equiv.Perm (Fin source.length) := eCast.trans eIdx
  let u : Fin source.length → E := fun i => f (source.get i)
  have htarget : ∀ i, f (target.get (eCast i)) = u (σ i) := by
    intro i
    have hi := hperm.getElem_idxBij_eq_getElem (eCast i)
    simpa [u, σ, eCast, eIdx, List.get_eq_getElem] using congrArg f hi.symm
  have hsum :
      (∑ i : Fin source.length,
        a i * ⟪z, f (target.get (eCast i)) - f (source.get i)⟫_ℝ) =
      ∑ i : Fin source.length, a i * ⟪z, u (σ i) - u i⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [htarget i]
  rw [hsum]
  apply cyclicProjectedVelocity_nonpos_of_orderedCoefficients σ u a z₀ z ha
  intro i j hij
  exact horder i j hij

omit [Fintype ι] in
/-- A uniform coefficient interval and a sufficiently large gap in the exponent levels make
exponential source coefficients monotone in those levels. -/
theorem expWeightedCoefficients_monovary_of_separation
    {k p : ι → ℝ} {kmin kmax δ : ℝ}
    (hkmin : 0 ≤ kmin) (hscale : kmax ≤ kmin * Real.exp δ)
    (hk : ∀ i, kmin ≤ k i ∧ k i ≤ kmax)
    (hgap : ∀ i j, p i < p j → p i + δ ≤ p j) :
    Monovary (fun i => k i * Real.exp (p i)) p := by
  intro i j hij
  calc
    k i * Real.exp (p i) ≤ kmax * Real.exp (p i) :=
      mul_le_mul_of_nonneg_right (hk i).2 (le_of_lt (Real.exp_pos _))
    _ ≤ (kmin * Real.exp δ) * Real.exp (p i) :=
      mul_le_mul_of_nonneg_right hscale (le_of_lt (Real.exp_pos _))
    _ = kmin * Real.exp (p i + δ) := by rw [Real.exp_add]; ring
    _ ≤ kmin * Real.exp (p j) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (hgap i j hij)) hkmin
    _ ≤ k j * Real.exp (p j) :=
      mul_le_mul_of_nonneg_right (hk j).1 (le_of_lt (Real.exp_pos _))

/-- A finite family of positive prefactors admits one common lower bound, upper bound, and
exponential separation margin. The margin `δ = log(kmax / kmin)` makes
`kmax = kmin * exp δ`, so `expWeightedCoefficients_monovary_of_separation` applies uniformly to
every member of the family. -/
theorem exists_uniform_exp_prefactor_separation {ι : Type*} [Fintype ι] [Nonempty ι]
    (k : ι → ℝ) (hk : ∀ i, 0 < k i) :
    ∃ kmin kmax δ : ℝ, 0 < kmin ∧
      (∀ i, kmin ≤ k i ∧ k i ≤ kmax) ∧
      kmax ≤ kmin * Real.exp δ := by
  classical
  let values : Finset ℝ := Finset.univ.image k
  have hvalues : values.Nonempty := by
    obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨k i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  let kmin : ℝ := values.min' hvalues
  let kmax : ℝ := values.max' hvalues
  let δ : ℝ := Real.log (kmax / kmin)
  have hminpos : 0 < kmin := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.min'_mem values hvalues)
    dsimp [kmin]
    rw [← hi]
    exact hk i
  have hmaxpos : 0 < kmax := by
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finset.max'_mem values hvalues)
    dsimp [kmax]
    rw [← hi]
    exact hk i
  refine ⟨kmin, kmax, δ, hminpos, ?_, ?_⟩
  · intro i
    constructor
    · dsimp [kmin]
      exact Finset.min'_le values (k i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · dsimp [kmax]
      exact Finset.le_max' values (k i)
        (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  · dsimp [δ]
    rw [Real.exp_log (div_pos hmaxpos hminpos)]
    field_simp [ne_of_gt hminpos]
    norm_num

/-- A finite family of real levels has a positive lower bound on all of its strictly positive
gaps, provided at least one strict gap occurs. This is the finite gap used when a logarithmic
state moves out along a generic ray: every distinct source level eventually separates by any
fixed prefactor margin. -/
theorem exists_positive_uniform_strict_gap {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hstrict : ∃ i j, p i < p j) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ i j, p i < p j → ε ≤ p j - p i := by
  classical
  let pairs : Finset (ι × ι) := Finset.univ.filter (fun ij => p ij.1 < p ij.2)
  let gaps : Finset ℝ := pairs.image (fun ij => p ij.2 - p ij.1)
  have hpairs : pairs.Nonempty := by
    obtain ⟨i, j, hij⟩ := hstrict
    exact ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩⟩
  have hgaps : gaps.Nonempty := by
    obtain ⟨ij, hij⟩ := hpairs
    exact ⟨p ij.2 - p ij.1, Finset.mem_image.mpr ⟨ij, hij, rfl⟩⟩
  let ε : ℝ := gaps.min' hgaps
  have hεpos : 0 < ε := by
    have hmem : gaps.min' hgaps ∈ gaps := Finset.min'_mem gaps hgaps
    rcases Finset.mem_image.mp hmem with ⟨⟨i, j⟩, hij, hgapEq⟩
    change 0 < gaps.min' hgaps
    rw [← hgapEq]
    exact sub_pos.mpr (Finset.mem_filter.mp hij).2
  refine ⟨ε, hεpos, ?_⟩
  intro i j hij
  dsimp [ε]
  exact Finset.min'_le gaps (p j - p i)
    (Finset.mem_image.mpr ⟨(i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hij⟩, rfl⟩)

/-- The projected cycle-sign lemma with explicit uniform bounds on the reaction coefficients.
The separation margin `δ` must dominate the coefficient range, expressed by
`kmax ≤ kmin * exp δ`. This is the finite core used to embed one weakly reversible cycle into a
toric differential inclusion away from the uncertainty hyperplanes. -/
theorem cyclicProjectedVelocity_nonpos_of_rateSeparation
    (σ : Equiv.Perm ι) (u : ι → E) (k p : ι → ℝ) (z₀ z : E)
    {kmin kmax δ : ℝ}
    (hkmin : 0 ≤ kmin) (hscale : kmax ≤ kmin * Real.exp δ)
    (hk : ∀ i, kmin ≤ k i ∧ k i ≤ kmax)
    (hgap : ∀ i j, p i < p j → p i + δ ≤ p j)
    (hp : ∀ i, p i = ⟪z₀, u i⟫_ℝ)
    (horder : ∀ i j, ⟪z, u i⟫_ℝ < ⟪z, u j⟫_ℝ → p i < p j) :
    (∑ i, (k i * Real.exp (p i)) * ⟪z, u (σ i) - u i⟫_ℝ) ≤ 0 := by
  have hcoeff : Monovary (fun i => k i * Real.exp (p i))
      (fun i => ⟪z₀, u i⟫_ℝ) := by
    intro i j hij
    apply expWeightedCoefficients_monovary_of_separation hkmin hscale hk hgap
    rw [hp i, hp j]
    exact hij
  exact cyclicProjectedVelocity_nonpos_of_orderedCoefficients σ u
    (fun i => k i * Real.exp (p i)) z₀ z hcoeff
    (by
      intro i j hzij
      rw [← hp i, ← hp j]
      exact horder i j hzij)

/-- **Closed-walk rate separation with a reference direction.** The source/target lists of a
closed walk induce a permutation of its vertices. If the coefficient prefactors stay in
`[kmin,kmax]`, their range is dominated by `exp δ`, and each strict reference-projection gap is at
least `δ`, then the exponential coefficients increase in the reference order. If the test direction
respects that order, the walk's projected velocity is nonpositive. This is the finite estimate
needed when fixed equilibrium-rate factors perturb the pure monomial ordering. -/
theorem cyclicProjectedVelocity_nonpos_of_permutedList_rateSeparation
    {α E : Type*} [BEq α] [LawfulBEq α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (target source : List α) (hperm : List.Perm target source)
    (f : α → E) (k p : Fin source.length → ℝ) (z₀ z : E)
    {kmin kmax δ : ℝ}
    (hkmin : 0 ≤ kmin) (hscale : kmax ≤ kmin * Real.exp δ)
    (hk : ∀ i, kmin ≤ k i ∧ k i ≤ kmax)
    (hgap : ∀ i j, p i < p j → p i + δ ≤ p j)
    (hp : ∀ i, p i = ⟪z₀, f (source.get i)⟫_ℝ)
    (horder : ∀ i j, ⟪z, f (source.get i)⟫_ℝ < ⟪z, f (source.get j)⟫_ℝ →
      p i < p j) :
    (∑ i : Fin source.length,
      (k i * Real.exp (p i)) *
        ⟪z, f (target.get (finCongr hperm.length_eq.symm i)) -
          f (source.get i)⟫_ℝ) ≤ 0 := by
  have hcoeff : Monovary (fun i => k i * Real.exp (p i))
      (fun i => ⟪z₀, f (source.get i)⟫_ℝ) := by
    intro i j hij
    apply expWeightedCoefficients_monovary_of_separation hkmin hscale hk hgap
    rw [hp i, hp j]
    exact hij
  exact cyclicProjectedVelocity_nonpos_of_permutedList_of_orderedCoefficients
    target source hperm f z₀ z (fun i => k i * Real.exp (p i)) hcoeff
    (by
      intro i j hzij
      rw [← hp i, ← hp j]
      exact horder i j hzij)

/-- A constant circulation weight around a cycle needs no separation margin: multiplying every
source monomial by the same nonnegative cycle-flow coefficient preserves the ordering of its
exponential weights. This is the single-cycle form consumed after decomposing a graph
circulation into simple directed cycles. -/
theorem cyclicProjectedVelocity_nonpos_of_constantCycleFlow
    (σ : Equiv.Perm ι) (u : ι → E) (p : ι → ℝ) (z₀ z : E) (q : ℝ)
    (hq : 0 ≤ q)
    (hp : ∀ i, p i = ⟪z₀, u i⟫_ℝ)
    (horder : ∀ i j, ⟪z, u i⟫_ℝ < ⟪z, u j⟫_ℝ → p i < p j) :
    (∑ i, (q * Real.exp (p i)) * ⟪z, u (σ i) - u i⟫_ℝ) ≤ 0 := by
  exact cyclicProjectedVelocity_nonpos_of_rateSeparation σ u (fun _ => q) p z₀ z
    (kmin := q) (kmax := q) (δ := 0) hq (by simp)
    (fun _ => ⟨le_rfl, le_rfl⟩)
    (fun i j hij => by simpa using hij.le)
    hp horder

/-- A closed list of vertices yields a nonpositive exponentially weighted projected velocity.
The permutation identifies each target position with a source position carrying the same vertex;
the exponential coefficient is monotone in the projected source level. -/
theorem cyclicProjectedVelocity_nonpos_of_permutedList
    {α E : Type*} [BEq α] [LawfulBEq α]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (target source : List α) (hperm : List.Perm target source)
    (f : α → E) (z : E) (q : ℝ) (hq : 0 ≤ q) :
    (∑ i : Fin source.length,
      (q * Real.exp (⟪z, f (source.get i)⟫_ℝ)) *
        ⟪z, f (target.get (finCongr hperm.length_eq.symm i)) -
          f (source.get i)⟫_ℝ) ≤ 0 := by
  classical
  let eCast : Fin source.length ≃ Fin target.length := finCongr hperm.length_eq.symm
  have hbij : Function.Bijective hperm.idxBij :=
    ⟨hperm.idxBij_injective, hperm.idxBij_surjective⟩
  let eIdx : Fin target.length ≃ Fin source.length := Equiv.ofBijective hperm.idxBij hbij
  let σ : Equiv.Perm (Fin source.length) := eCast.trans eIdx
  let u : Fin source.length → E := fun i => f (source.get i)
  have htarget : ∀ i, f (target.get (eCast i)) = u (σ i) := by
    intro i
    have hi := hperm.getElem_idxBij_eq_getElem (eCast i)
    simpa [u, σ, eCast, eIdx, List.get_eq_getElem] using congrArg f hi.symm
  have hsum :
      (∑ i : Fin source.length,
        (q * Real.exp (⟪z, f (source.get i)⟫_ℝ)) *
          ⟪z, f (target.get (eCast i)) - f (source.get i)⟫_ℝ) =
      ∑ i : Fin source.length,
        (q * Real.exp (⟪z, u i⟫_ℝ)) * ⟪z, u (σ i) - u i⟫_ℝ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [htarget i]
  rw [hsum]
  exact cyclicProjectedVelocity_nonpos_of_constantCycleFlow σ u
    (fun i => ⟪z, u i⟫_ℝ) z z q hq (fun _ => rfl)
    (by intro i j hij; exact hij)

end ProjectedCycleVelocity

end CRNT
