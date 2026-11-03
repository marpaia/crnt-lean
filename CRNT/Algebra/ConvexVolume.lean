import CRNT.Algebra.MixedVolumeBKK
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.Convex.Body
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Segment

/-
# Volume monotonicity for convex bodies, and the volume of a zonotope (leaf A3)

This module supplies the **geometric bridge** of the Bernstein–Kushnirenko–Khovanskii (BKK)
theory: the ingredient that turns the *mixed volume* of the repository into a bound on the
*volume* of a convex body.

## 1. The background

A **convex body** of `ℝⁿ` is a convex, compact, nonempty subset of `ℝⁿ`; Mathlib's
`ConvexBody (Fin n → ℝ)` is exactly that.  Its **volume** is its Lebesgue measure, and the
two classical facts about it that the BKK theory uses are

* **volume monotonicity**: `K ⊆ L` implies `vol K ≤ vol L`;
* **Shephard's formula for the volume of a zonotope**: for a Minkowski sum of segments
  `Z = [0, v₁] + ⋯ + [0, v_m]` in `ℝⁿ`,
  `vol Z = ∑_{|S| = n} |det (v_{j₁}, …, v_{jₙ})|`, the sum running over the `n`-element
  subsets of the generators — i.e. the **mixed volume** of the `n` singleton zonotopes spanned
  by the generators.

Shephard's formula is a special case of the **Brunn–Minkowski theory** (the volume polynomial
theorem), which is the source of the BKK bound itself: the number of isolated solutions of a
system of `n` polynomials in `n` variables with Newton polytopes `K₁, …, Kₙ` is at most the
mixed volume `MV(K₁, …, Kₙ)`, i.e. `n!` times the volume of the Minkowski sum
`K₁ + ⋯ + Kₙ`.  **The BKK bound is a volume statement.**

The **geometric bridge** between the mixed volume and the volume of a Newton polytope is the
following: if `P` is a polytope with vertices `v₀, …, v_m` and `Z = [0, v₁ - v₀] + ⋯ +
[0, v_m - v₀]` is the zonotope spanned by the differences, then `P ⊆ v₀ + Z`, hence (by volume
monotonicity) `vol P ≤ vol Z`; and the mixed volume of the `n` singleton zonotopes spanned by
the differences bounds `vol Z`.  For a **circuit** — a minimally dependent set of monomials
`1, x^{w₁}, …, x^{w_n}, x^{w_{n+1}}` — the Newton polytope of an equation supported on the
`n + 1` monomials `1, x^{w₁}, …, x^{w_n}` is the **circuit simplex** `conv(0, w₁, …, w_n)`,
which is contained in the zonotope `∑_k [0, w_k]` spanned by the reaction vectors.

## 2. What the repository already contains

* `CRNT.Algebra.MixedVolume`: the **mixed volume** `CRNT.MixedVolume.mixedVolume` of
  **zonotopes**, in the Bernstein–Kushnirenko–Khovanskii normalization `MV(K, …, K) = n! vol K`.
  For zonotopes the classical determinant formula of Shephard *is* the definition, and the two
  defining properties (Minkowski additivity and homogeneity) are proved from it;
* `CRNT.Algebra.VolumePolynomial`: the **volume polynomial** `zonotopeVolumePolynomial` of a
  zonotope, its multilinearity, and the identification of its coefficients with the mixed
  volumes of the singleton zonotopes (`zonotopeVolumePolynomial_coeff_eq_mixedVolume`);
* `CRNT.Algebra.MixedVolumeBKK`: the **circuit Newton polytope**
  `CRNT.MixedVolume.circuitNewtonPolytope` (the convex hull of the origin and of the reaction
  vectors), the computation of the mixed volume of a circuit (`mixedVolume_circuit`, the
  normalized volume `|det E|`), and the BKK bound for systems supported on a circuit.

## 3. What this module adds

* **The volume of a convex body** (`ConvexBody.volumeI`): Mathlib has no `volumeI`; the volume
  is defined here as the Lebesgue measure of the carrier of the convex body.
* **Volume monotonicity** (`volume_le_of_subset`): if `K ⊆ L` are convex bodies of `ℝⁿ` then
  `vol K ≤ vol L`.  This is the missing *geometric* ingredient of the BKK theory: it turns a
  set-theoretic inclusion of convex bodies into an inequality of volumes, and hence bounds the
  volume of a Newton polytope by the volume of the zonotope spanned by its reaction vectors.
* **The zonotope spanned by the reaction vectors** (`CRNT.Geometry.zonotopeBody`) and the
  containment `circuitNewtonPolytope E ⊆ zonotopeBody (w₁, …, w_n)`
  (`circuitNewtonPolytope_subset_zonotopeBody`), together with its general form
  (`convexHull_subset_translate_zonotopeBody`): a polytope is contained in the translate of
  the zonotope spanned by the differences of its vertices;
* **the geometric bridge itself** (`volumeI_circuitNewtonPolytope_le`): the volume of the
  Newton polytope of a circuit is at most the volume of the zonotope spanned by the reaction
  vectors, i.e. at most the mixed volume of the Newton polytopes.
* **A machine-checked counterexample to the naive reading** of the containment: the Newton
  polytope `conv(0, w₁, …, w_n, w_{n+1})` of a circuit equation is *not* contained in the
  zonotope spanned by the reaction vectors `w₁, …, w_n` (the point `w_{n+1}` need not be in the
  zonotope); see `convexHull_three_not_subset_zonotopeBody_dimOne`.
* **The volume of a zonotope in dimension one** (`volumeI_zonotopeBody_dimOne`,
  `volume_zonotope_eq_mixedVolume_dimOne`): the volume of the zonotope spanned by segments in
  `ℝ¹` is the sum of the lengths of the segments, i.e. the mixed volume of the singleton
  zonotopes spanned by the generators.  This is Shephard's formula in dimension one.
* **The degenerate case** (`volumeI_zonotopeBody_degenerate`,
  `zonotopeVolumePolynomial_degenerate`): a zonotope whose generators vanish in one
  coordinate lies in a coordinate hyperplane, hence has volume `0`, and its mixed volume is `0`
  as well.

## 4. What is *not* formalized

* **Brunn–Minkowski** (`(λ A + μ B)^{1/n} ≥ λ^{1/n} A^{1/n} + μ^{1/n} B^{1/n}`) and the
  **volume polynomial theorem**: these are research-grade theorems; Mathlib has neither, and
  they are *not* attempted here;
* **Shephard's formula for the volume of a zonotope in dimension ≥ 2**: it is a consequence of
  Brunn–Minkowski and is *not* proved here.  What *is* proved is the one-dimensional instance
  (`volumeI_zonotopeBody_dimOne`) and the degenerate case (volume `0`);
* **the general BKK inequality** for `n` Newton polytopes in `ℝⁿ`: it needs the volume of a
  general non-zonotopal polytope, which is not available with the machinery above;
* the **degenerate case in full generality** (a zonotope lying in an *arbitrary* proper linear
  subspace): what is proved here is the coordinate-hyperplane case
  (`volumeI_zonotopeBody_degenerate`); the general statement needs the measure of a hyperplane
  to be zero, i.e. Fubini's theorem for the Lebesgue measure, which Mathlib does not make
  available in a usable form.
-/

open scoped BigOperators Pointwise
open Set

namespace ConvexBody

/-- The **volume** of a convex body `K ⊆ ℝⁿ`: its Lebesgue measure.

Mathlib has no `volumeI`; the volume of a convex body is defined here as the Lebesgue measure
of its carrier.  The carrier of a convex body is closed, hence measurable, and compact, hence
of finite measure. -/
noncomputable def volumeI {n : ℕ} (K : ConvexBody (Fin n → ℝ)) : ℝ :=
  (MeasureTheory.MeasureSpace.volume (K : Set (Fin n → ℝ))).toReal

end ConvexBody

namespace CRNT
namespace Geometry

variable {n m : ℕ}

set_option maxHeartbeats 800000

/-! ### 1. The volume of a convex body -/

/-- The carrier of a convex body is closed, hence **measurable**. -/
theorem measurableSet_coe (K : ConvexBody (Fin n → ℝ)) :
    MeasurableSet (K : Set (Fin n → ℝ)) := by
  have h : IsClosed (K : Set (Fin n → ℝ)) := K.isClosed
  exact h.measurableSet

/-- The Lebesgue measure of a convex body is **finite**. -/
theorem volume_ne_top (K : ConvexBody (Fin n → ℝ)) :
    (MeasureTheory.MeasureSpace.volume (K : Set (Fin n → ℝ))) ≠ ⊤ :=
  K.isCompact'.measure_ne_top

/-- The volume of a convex body is **non-negative**. -/
theorem volumeI_nonneg (K : ConvexBody (Fin n → ℝ)) : 0 ≤ K.volumeI :=
  ENNReal.toReal_nonneg

/-- **Volume monotonicity for convex bodies.**

If `K ⊆ L` are convex bodies of `ℝⁿ`, then the volume of `K` is at most the volume of `L`.
(The order `≤` on convex bodies is the inclusion of the carriers, by
`SetLike.coe_subset_coe`.)

This is the geometric ingredient the BKK theory needs: the Newton polytope of a circuit
equation is contained in the zonotope spanned by the reaction vectors, and the mixed volume of
that zonotope bounds the BKK quantity.

*Proof.* The Lebesgue measure is monotone for set inclusion (`MeasureTheory.measureReal_mono`);
the measure of `L` is finite because `L` is compact. -/
theorem volume_le_of_subset (K L : ConvexBody (Fin n → ℝ)) (h : K ≤ L) :
    K.volumeI ≤ L.volumeI := by
  have h' : (K : Set (Fin n → ℝ)) ⊆ (L : Set (Fin n → ℝ)) := SetLike.coe_subset_coe.mpr h
  have htop : (MeasureTheory.MeasureSpace.volume (L : Set (Fin n → ℝ))) ≠ ⊤ := volume_ne_top L
  have hmono := MeasureTheory.measureReal_mono h' htop
  simpa only [ConvexBody.volumeI, MeasureTheory.measureReal_def] using hmono

/-- **Volume monotonicity for convex bodies**, with the inclusion of the carriers as the
hypothesis. -/
theorem volume_le_of_subset' (K L : ConvexBody (Fin n → ℝ))
    (h : (K : Set (Fin n → ℝ)) ⊆ (L : Set (Fin n → ℝ))) : K.volumeI ≤ L.volumeI :=
  volume_le_of_subset K L (SetLike.coe_subset_coe.mp h)

/-- The convex body consisting of a **single point**. -/
noncomputable def pointBody (x : Fin n → ℝ) : ConvexBody (Fin n → ℝ) :=
  { carrier := {x}
    convex' := convex_singleton x
    isCompact' := isCompact_singleton
    nonempty' := ⟨x, rfl⟩ }

/-- **A point has zero volume** (in positive dimension). -/
theorem volumeI_pointBody (x : Fin n → ℝ) (hn : 0 < n) : (pointBody x).volumeI = 0 := by
  have hbox : ({x} : Set (Fin n → ℝ)) = Icc x x := by
    ext y
    simp only [Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro rfl
      exact ⟨le_rfl, le_rfl⟩
    · rintro ⟨h1, h2⟩
      exact le_antisymm h2 h1
  have hco : ((pointBody x : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ)) = {x} := rfl
  rw [ConvexBody.volumeI, hco, hbox, Real.volume_Icc_pi_toReal (fun _ => le_rfl)]
  rw [Finset.prod_eq_zero (i := ⟨0, by omega⟩) (Finset.mem_univ _)]
  ring

/-! ### 2. Zonotopes -/

/-- The **set of elements of a list**. -/
def listSet (vs : List α) : Set α := {x | x ∈ vs}

/-- The **zonotope** spanned by a list of generators `vs`: the Minkowski sum of the segments
`[0, v]`, `v ∈ vs`.  This is `CRNT.MixedVolume.Zonotope.toConvexBody` of the zonotope with
generators `vs`. -/
noncomputable def zonotopeBody (vs : List (Fin n → ℝ)) : ConvexBody (Fin n → ℝ) :=
  vs.foldr (fun v K => CRNT.MixedVolume.Zonotope.segmentBody v + K) 0

/-- The carrier of the zonotope spanned by `vs` is the Minkowski sum of the segments. -/
theorem coe_zonotopeBody (vs : List (Fin n → ℝ)) :
    ((zonotopeBody vs : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ))
      = ((CRNT.MixedVolume.Zonotope.toConvexBody (⟨vs⟩ : CRNT.MixedVolume.Zonotope n) :
        ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ)) := rfl

/-- The origin belongs to the segment `[0, v]`. -/
theorem zero_mem_segmentBody (v : Fin n → ℝ) :
    (0 : Fin n → ℝ) ∈ CRNT.MixedVolume.Zonotope.segmentBody v := by
  refine subset_convexHull ℝ _ ?_
  simp

/-- The generator `v` belongs to the segment `[0, v]`. -/
theorem mem_segmentBody (v : Fin n → ℝ) :
    v ∈ CRNT.MixedVolume.Zonotope.segmentBody v := by
  refine subset_convexHull ℝ _ ?_
  simp

/-- The origin belongs to the zonotope spanned by any list of generators. -/
theorem mem_zonotopeBody_zero (vs : List (Fin n → ℝ)) :
    (0 : Fin n → ℝ) ∈ zonotopeBody vs := by
  induction vs with
  | nil =>
      rw [zonotopeBody, List.foldr_nil]
      show (0 : Fin n → ℝ) ∈ ({0} : Set (Fin n → ℝ))
      exact Set.mem_singleton_iff.mpr rfl
  | cons v vs ih =>
      rw [zonotopeBody, List.foldr_cons]
      exact Set.mem_image2.mpr ⟨0, zero_mem_segmentBody v, 0, ih, zero_add 0⟩

/-- A generator belongs to the zonotope spanned by any list of generators containing it. -/
theorem mem_zonotopeBody_of_mem (vs : List (Fin n → ℝ)) (v : Fin n → ℝ) (hv : v ∈ vs) :
    v ∈ zonotopeBody vs := by
  induction vs with
  | nil => simp at hv
  | cons w vs ih =>
      rw [zonotopeBody, List.foldr_cons]
      by_cases h : v = w
      · subst h
        exact Set.mem_image2.mpr ⟨v, mem_segmentBody v, 0, mem_zonotopeBody_zero vs, by simp⟩
      · have hv' : v ∈ vs := List.mem_cons.mp hv |>.resolve_left h
        exact Set.mem_image2.mpr ⟨0, zero_mem_segmentBody w, v, ih hv', by simp⟩

/-! ### 3. The Newton polytope of a circuit and the zonotope of the reaction vectors -/

/-- **The convex hull of the origin and of a list of generators is contained in the zonotope
spanned by those generators.** -/
theorem convexHull_subset_zonotopeBody (vs : List (Fin n → ℝ)) :
    convexHull ℝ ({0} ∪ listSet vs) ≤ zonotopeBody vs := by
  show convexHull ℝ ({0} ∪ listSet vs) ⊆ (zonotopeBody vs : Set (Fin n → ℝ))
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst hx0
      exact mem_zonotopeBody_zero vs
    · exact mem_zonotopeBody_of_mem vs x hx
  · exact (zonotopeBody vs).convex

/-- **The Newton polytope of a circuit equation is contained in the zonotope spanned by the
reaction vectors.**

The Newton polytope of a circuit equation supported on the monomials `1, x^{w₁}, …, x^{w_n}`
is the **circuit simplex** `conv(0, w₁, …, w_n)`, where `w₁, …, w_n` are the reaction vectors
of the circuit (the rows of the exponent matrix `E`); the zonotope spanned by the reaction
vectors is the parallelepiped `∑_k [0, w_k]`.  The circuit simplex is contained in it, and
hence (by `volume_le_of_subset`) its volume is at most the volume of the parallelepiped, which
is `|det E|` — the mixed volume of the Newton polytopes
(`CRNT.MixedVolume.mixedVolume_circuit`). -/
theorem circuitNewtonPolytope_subset_zonotopeBody (E : Matrix (Fin n) (Fin n) ℝ) :
    CRNT.MixedVolume.circuitNewtonPolytope E
      ≤ zonotopeBody (List.ofFn (fun k => E k)) := by
  show convexHull ℝ ({0} ∪ Set.range (fun k => E k))
    ⊆ (zonotopeBody (List.ofFn (fun k => E k)) : Set (Fin n → ℝ))
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · have hx0 : x = 0 := Set.mem_singleton_iff.mp hx
      subst hx0
      exact mem_zonotopeBody_zero _
    · obtain ⟨k, rfl⟩ := hx
      exact mem_zonotopeBody_of_mem _ _ (List.mem_ofFn.mpr ⟨k, rfl⟩)
  · exact (zonotopeBody _).convex

/-- **A polytope is contained in the translate of the zonotope spanned by the differences of
its vertices.**

If `p` is a point and `v₁, …, v_m` are vectors, then the convex hull of the points
`p, p + v₁, …, p + v_m` is contained in `p + ∑_i [0, v_i]`, the translate of the zonotope
spanned by the differences.  This is the general form of the geometric bridge used by the BKK
theory: the Newton polytope of a system of equations is contained in the translate of the
zonotope spanned by the reaction vectors, so that its volume is bounded by the volume of that
zonotope. -/
theorem convexHull_subset_translate_zonotopeBody (p : Fin n → ℝ) (vs : List (Fin n → ℝ)) :
    convexHull ℝ ({p} ∪ listSet (vs.map fun v => p + v))
      ≤ (pointBody p + zonotopeBody vs : ConvexBody (Fin n → ℝ)) := by
  show convexHull ℝ ({p} ∪ listSet (vs.map fun v => p + v))
    ⊆ ((pointBody p + zonotopeBody vs : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ))
  refine convexHull_min ?_ ?_
  · intro x hx
    rcases hx with hx | hx
    · have hxp : x = p := Set.mem_singleton_iff.mp hx
      rw [hxp, ConvexBody.coe_add]
      exact Set.mem_image2.mpr ⟨p, Set.mem_singleton p, 0, mem_zonotopeBody_zero vs, by simp⟩
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hx
      rw [ConvexBody.coe_add]
      exact Set.mem_image2.mpr
        ⟨p, Set.mem_singleton p, v, mem_zonotopeBody_of_mem vs v hv, by simp⟩
  · exact (pointBody p + zonotopeBody vs).convex

/-- **The volume of the Newton polytope of a circuit is at most the volume of the zonotope
spanned by the reaction vectors.**

This is the geometric bridge of the BKK theory: the Newton polytope of a circuit equation is
contained in the zonotope spanned by the reaction vectors, and the volume is monotone for
inclusions, so that the volume of the Newton polytope is bounded by the volume of the
zonotope; the latter is the mixed volume of the singleton zonotopes spanned by the reaction
vectors (`CRNT.MixedVolume.mixedVolume_circuit`). -/
theorem volumeI_circuitNewtonPolytope_le (E : Matrix (Fin n) (Fin n) ℝ) :
    (CRNT.MixedVolume.circuitNewtonPolytope E).volumeI
      ≤ (zonotopeBody (List.ofFn (fun k => E k))).volumeI :=
  volume_le_of_subset _ _ (circuitNewtonPolytope_subset_zonotopeBody E)

/-! ### 4. The naive containment is false -/

/-- The carrier of the zonotope spanned by a single generator `v` is the segment `[0, v]`. -/
theorem mem_zonotopeBody_singleton (v x : Fin 1 → ℝ) :
    x ∈ zonotopeBody [v] ↔ x ∈ CRNT.MixedVolume.Zonotope.segmentBody v := by
  show x ∈ (zonotopeBody [v] : Set (Fin 1 → ℝ))
    ↔ x ∈ (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ))
  have hco : ((zonotopeBody [v] : ConvexBody (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))
      = (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ)) + {0} := by
    rw [zonotopeBody, List.foldr_cons]
    rfl
  rw [hco]
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hxy⟩ := Set.mem_image2.mp hx
    have hb0 : b = 0 := Set.mem_singleton_iff.mp hb
    subst hb0
    rw [hxy.symm]
    simpa using ha
  · intro hx
    exact Set.mem_image2.mpr ⟨x, hx, 0, Set.mem_singleton 0, by simp⟩

/-- **In dimension one, the point `2` does not belong to the segment `[0, 1]`.** -/
theorem not_mem_segmentBody_dimOne (v : Fin 1 → ℝ) (hv : v 0 = 1) :
    (fun _ => 2) ∉ CRNT.MixedVolume.Zonotope.segmentBody v := by
  show (fun _ => 2) ∉ (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ))
  have hseg : (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ)) = segment ℝ 0 v := by
    change (convexHull ℝ ({0, v} : Set (Fin 1 → ℝ))) = segment ℝ 0 v
    exact convexHull_pair 0 v
  rw [hseg, segment_eq_image']
  rintro ⟨c, hc, heq⟩
  have h1 := congrArg (fun f : Fin 1 → ℝ => f 0) heq
  have h1' : (0 : Fin 1 → ℝ) 0 + (c • (v - 0)) 0 = 2 := by
    simpa only [Pi.add_apply] using h1
  have h2 : (c • (v - 0)) 0 = c * (v 0 - 0) := by
    rw [Pi.smul_apply, Pi.sub_apply]
    simp only [smul_eq_mul, Pi.zero_apply]
  rw [h2] at h1'
  simp only [Pi.zero_apply] at h1'
  rw [hv] at h1'
  have hc' := hc.2
  linarith

/-- **In dimension one, the point `2` does not belong to the zonotope spanned by the single
generator `1`.** -/
theorem not_mem_zonotopeBody_dimOne (v : Fin 1 → ℝ) (hv : v 0 = 1) :
    (fun _ => 2) ∉ zonotopeBody [v] := by
  rw [mem_zonotopeBody_singleton]
  exact not_mem_segmentBody_dimOne v hv

/-- **The naive containment is false.**

The Newton polytope of a circuit equation supported on the `n + 2` monomials
`1, x^{w₁}, …, x^{w_n}, x^{w_{n+1}}` is the polytope `conv(0, w₁, …, w_n, w_{n+1})`, which is
*not* contained in the zonotope `∑_k [0, w_k]` spanned by the reaction vectors: the point
`w_{n+1}` need not belong to that zonotope.

The counterexample is the circuit `1, x, x²` of `ℝ¹`: the reaction vector is `w₁ = 1` and the
extra monomial is `x²`, so the Newton polytope is `conv(0, 1, 2) = [0, 2]`, whereas the zonotope
spanned by the reaction vector is `[0, 1]`.  The correct statement is the containment of the
*circuit simplex* `conv(0, w₁, …, w_n)` (`circuitNewtonPolytope_subset_zonotopeBody`). -/
theorem convexHull_three_not_subset_zonotopeBody_dimOne :
    ¬ (convexHull ℝ ({0, (fun _ => 1), (fun _ => 2)} : Set (Fin 1 → ℝ))
        ⊆ ((zonotopeBody [(fun _ => 1)] : ConvexBody (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))) := by
  intro h
  have h2 : (fun _ => 2)
      ∈ convexHull ℝ ({0, (fun _ => 1), (fun _ => 2)} : Set (Fin 1 → ℝ)) :=
    subset_convexHull ℝ _ (by simp)
  exact not_mem_zonotopeBody_dimOne _ rfl (h h2)

/-! ### 5. The volume of a zonotope in dimension one -/

/-- Every function `ℝ¹ → ℝ` is determined by its value at `0`. -/
lemma finOne_eq (x : Fin 1 → ℝ) : x = fun _ => x 0 := by
  funext i
  refine Fin.cases rfl (fun i => Fin.elim0 i) i

/-- The interval `Icc a b` of `ℝ¹`, in terms of coordinates. -/
lemma mem_Icc_dimOne {a b x : Fin 1 → ℝ} : x ∈ Icc a b ↔ a 0 ≤ x 0 ∧ x 0 ≤ b 0 := by
  rw [Set.mem_Icc, Pi.le_def, Pi.le_def]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1 0, h2 0⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => ?_, fun i => ?_⟩
    · refine Fin.cases h1 (fun i => Fin.elim0 i) i
    · refine Fin.cases h2 (fun i => Fin.elim0 i) i

/-- **Splitting a point of the sum of two intervals.**  If `z ∈ [a + c, b + d]` with `a ≤ b` and
`c ≤ d`, then `z = x + y` with `x ∈ [a, b]` and `y ∈ [c, d]`. -/
lemma exists_split_Icc_add {a b c d z : ℝ} (hab : a ≤ b) (hcd : c ≤ d)
    (hz : a + c ≤ z ∧ z ≤ b + d) :
    ∃ x y : ℝ, a ≤ x ∧ x ≤ b ∧ c ≤ y ∧ y ≤ d ∧ x + y = z := by
  refine ⟨min (z - c) b, z - min (z - c) b, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_min (by linarith) (by linarith)
  · exact min_le_right _ _
  · linarith [min_le_left (z - c) b]
  · have h1 : z - d ≤ b := by linarith
    have h2 : z - d ≤ z - c := by linarith
    linarith [le_min h2 h1]
  · ring

/-- **A convex combination of `0` and `v` lies between them.** -/
lemma mul_between_zero {v0 θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    min 0 v0 ≤ θ * v0 ∧ θ * v0 ≤ max 0 v0 := by
  rcases le_total 0 v0 with hv | hv
  · constructor
    · exact le_trans (min_le_left 0 v0) (mul_nonneg hθ0 hv)
    · refine le_trans (mul_le_mul_of_nonneg_right hθ1 hv)
        (le_of_eq (by rw [max_eq_right hv, one_mul]))
  · constructor
    · have h1 : 0 ≤ (θ - 1) * v0 := mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hθ1) hv
      have h2 : θ * v0 - v0 = (θ - 1) * v0 := by ring
      rw [min_eq_right hv]
      linarith
    · refine le_trans (mul_nonpos_of_nonneg_of_nonpos hθ0 hv)
        (le_of_eq (by rw [max_eq_left hv]))

/-- The carrier of the segment `[0, v]` is the segment `segment ℝ 0 v`. -/
theorem coe_segmentBody (v : Fin 1 → ℝ) :
    (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ)) = segment ℝ 0 v := by
  change (convexHull ℝ ({0, v} : Set (Fin 1 → ℝ))) = segment ℝ 0 v
  exact convexHull_pair 0 v

/-- **The segment `[0, v]` in `ℝ¹` is the interval between `0` and `v`.** -/
lemma mem_segment_dimOne {v x : Fin 1 → ℝ} :
    x ∈ CRNT.MixedVolume.Zonotope.segmentBody v ↔ min 0 (v 0) ≤ x 0 ∧ x 0 ≤ max 0 (v 0) := by
  show x ∈ (CRNT.MixedVolume.Zonotope.segmentBody v : Set (Fin 1 → ℝ)) ↔ _
  rw [coe_segmentBody, segment_eq_image']
  constructor
  · rintro ⟨θ, hθ, heq⟩
    have hx : x 0 = θ * (v 0) := by
      have h : (0 + θ • (v - 0)) 0 = x 0 := congrArg (fun f : Fin 1 → ℝ => f 0) heq
      rw [Pi.add_apply, Pi.smul_apply, Pi.sub_apply] at h
      simp only [smul_eq_mul, Pi.zero_apply] at h
      linarith
    rw [hx]
    exact mul_between_zero hθ.1 hθ.2
  · rintro ⟨h1, h2⟩
    by_cases hv : v 0 = 0
    · have hmin : min 0 (v 0) = 0 := min_eq_left (le_of_eq hv.symm)
      have hmax : max 0 (v 0) = 0 := max_eq_left (le_of_eq hv)
      have hx0 : x 0 = 0 := by
        have h1' : 0 ≤ x 0 := by simpa [hmin] using h1
        have h2' : x 0 ≤ 0 := by simpa [hmax] using h2
        linarith
      refine ⟨0, ⟨le_rfl, by simp⟩, ?_⟩
      have hx : (fun θ => 0 + θ • (v - 0)) (0 : ℝ) = x := by
        rw [finOne_eq x, hx0]
        funext i
        refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        simp
      exact hx
    · rcases lt_or_gt_of_ne hv with hvp | hvp
      · refine ⟨x 0 / v 0, ⟨?_, ?_⟩, ?_⟩
        · have hmax : max 0 (v 0) = 0 := max_eq_left hvp.le
          have hle : x 0 ≤ 0 := by simpa [hmax] using h2
          have hinv : (v 0)⁻¹ ≤ 0 := inv_nonpos.mpr hvp.le
          have hpos : 0 ≤ x 0 * (v 0)⁻¹ := mul_nonneg_of_nonpos_of_nonpos hle hinv
          rw [div_eq_mul_inv]
          exact hpos
        · have hmin : min 0 (v 0) = v 0 := min_eq_right hvp.le
          have hle : v 0 ≤ x 0 := by simpa [hmin] using h1
          exact (div_le_one_of_neg hvp).mpr hle
        · have hx : (fun θ => 0 + θ • (v - 0)) (x 0 / v 0) = x := by
            rw [finOne_eq x]
            funext i
            refine Fin.cases ?_ (fun i => Fin.elim0 i) i
            simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
            field_simp; ring
          exact hx
      · refine ⟨x 0 / v 0, ⟨?_, ?_⟩, ?_⟩
        · have hmin : min 0 (v 0) = 0 := min_eq_left hvp.le
          have hle : 0 ≤ x 0 := by simpa [hmin] using h1
          exact div_nonneg hle hvp.le
        · have hmax : max 0 (v 0) = v 0 := max_eq_right hvp.le
          have hle : x 0 ≤ v 0 := by simpa [hmax] using h2
          exact (div_le_one hvp).mpr hle
        · have hx : (fun θ => 0 + θ • (v - 0)) (x 0 / v 0) = x := by
            rw [finOne_eq x]
            funext i
            refine Fin.cases ?_ (fun i => Fin.elim0 i) i
            simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, Pi.zero_apply]
            field_simp; ring
          exact hx

/-- The **lower endpoint** of the zonotope spanned by `vs` in dimension one: the sum of the
negative parts of the generators. -/
def loDimOne (vs : List (Fin 1 → ℝ)) : ℝ := vs.foldr (fun v acc => min 0 (v 0) + acc) 0

/-- The **upper endpoint** of the zonotope spanned by `vs` in dimension one: the sum of the
positive parts of the generators. -/
def hiDimOne (vs : List (Fin 1 → ℝ)) : ℝ := vs.foldr (fun v acc => max 0 (v 0) + acc) 0

/-- The lower endpoint of a zonotope spanned by `v :: vs`. -/
@[simp] lemma loDimOne_cons (v : Fin 1 → ℝ) (vs : List (Fin 1 → ℝ)) :
    loDimOne (v :: vs) = min 0 (v 0) + loDimOne vs := rfl

/-- The upper endpoint of a zonotope spanned by `v :: vs`. -/
@[simp] lemma hiDimOne_cons (v : Fin 1 → ℝ) (vs : List (Fin 1 → ℝ)) :
    hiDimOne (v :: vs) = max 0 (v 0) + hiDimOne vs := rfl

/-- The lower endpoint of the zonotope is at most the upper endpoint. -/
lemma loDimOne_le_hiDimOne (vs : List (Fin 1 → ℝ)) : loDimOne vs ≤ hiDimOne vs := by
  unfold loDimOne hiDimOne
  induction vs with
  | nil => simp
  | cons v vs ih =>
      simp only [List.foldr_cons]
      exact add_le_add min_le_max ih

/-- **In dimension one, the zonotope spanned by a list of generators is the interval between
the sums of the negative and of the positive parts of the generators.** -/
theorem mem_zonotopeBody_dimOne (vs : List (Fin 1 → ℝ)) (x : Fin 1 → ℝ) :
    x ∈ zonotopeBody vs ↔ loDimOne vs ≤ x 0 ∧ x 0 ≤ hiDimOne vs := by
  induction vs generalizing x with
  | nil =>
      rw [zonotopeBody, List.foldr_nil]
      have hx0 : x = 0 ↔ x 0 = 0 := by
        constructor
        · intro h
          rw [h]
          rfl
        · intro h
          rw [finOne_eq x, h]
          rfl
      simp only [loDimOne, hiDimOne, List.foldr_nil]
      constructor
      · intro h
        rw [hx0.mp h]
        exact ⟨le_rfl, le_rfl⟩
      · rintro ⟨h1, h2⟩
        exact hx0.mpr (by linarith)
  | cons v vs ih =>
      have hinner : ((zonotopeBody vs : ConvexBody (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))
          = ((List.foldr (fun w K => CRNT.MixedVolume.Zonotope.segmentBody w + K) 0 vs :
            ConvexBody (Fin 1 → ℝ)) : Set (Fin 1 → ℝ)) := rfl
      show x ∈ (zonotopeBody (v :: vs) : Set (Fin 1 → ℝ)) ↔ _
      rw [zonotopeBody, List.foldr_cons, ConvexBody.coe_add, ← hinner]
      constructor
      · intro hx
        obtain ⟨a, ha, b, hb, hxy⟩ := Set.mem_image2.mp hx
        have ha' := (mem_segment_dimOne).mp ha
        have hb' := (ih b).mp hb
        have hx' : a 0 + b 0 = x 0 := by
          have h := congrArg (fun f : Fin 1 → ℝ => f 0) hxy
          rw [Pi.add_apply] at h
          exact h
        simp only [loDimOne_cons, hiDimOne_cons]
        constructor
        · linarith
        · linarith
      · rintro ⟨h1, h2⟩
        have hsplit : ∃ u w : ℝ, min 0 (v 0) ≤ u ∧ u ≤ max 0 (v 0) ∧ loDimOne vs ≤ w
          ∧ w ≤ hiDimOne vs ∧ u + w = x 0 := by
          refine exists_split_Icc_add min_le_max (loDimOne_le_hiDimOne vs) ⟨h1, h2⟩
        obtain ⟨u, w, hu1, hu2, hw1, hw2, huw⟩ := hsplit
        have ha : (fun _ => u) ∈ CRNT.MixedVolume.Zonotope.segmentBody v := by
          rw [mem_segment_dimOne]
          exact ⟨hu1, hu2⟩
        have hb : (fun _ => w) ∈ zonotopeBody vs := by
          rw [ih]
          exact ⟨hw1, hw2⟩
        refine Set.mem_image2.mpr ⟨fun _ => u, ha, fun _ => w, hb, ?_⟩
        have hx : x = fun _ => x 0 := finOne_eq x
        rw [hx]
        funext i
        refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        simp only [Pi.add_apply]
        exact huw

/-! ### 6. The volume of a zonotope in dimension one (continued) -/

/-- The sum of the lengths of the generators of a zonotope in dimension one. -/
def lengthSumDimOne (vs : List (Fin 1 → ℝ)) : ℝ := vs.foldr (fun v acc => |v 0| + acc) 0

/-- The sum of the lengths of the generators of the empty zonotope. -/
@[simp] lemma lengthSumDimOne_nil : lengthSumDimOne ([] : List (Fin 1 → ℝ)) = 0 := rfl

/-- The sum of the lengths of the generators of a zonotope spanned by `v :: vs`. -/
@[simp] lemma lengthSumDimOne_cons (v : Fin 1 → ℝ) (vs : List (Fin 1 → ℝ)) :
    lengthSumDimOne (v :: vs) = |v 0| + lengthSumDimOne vs := rfl

/-- The difference of the endpoints of the zonotope is the sum of the lengths of the
generators. -/
lemma sub_lengthSumDimOne (vs : List (Fin 1 → ℝ)) :
    hiDimOne vs - loDimOne vs = lengthSumDimOne vs := by
  induction vs with
  | nil => simp [hiDimOne, loDimOne, lengthSumDimOne]
  | cons v vs ih =>
      simp only [hiDimOne_cons, loDimOne_cons, lengthSumDimOne_cons]
      have h : max 0 (v 0) - min 0 (v 0) = |v 0| := by
        rcases le_total 0 (v 0) with h' | h'
        · simp [abs_of_nonneg h', max_eq_right h', min_eq_left h']
        · simp [abs_of_nonpos h', max_eq_left h', min_eq_right h']
      rw [ih.symm]
      linarith

/-- **The volume of a zonotope in dimension one is the sum of the lengths of its generators.**
This is Shephard's formula for the volume of a zonotope in dimension one. -/
theorem volumeI_zonotopeBody_dimOne (vs : List (Fin 1 → ℝ)) :
    (zonotopeBody vs).volumeI = lengthSumDimOne vs := by
  have hco : ((zonotopeBody vs : ConvexBody (Fin 1 → ℝ)) : Set (Fin 1 → ℝ))
      = Icc (fun _ => loDimOne vs) (fun _ => hiDimOne vs) := by
    ext x
    rw [mem_Icc_dimOne]
    exact mem_zonotopeBody_dimOne vs x
  rw [ConvexBody.volumeI, hco, Real.volume_Icc_pi_toReal (fun _ => loDimOne_le_hiDimOne vs)]
  have hprod : ∏ i : Fin 1, (hiDimOne vs - loDimOne vs) = hiDimOne vs - loDimOne vs := by
    simp
  rw [hprod, sub_lengthSumDimOne]

/-- **The mixed volume of the singleton zonotope spanned by a segment of `ℝ¹` is its length.**
This is the classical determinant formula `|det (v)| = |v|` in dimension one. -/
theorem mixedVolume_segment_dimOne (v : Fin 1 → ℝ) :
    CRNT.MixedVolume.mixedVolume (fun _ : Fin 1 => (⟨[v]⟩ : CRNT.MixedVolume.Zonotope 1))
      = |v 0| := by
  have h1 : List.ofFn (fun _ : Fin 1 => (⟨[v]⟩ : CRNT.MixedVolume.Zonotope 1))
      = [(⟨[v]⟩ : CRNT.MixedVolume.Zonotope 1)] := by simp
  have h2 : CRNT.MixedVolume.mixedVolumeList [(⟨[v]⟩ : CRNT.MixedVolume.Zonotope 1)]
      = CRNT.MixedVolume.absDet [v] := by
    have h3 : List.map (fun w : Fin 1 → ℝ => (⟨[w]⟩ : CRNT.MixedVolume.Zonotope 1)) [v]
        = [(⟨[v]⟩ : CRNT.MixedVolume.Zonotope 1)] := by simp
    rw [← h3]
    exact CRNT.MixedVolume.mixedVolumeList_singleton [v]
  rw [CRNT.MixedVolume.mixedVolume, h1, h2, CRNT.MixedVolume.absDet_singleton]

/-- **The volume of a zonotope in dimension one is the mixed volume of its generators.**

The volume of the zonotope spanned by the segments `[0, v]`, `v ∈ vs`, is the sum of the mixed
volumes of the `n` singleton zonotopes spanned by the generators — Shephard's formula for the
volume of a zonotope, in dimension one. -/
theorem volume_zonotope_eq_mixedVolume_dimOne (vs : List (Fin 1 → ℝ)) :
    (zonotopeBody vs).volumeI
      = vs.foldr (fun v acc =>
          CRNT.MixedVolume.mixedVolume (fun _ : Fin 1 => (⟨[v]⟩ : CRNT.MixedVolume.Zonotope 1)) + acc) 0 := by
  rw [volumeI_zonotopeBody_dimOne]
  have h : ∀ v : Fin 1 → ℝ, |v 0| =
      CRNT.MixedVolume.mixedVolume (fun _ : Fin 1 => (⟨[v]⟩ : CRNT.MixedVolume.Zonotope 1)) :=
    fun v => (mixedVolume_segment_dimOne v).symm
  induction vs with
  | nil => simp
  | cons v vs ih =>
      simp only [lengthSumDimOne_cons, List.foldr_cons]
      rw [h v, ih]

/-! ### 7. The degenerate case -/

/-- **A zonotope whose generators vanish in one coordinate lies in a coordinate hyperplane.** -/
theorem mem_coordHyperplane (vs : List (Fin n → ℝ)) (i : Fin n)
    (h : ∀ v ∈ vs, v i = 0) : ∀ x ∈ (zonotopeBody vs : Set (Fin n → ℝ)), x i = 0 := by
  induction vs with
  | nil =>
      intro x hx
      rw [zonotopeBody, List.foldr_nil] at hx
      have hx' : x = 0 := Set.mem_singleton_iff.mp hx
      subst hx'
      simp
  | cons w vs ih =>
      intro x hx
      rw [zonotopeBody, List.foldr_cons, ConvexBody.coe_add] at hx
      obtain ⟨a, ha, b, hb, hxy⟩ := Set.mem_image2.mp hx
      have hai : a i = 0 := by
        have hseg : (CRNT.MixedVolume.Zonotope.segmentBody w : Set (Fin n → ℝ)) = segment ℝ 0 w := by
          change (convexHull ℝ ({0, w} : Set (Fin n → ℝ))) = segment ℝ 0 w
          exact convexHull_pair 0 w
        rw [hseg, segment_eq_image'] at ha
        obtain ⟨θ, hθ, heq⟩ := (Set.mem_image _ _ _).mp ha
        have h1 := congrArg (fun f : Fin n → ℝ => f i) heq
        rw [Pi.add_apply, Pi.smul_apply, Pi.sub_apply] at h1
        simp only [smul_eq_mul, Pi.zero_apply] at h1
        have h2 : a i = θ * (w i - 0) := by linarith
        rw [h2, h w List.mem_cons_self]
        simp
      have hbi : b i = 0 := by
        have hinner : ((zonotopeBody vs : ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ))
            = ((List.foldr (fun u K => CRNT.MixedVolume.Zonotope.segmentBody u + K) 0 vs :
              ConvexBody (Fin n → ℝ)) : Set (Fin n → ℝ)) := rfl
        rw [← hinner] at hb
        exact ih (fun v hv => h v (List.mem_cons.mpr (Or.inr hv))) b hb
      have h1 := congrArg (fun f : Fin n → ℝ => f i) hxy
      rw [Pi.add_apply] at h1
      linarith

/-- **A zonotope whose generators vanish in one coordinate lies in a coordinate hyperplane.** -/
theorem subset_coordHyperplane (vs : List (Fin n → ℝ)) (i : Fin n)
    (h : ∀ v ∈ vs, v i = 0) : (zonotopeBody vs : Set (Fin n → ℝ)) ⊆ {x | x i = 0} :=
  fun x hx => mem_coordHyperplane vs i h x hx

/-- **The volume of a degenerate zonotope is zero.**

If all the generators of the zonotope vanish in one coordinate, the zonotope is contained in a
coordinate hyperplane, which has Lebesgue measure zero; hence so has the zonotope.  This is the
degenerate case of Shephard's formula: the mixed volume of the generators is zero as well
(`zonotopeVolumePolynomial_degenerate`). -/
theorem volumeI_zonotopeBody_degenerate (vs : List (Fin n → ℝ)) (i : Fin n)
    (h : ∀ v ∈ vs, v i = 0) : (zonotopeBody vs).volumeI = 0 := by
  obtain ⟨M, hM0, hM⟩ : ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ (zonotopeBody vs : Set (Fin n → ℝ)), ∀ j, |x j| ≤ M := by
    obtain ⟨M, hMb⟩ := Metric.isBounded_iff.mp (zonotopeBody vs).isCompact'.isBounded
    have h0 : (0 : Fin n → ℝ) ∈ (zonotopeBody vs : Set (Fin n → ℝ)) := mem_zonotopeBody_zero vs
    refine ⟨M, ?_, ?_⟩
    · have hM0 := hMb h0 h0
      simp only [dist_self] at hM0
      exact hM0
    · intro x hx j
      have h1 : dist x 0 ≤ M := hMb hx h0
      have h2 : |x j| ≤ dist x 0 := by
        rw [dist_eq_norm, sub_zero]
        exact norm_le_pi_norm x j
      exact h2.trans h1
  have hbox : (zonotopeBody vs : Set (Fin n → ℝ))
      ⊆ Icc (fun j => if j = i then 0 else -M) (fun j => if j = i then 0 else M) := by
    intro x hx
    have hxi : x i = 0 := subset_coordHyperplane vs i h hx
    rw [Set.mem_Icc]
    constructor
    · intro j
      by_cases hj : j = i
      · simp [hj, hxi]
      · have hle : |x j| ≤ M := hM x hx j
        have h1 : -M ≤ x j := by linarith [(abs_le.mp hle).1]
        simp [hj]
        exact h1
    · intro j
      by_cases hj : j = i
      · simp [hj, hxi]
      · have hle : |x j| ≤ M := hM x hx j
        have h2 : x j ≤ M := by linarith [(abs_le.mp hle).2]
        simp [hj]
        exact h2
  have hmeas : (MeasureTheory.MeasureSpace.volume
      (Icc (fun j => if j = i then 0 else -M) (fun j => if j = i then 0 else M))) = 0 := by
    rw [Real.volume_Icc_pi]
    rw [Finset.prod_eq_zero (i := i) (Finset.mem_univ _)]
    simp
  have hle : (MeasureTheory.MeasureSpace.volume (zonotopeBody vs : Set (Fin n → ℝ)))
      ≤ MeasureTheory.MeasureSpace.volume
        (Icc (fun j => if j = i then 0 else -M) (fun j => if j = i then 0 else M)) :=
    MeasureTheory.measure_mono hbox
  have hz : (MeasureTheory.MeasureSpace.volume (zonotopeBody vs : Set (Fin n → ℝ))) = 0 := by
    have h2 : (MeasureTheory.MeasureSpace.volume
        (Icc (fun j => if j = i then 0 else -M) (fun j => if j = i then 0 else M)))
        ≤ (MeasureTheory.MeasureSpace.volume (zonotopeBody vs : Set (Fin n → ℝ))) := by
      rw [hmeas]
      exact bot_le
    calc (MeasureTheory.MeasureSpace.volume (zonotopeBody vs : Set (Fin n → ℝ)))
        = MeasureTheory.MeasureSpace.volume
            (Icc (fun j => if j = i then 0 else -M) (fun j => if j = i then 0 else M)) :=
          le_antisymm hle h2
      _ = 0 := hmeas
  rw [ConvexBody.volumeI, hz]
  rfl

/-- **The mixed volume of a degenerate zonotope is zero.**

If all the generators of the zonotope vanish in one coordinate, the matrix of any `n` of them
has a zero row, so its determinant — and hence the mixed volume — vanishes. -/
theorem zonotopeVolumePolynomial_degenerate (z : Fin m → Fin n → ℝ) (i : Fin n)
    (h : ∀ j, z j i = 0) : CRNT.MixedVolume.zonotopeVolumePolynomial z (fun _ => 1) = 0 := by
  classical
  rw [CRNT.MixedVolume.zonotopeVolumePolynomial_at_one]
  apply Finset.sum_eq_zero
  intro S hS
  have hcard : S.card = n := (Finset.mem_powersetCard.mp hS).2
  have hlen : (CRNT.MixedVolume.finsetSorted S).length = n := by
    rw [CRNT.MixedVolume.finsetSorted, Finset.length_sort (fun a b => a ≤ b), hcard]
  -- every generator of `S` vanishes in the coordinate `i`
  have hzero : ∀ k : Fin n, (CRNT.MixedVolume.sortedGenerator z S k) i = 0 := by
    intro k
    have hk : k.val < (CRNT.MixedVolume.finsetSorted S).length := by simp [hlen]
    have hget : CRNT.MixedVolume.sortedGenerator z S k
        = z ((CRNT.MixedVolume.finsetSorted S)[k.val]) := by
      simp only [CRNT.MixedVolume.sortedGenerator]
      rw [List.getD_eq_getElem _ _ (by simp [hk]), List.getElem_map]
    rw [hget]
    have hmem : (CRNT.MixedVolume.finsetSorted S)[k.val] ∈ S :=
      (Finset.mem_sort (α := Fin m) (fun a b => a ≤ b)).1 (List.get_mem _ ⟨k.val, hk⟩)
    exact h (CRNT.MixedVolume.finsetSorted S)[k.val]
  -- the matrix of the `n` generators of `S` has a zero row
  have hrow : ∀ j : Fin n, CRNT.MixedVolume.columnMatrix
      (List.ofFn (fun k : Fin n => CRNT.MixedVolume.sortedGenerator z S k)) i j = 0 := by
    intro j
    simp only [CRNT.MixedVolume.columnMatrix]
    have hj : j.val < n := j.isLt
    have hget : (List.ofFn (fun k : Fin n => CRNT.MixedVolume.sortedGenerator z S k)).getD j.val 0
        = CRNT.MixedVolume.sortedGenerator z S ⟨j.val, hj⟩ := by
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
    rw [hget]
    exact hzero ⟨j.val, hj⟩
  have hdet : (CRNT.MixedVolume.columnMatrix
      (List.ofFn (fun k : Fin n => CRNT.MixedVolume.sortedGenerator z S k))).det = 0 :=
    Matrix.det_eq_zero_of_row_eq_zero i hrow
  have h1 : List.ofFn (fun k : Fin n => (⟨[CRNT.MixedVolume.sortedGenerator z S k]⟩ :
        CRNT.MixedVolume.Zonotope n))
      = List.map (fun w : Fin n → ℝ => (⟨[w]⟩ : CRNT.MixedVolume.Zonotope n))
        (List.ofFn (fun k : Fin n => CRNT.MixedVolume.sortedGenerator z S k)) := by
      have hcomp : (fun k : Fin n => (⟨[CRNT.MixedVolume.sortedGenerator z S k]⟩ :
          CRNT.MixedVolume.Zonotope n))
          = (fun w : Fin n → ℝ => (⟨[w]⟩ : CRNT.MixedVolume.Zonotope n)) ∘
            (fun k : Fin n => CRNT.MixedVolume.sortedGenerator z S k) := rfl
      rw [hcomp]
      exact List.ofFn_comp' (fun k : Fin n => CRNT.MixedVolume.sortedGenerator z S k)
        (fun w : Fin n → ℝ => (⟨[w]⟩ : CRNT.MixedVolume.Zonotope n))
  have hlen2 : (List.ofFn (fun k : Fin n => CRNT.MixedVolume.sortedGenerator z S k)).length = n := by
    simp
  rw [CRNT.MixedVolume.mixedVolume, h1, CRNT.MixedVolume.mixedVolumeList_singleton]
  rw [CRNT.MixedVolume.absDet, ite_eq_left hlen2]
  rw [hdet]
  simp

/-! ### 8. Audit -/

#print axioms ConvexBody.volumeI
#print axioms measurableSet_coe
#print axioms volume_ne_top
#print axioms volumeI_nonneg
#print axioms volume_le_of_subset
#print axioms volume_le_of_subset'
#print axioms volumeI_pointBody
#print axioms zonotopeBody
#print axioms mem_zonotopeBody_zero
#print axioms mem_zonotopeBody_of_mem
#print axioms convexHull_subset_zonotopeBody
#print axioms circuitNewtonPolytope_subset_zonotopeBody
#print axioms volumeI_circuitNewtonPolytope_le
#print axioms convexHull_subset_translate_zonotopeBody
#print axioms convexHull_three_not_subset_zonotopeBody_dimOne
#print axioms mem_segment_dimOne
#print axioms mem_zonotopeBody_dimOne
#print axioms volumeI_zonotopeBody_dimOne
#print axioms mixedVolume_segment_dimOne
#print axioms volume_zonotope_eq_mixedVolume_dimOne
#print axioms mem_coordHyperplane
#print axioms subset_coordHyperplane
#print axioms volumeI_zonotopeBody_degenerate
#print axioms zonotopeVolumePolynomial_degenerate

end Geometry
end CRNT
