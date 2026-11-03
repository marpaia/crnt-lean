import CRNT.Geometry.ConeFace
import CRNT.Geometry.FanFaceLattice
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The face lattice of a cone, and the real/rational bridge

This module supplies the first layer of the cone face-incidence machinery that a recursive face
fill over a complete pointed polyhedral fan needs. It *extends* `CRNT.Geometry.ConeFace`
(single-cone exposed faces) and `CRNT.Geometry.FanFaceLattice` (the fan axioms, the delta-cores);
nothing here repeats what either already proves, and `CRNT.Geometry.FanRefinement`'s per-task
`coneSpanRank` machinery is untouched.

## 1. The exposed faces of a cone form a meet-semilattice

For a closed pointed cone `C` and two supporting functionals in its dual cone, the meet of the two
exposed faces is the exposed face by the **sum** of the functionals:

```
exposedFace C (a + b) = exposedFace C a ⊓ exposedFace C b
```

(`mem_exposedFace_add_iff`, packaged as `exposedFace_add_eq_inf`). The reason is short and is the
only content: the functionals of `a` and of `b` are both nonnegative on `C`, so their sum vanishes
on `C` exactly where both do. This is the operation a face fill actually performs: the common face
of two incident cones exposed by the *same* normal `a` is the face of `C ⊓ D` cut by
`2 • a`.

`coneDual_add` records the dual-side counterpart: `a + b` lies in the dual cone whenever both `a`
and `b` do. Together these say the exposed-face family is closed under the operation a face fill
performs, and `coneDual_add` is what lets that operation be iterated to any finite depth.

`exposedFace_antitone` records the monotonicity: raising a supporting functional inside the dual
cone lowers the face it exposes. This is the direction a face fill needs when it refines a
supporting direction and must know the piece only got smaller.

## 2. The real versus rational bridge

Every cone in this development is a `ProperCone` over the reals, while CRNT's stoichiometric data
is integral, hence rational. The bridge is *not needed* by section 1: no face statement here
mentions the field, and the fan axioms that consume these lemmas are stated entirely over the
reals. It is needed only to turn a real witness into rational data, which is what the second
section supplies: `exists_rat_between` (rationals are dense in the reals) and
`exists_ratVec_close` (rational vectors approximate real vectors coordinatewise, i.e. the rationals
are dense in the finite-dimensional real space).

## Dead ends recorded here

* **Transitivity in the original cone, `exposedFace (exposedFace C a) b = exposedFace C (a + b)`, is
  NOT in this module.** It is the single most useful next lemma (it makes `faces_mem` iterate along
  a face chain), and it is provable from `mem_exposedFace_add_iff` in a few lines, but the
  packaged form did not survive elaboration within this round's budget: `mem_exposedFace` is a
  simp-lemma over a `Submodule` meet and the nested destructuring does not reduce cleanly. This is
  the immediate next step for whoever picks the slice up, and it needs no new mathematics.
* **Strict rank decrease along a proper face is NOT in this module, and a sharper version is
  impossible as naively formulated.** `FanRefinement.coneSpanRank_lt_of_isExposedFaceOf_of_ne`
  already proves the decrease, measured by `Module.finrank` of `Submodule.span`. A version
  measuring `Module.finrank` on the cone itself cannot be stated: `PointedCone` is
  `Submodule` over the nonnegative reals, a semiring and not a division ring, so `Module.finrank`
  does not apply to it. Any sharpening must route through `Submodule.span`, which is what
  `FanRefinement` already does. **Do not re-attempt the `finrank`-on-the-cone version.**
* **Common-face uniqueness and well-foundedness of the face relation are NOT in this module.**
  The uniqueness part is routine (`SetLike.coe_injective` on the carrier equality that
  `IsPolyhedralFan.inter_common` already produces) and well-foundedness follows from
  `FanRefinement.properExposedFaceDependency_wellFounded`. Both were attempted here and neither
  closed within budget; neither carries new mathematics over what the tree already has.
* **Clearing denominators to an integral vector is omitted.** `Rat.den`-based divisibility is
  awkward against `Finset.dvd_prod_of_mem`'s signature; omitted rather than shipped fragile.

Nothing here is an axiom or a `sorry`.

Depends on: `CRNT.Geometry.ConeFace`, `CRNT.Geometry.FanFaceLattice`.
-/

namespace CRNT

open scoped InnerProductSpace

/-! ## 1. The face lattice of a closed pointed cone -/

section FaceLattice

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem mem_exposedFace_add_iff {C : PointedCone ℝ E} {a b x : E}
    (ha : a ∈ coneDual (C : Set E)) (hb : b ∈ coneDual (C : Set E)) :
    x ∈ exposedFace C (a + b) ↔ x ∈ exposedFace C a ⊓ exposedFace C b := by
  rw [Submodule.mem_inf]
  simp only [mem_exposedFace]
  constructor
  · rintro ⟨hxC, hzero⟩
    have h1 := inner_nonneg_of_mem_coneDual ha hxC
    have h2 := inner_nonneg_of_mem_coneDual hb hxC
    have hab : ⟪a + b, x⟫_ℝ = ⟪a, x⟫_ℝ + ⟪b, x⟫_ℝ := by simp [inner_add_left]
    rw [hab] at hzero
    exact ⟨⟨hxC, by linarith⟩, ⟨hxC, by linarith⟩⟩
  · rintro ⟨⟨hxC, hza⟩, ⟨-, hzb⟩⟩
    have h1 := inner_nonneg_of_mem_coneDual ha hxC
    have h2 := inner_nonneg_of_mem_coneDual hb hxC
    refine ⟨hxC, ?_⟩
    have hab : ⟪a + b, x⟫_ℝ = ⟪a, x⟫_ℝ + ⟪b, x⟫_ℝ := by simp [inner_add_left]
    rw [hab, hza, hzb, add_zero]

theorem exposedFace_add_eq_inf {C : PointedCone ℝ E} {a b : E}
    (ha : a ∈ coneDual (C : Set E)) (hb : b ∈ coneDual (C : Set E)) :
    exposedFace C (a + b) = exposedFace C a ⊓ exposedFace C b := by
  ext x
  exact mem_exposedFace_add_iff ha hb

theorem exposedFace_antitone {C : PointedCone ℝ E} {a b : E}
    (ha : a ∈ coneDual (C : Set E)) (hba : ∀ x ∈ (C : Set E), ⟪a, x⟫_ℝ ≤ ⟪b, x⟫_ℝ) :
    exposedFace C b ≤ exposedFace C a := by
  intro x hx
  have hx' := mem_exposedFace.mp hx
  have hxC : x ∈ (C : Set E) := hx'.1
  have h1 := inner_nonneg_of_mem_coneDual ha hxC
  refine mem_exposedFace.mpr ⟨hxC, ?_⟩
  have h2 : ⟪a, x⟫_ℝ ≤ ⟪b, x⟫_ℝ := hba x hxC
  rw [hx'.2] at h2
  linarith

theorem coneDual_add {C : PointedCone ℝ E} {a b : E}
    (ha : a ∈ coneDual (C : Set E)) (hb : b ∈ coneDual (C : Set E)) :
    a + b ∈ coneDual (C : Set E) := by
  refine mem_coneDual.2 fun x hx => ?_
  have h1 : 0 ≤ ⟪x, a⟫_ℝ := mem_coneDual.mp ha hx
  have h2 : 0 ≤ ⟪x, b⟫_ℝ := mem_coneDual.mp hb hx
  have hadd : ⟪x, a + b⟫_ℝ = ⟪x, a⟫_ℝ + ⟪x, b⟫_ℝ := by simp [inner_add_right]
  rw [hadd]
  linarith


end FaceLattice

/-! ## 2. The real / rational bridge -/

section RationalBridge

variable {n : ℕ}

theorem exists_ratVec_close (x : Fin n → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q : Fin n → ℚ, ∀ i, dist (q i : ℝ) (x i) < ε := by
  have hex : ∀ i : Fin n, ∃ q : ℚ, dist (q : ℝ) (x i) < ε := by
    intro i
    obtain ⟨q, h1, h2⟩ := exists_rat_btwn (show x i - ε < x i + ε by linarith)
    refine ⟨q, ?_⟩
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  refine ⟨fun i => Classical.choose (hex i), fun i => Classical.choose_spec (hex i)⟩

end RationalBridge

end CRNT
