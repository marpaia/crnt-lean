import CRNT.Equilibria.CompatibilityClass
import CRNT.Geometry.CompatibilityFaces
import CRNT.Geometry.ConservativeCompatibility
import CRNT.Dynamics.SiphonConservation
import CRNT.Stoich.Subspace
import Mathlib.Analysis.Convex.Basic

/-!
# Stoichiometric compatibility classes: the zero-set antitone engine

This module records the *order-theoretic* content of the maximal-face (`wmax` / `Pmax`)
mechanism: the zero set `zeroSet x = {s | x s = 0}` of a concentration, its antitone
behaviour under coordinatewise comparison, and the pure `Finset` combinatorics that
produce the maximal zero set of an arbitrary family of nonnegative class points.

The affine reading of the class (`x₀ + N.stoichSubspace`) comes from
`CRNT.Equilibria.CompatibilityClass`; closedness of its nonnegative part comes from
`CRNT.Geometry.ConservativeCompatibility`.

## What is proved

**A. The class is an affine subspace, and it is convex.**

* `stoichCompatible_iff_exists_sub` : `N.StoichCompatible x₀ x ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v`,
  the literal affine-span reading of the definition.
* `mem_compatibilityClass_iff_exists_sub` : the same for the class itself.
* `mem_compatibilityClass_self` : the reference point is in its own class.
* `stoichCompatible_smul_add` : closure under `x₀ + a • v` for `v ∈ S(N)`.
* `stoichCompatible_of_convex_combination` : for `a + b = 1`, the point `a • x + b • y` is
  compatible with `x₀` whenever `x` and `y` both are. This is what makes the class an *affine*
  subspace rather than merely a translate-invariant set, and it is what the two convexity
  theorems below are built on.
* `stoichCompatible_segment` : the segment `(1-t) • x₀ + t • x` stays in the class.
* `compatibilityClass_isConvex`, `nonnegativeCompatibilityClass_isConvex`,
  `positiveCompatibilityClass_isConvex`.

**B. Zero sets and the antitone engine.**

* `zeroSet`, `mem_zeroSet_iff`, `zeroSet_eq_filter`.
* `mem_zeroSet_iff_of_mem_nonnegativeCompatibilityClass`.
* `zeroSet_antitone_of_le` : if `z` is nonnegative and `z ≤ w` coordinatewise then
  `zeroSet w ⊆ zeroSet z`. This single lemma is the engine of the whole `Pmax` package.
* `not_mem_zeroSet_of_strictly_gt` : if `z` is nonnegative and `z s < w s` then `s ∉ zeroSet w`.
* `zeroSet_ssubset_of_strictlyGreater` : **strict domination grows the zero set.** If
  `z` is nonnegative, `z ≤ w` coordinatewise, `z` is strictly dominated at every coordinate,
  and `z` vanishes somewhere, then `zeroSet w ⊊ zeroSet z`.
* `exists_zeroCoordinate_of_strictlyDominated` : **the boundary is reachable.** If `w` and `z`
  are nonnegative points of the same class and `z s < w s` at every coordinate, then the class
  contains a nonnegative point with a vanishing coordinate.
* `not_lt_of_mem_nonnegativeCompatibilityClass_of_maximal_zeroSet` : **a maximal zero set
  cannot be strictly dominated.** If no member of the nonnegative class has a zero set
  strictly containing `zeroSet w`, then no member of the class is strictly below `w`
  coordinatewise. This is the `wmax` forcing argument.

**C. Maximal zero sets: the finite combinatorics.**

* `exists_maximal_zeroSet` : for any nonempty family `Ξ` of nonnegative class points there are
  `wmax ∈ Ξ` and `Pmax := zeroSet wmax` with the two clauses the `wmax` / `Pmax` package
  needs: `|zeroSet z| ≤ |Pmax|` for every `z ∈ Ξ` (`hzcard`), and every `z ∈ Ξ` that vanishes
  on all of `Pmax` vanishes exactly on `Pmax` (`hmaxExact`). This is the purely combinatorial
  core behind `CRNT.Dynamics.GACOmegaPositive.exists_maximal_zeroSet_omegaPoint`, with the
  ω-limit-set quantifier replaced by an arbitrary family — no dynamics are used.

Depends on: `CRNT.Equilibria.CompatibilityClass`,
`CRNT.Geometry.CompatibilityFaces`, `CRNT.Geometry.ConservativeCompatibility`,
`CRNT.Dynamics.SiphonConservation`, `CRNT.Stoich.Subspace`, Mathlib `Analysis.Convex`.
-/

namespace CRNT
namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### A. The compatibility class is an affine subspace -/

/-- **The affine-span reading of compatibility.** A point is in the class of `x₀` exactly
when it is `x₀ + v` for some stoichiometric displacement `v ∈ N.stoichSubspace`. -/
theorem stoichCompatible_iff_exists_sub (N : Network S) (x₀ x : Concentration S) :
    N.StoichCompatible x₀ x ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v := by
  constructor
  · intro h
    refine ⟨x - x₀, h, ?_⟩
    funext s
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  · rintro ⟨v, hv, hxv⟩
    rw [StoichCompatible, hxv]
    have hzero : x₀ + v - x₀ = v := by
      funext s
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [hzero]
    exact hv

/-- The same statement for the class itself. -/
theorem mem_compatibilityClass_iff_exists_sub (N : Network S) (x₀ x : Concentration S) :
    x ∈ N.compatibilityClass x₀ ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v :=
  (mem_compatibilityClass).trans (N.stoichCompatible_iff_exists_sub x₀ x)

/-- **The reference point is in its own class.** -/
theorem mem_compatibilityClass_self (N : Network S) (x₀ : Concentration S) :
    x₀ ∈ N.compatibilityClass x₀ := StoichCompatible.refl N x₀

/-- **Rays out of the reference point stay in the class.** For `v ∈ N.stoichSubspace` and any
real `a`, the point `x₀ + a • v` is stoichiometrically compatible with `x₀`. -/
theorem stoichCompatible_smul_add (N : Network S) {x₀ : Concentration S} (v : S → ℝ)
    (hv : v ∈ N.stoichSubspace) (a : ℝ) : N.StoichCompatible x₀ (x₀ + a • v) :=
  (N.stoichCompatible_iff_exists_sub x₀ (x₀ + a • v)).mpr
    ⟨a • v, N.stoichSubspace.smul_mem a hv, rfl⟩

/-- **The general two-point combination form.** If `x` and `y` are both compatible with `x₀`
and `a + b = 1`, then so is `a • x + b • y`.

The hypothesis `a + b = 1` is not cosmetic: without it the displacement
`a • x + b • y - x₀` picks up the extra term `(a + b - 1) • x₀`, which is a multiple of `x₀`
rather than of a stoichiometric displacement, and `x₀` need not lie in `N.stoichSubspace`. -/
theorem stoichCompatible_of_convex_combination (N : Network S) {x₀ x y : Concentration S}
    (hx : N.StoichCompatible x₀ x) (hy : N.StoichCompatible x₀ y) (a b : ℝ) (hab : a + b = 1) :
    N.StoichCompatible x₀ (a • x + b • y) :=
  (N.stoichCompatible_iff_exists_sub x₀ (a • x + b • y)).mpr
    ⟨a • (x - x₀) + b • (y - x₀),
      N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem a hx)
        (N.stoichSubspace.smul_mem b hy), by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      have hsum : a * x₀ s + b * x₀ s = x₀ s := by
        rw [← add_mul, hab, one_mul]
      linarith⟩

/-- **Segments inside the class.** For `0 ≤ t ≤ 1` the point `(1-t) • x₀ + t • x` is compatible
with `x₀` whenever `x` is. The two inequalities only record that the point really lies on the
*segment*; the compatibility itself holds for every real `t`. -/
theorem stoichCompatible_segment (N : Network S) {x₀ x : Concentration S}
    (hx : N.StoichCompatible x₀ x) {t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    N.StoichCompatible x₀ ((1 - t) • x₀ + t • x) :=
  N.stoichCompatible_of_convex_combination (StoichCompatible.refl N x₀) hx (1 - t) t (by ring)

/-- **Convexity of the compatibility class.** -/
theorem compatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.compatibilityClass x₀) := by
  intro x hx y hy a b ha hb hab
  rw [mem_compatibilityClass]
  exact N.stoichCompatible_of_convex_combination
    (mem_compatibilityClass.mp hx) (mem_compatibilityClass.mp hy) a b hab

/-- **Convexity of the nonnegative part of the class.** Compatibility is handled by
`stoichCompatible_of_convex_combination`; pointwise nonnegativity is preserved by nonnegative
combinations. -/
theorem nonnegativeCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.nonnegativeCompatibilityClass x₀) := by
  intro x hx y hy a b ha hb hab
  refine ⟨N.stoichCompatible_of_convex_combination hx.1 hy.1 a b hab, ?_⟩
  intro s
  have h1 := add_nonneg (mul_nonneg ha (hx.2 s)) (mul_nonneg hb (hy.2 s))
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1

/-- **Convexity of the positive part of the class.** Membership in
`N.positiveCompatibilityClass` is `N.StoichCompatible x₀ x ∧ x.Positive`; when `a = 0` the
combination collapses to `y`, which is already positive. -/
theorem positiveCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveCompatibilityClass x₀) := by
  intro x hx y hy a b ha hb hab
  refine ⟨N.stoichCompatible_of_convex_combination hx.1 hy.1 a b hab, ?_⟩
  intro s
  rcases ha.eq_or_lt with hzero | hapos
  · subst hzero
    have hb1 : b = 1 := by linarith [hab]
    subst hb1
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, mul_one, one_mul,
      zero_add] using (hy.2 s)
  · have h1 := add_pos_of_pos_of_nonneg (mul_pos hapos (hx.2 s)) (mul_nonneg hb (hy.2 s).le)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1

/-! ### B. Zero sets and the antitone engine -/

/-- The zero set of a concentration: the species whose coordinate vanishes. -/
noncomputable def zeroSet {S : Type} [DecidableEq S] [Fintype S] (x : Concentration S) :
    Finset S :=
  Finset.univ.filter fun s => x s = 0

@[simp] theorem mem_zeroSet_iff {S : Type} [DecidableEq S] [Fintype S]
    (x : Concentration S) (s : S) :
    s ∈ zeroSet x ↔ x s = 0 := by
  simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **The zero set is exactly the set of vanishing coordinates.** -/
theorem zeroSet_eq_filter {S : Type} [DecidableEq S] [Fintype S] (x : Concentration S) :
    zeroSet x = Finset.univ.filter (fun s => x s = 0) := rfl

/-- The zero set of a point of the nonnegative part of a class determines its face
membership, independently of the class it lives in. -/
theorem mem_zeroSet_iff_of_mem_nonnegativeCompatibilityClass (N : Network S)
    {x₀ x : Concentration S} (_hx : x ∈ N.nonnegativeCompatibilityClass x₀) (s : S) :
    s ∈ zeroSet x ↔ x s = 0 := mem_zeroSet_iff x s

/-- **The `Pmax` antitone engine.** If `z` is nonnegative and `z ≤ w` coordinatewise then
`zeroSet w ⊆ zeroSet z`: wherever the larger point vanishes, the smaller one does too.

The nonnegativity of `z` is essential — without it `z ≤ w` only yields `z s ≤ 0` off the
support of `w`. -/
theorem zeroSet_antitone_of_le {z w : Concentration S} (hz : z.Nonnegative)
    (hzw : ∀ s, z s ≤ w s) : zeroSet w ⊆ zeroSet z := by
  intro s hs
  have hws : w s = 0 := (mem_zeroSet_iff w s).mp hs
  rw [mem_zeroSet_iff z s]
  exact le_antisymm (hzw s |>.trans_eq hws) (hz s)

/-- **Strict inequality at a coordinate separates.** If `z` is nonnegative and `z s < w s`
then `s ∉ zeroSet w`. -/
theorem not_mem_zeroSet_of_strictly_gt {z w : Concentration S} (hz : z.Nonnegative) {s : S}
    (hlt : z s < w s) : s ∉ zeroSet w := by
  intro hs
  have hws : w s = 0 := (mem_zeroSet_iff w s).mp hs
  exact absurd hlt (by rw [hws]; exact not_lt_of_ge (hz s))

/-- **Strict domination grows the zero set strictly.** If `z` is nonnegative, `z ≤ w`
coordinatewise, `z` is strictly dominated at *every* coordinate, and `z` vanishes at some
coordinate, then `zeroSet w ⊊ zeroSet z`: the coordinate where `z` vanishes is positive for
`w`, while `w` can only vanish where `z` does.

The statement is pure coordinate order theory; no compatibility hypothesis is needed. -/
theorem zeroSet_ssubset_of_strictlyGreater {w z : Concentration S} (hz : z.Nonnegative)
    (hzw : ∀ s, z s ≤ w s) (hlt : ∀ s, z s < w s) (hzero : ∃ s, z s = 0) :
    zeroSet w ⊂ zeroSet z := by
  refine Finset.ssubset_iff_subset_ne.mpr ⟨zeroSet_antitone_of_le hz hzw, ?_⟩
  intro hEq
  obtain ⟨s, hs⟩ := hzero
  have hws : w s = 0 := (mem_zeroSet_iff w s).mp (hEq ▸ (mem_zeroSet_iff z s).mpr hs)
  linarith [hlt s]

/-- **The boundary is reachable from a strictly dominated class point.** If `w` and `z` are
nonnegative points of the same class and `z s < w s` at every coordinate, then the class
contains a nonnegative point with a vanishing coordinate: walk along the stoichiometric
direction `w - z` until the first coordinate hits zero.

This is the engine behind `not_lt_of_mem_nonnegativeCompatibilityClass_of_maximal_zeroSet`:
the class of a dominated point always meets the boundary of the orthant. -/
theorem exists_zeroCoordinate_of_strictlyDominated (N : Network S) [Nonempty S]
    {x₀ w z : Concentration S} (hw : w ∈ N.nonnegativeCompatibilityClass x₀)
    (hz : z ∈ N.nonnegativeCompatibilityClass x₀) (hlt : ∀ s, z s < w s) :
    ∃ y ∈ N.nonnegativeCompatibilityClass x₀, ∃ s, y s = 0 := by
  have hvpos : ∀ s, 0 < w s - z s := fun s => sub_pos.mpr (hlt s)
  have hv : w - z ∈ N.stoichSubspace := by
    have h1 : w - x₀ ∈ N.stoichSubspace := hw.1
    have h2 : z - x₀ ∈ N.stoichSubspace := hz.1
    have h3 : (w - x₀) - (z - x₀) = w - z := by
      funext q
      simp only [Pi.sub_apply]
      ring
    rw [← h3]
    exact N.stoichSubspace.sub_mem h1 h2
  obtain ⟨s₀, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset S)
    (fun s => w s / (w s - z s)) Finset.univ_nonempty
  have htle : ∀ q : S, w s₀ / (w s₀ - z s₀) ≤ w q / (w q - z q) :=
    fun q => hmin q (Finset.mem_univ q)
  refine ⟨w - (w s₀ / (w s₀ - z s₀)) • (w - z), ⟨?_, ?_⟩, s₀, ?_⟩
  · rw [StoichCompatible]
    have hid : (w - (w s₀ / (w s₀ - z s₀)) • (w - z)) - x₀
        = (w - x₀) - (w s₀ / (w s₀ - z s₀)) • (w - z) := by
      funext q
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hid]
    exact N.stoichSubspace.sub_mem hw.1 (N.stoichSubspace.smul_mem _ hv)
  · intro q
    have hle : (w s₀ / (w s₀ - z s₀)) * (w q - z q) ≤ w q := by
      have h1 := mul_le_mul_of_nonneg_right (htle q) (le_of_lt (hvpos q))
      calc (w s₀ / (w s₀ - z s₀)) * (w q - z q)
          = w s₀ * (w q - z q) / (w s₀ - z s₀) := by ring
        _ ≤ (w q / (w q - z q)) * (w q - z q) := by simpa [div_mul_eq_mul_div] using h1
        _ = w q := div_mul_cancel₀ _ (ne_of_gt (hvpos q))
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    linarith [hw.2 q, hle]
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [div_mul_cancel₀ _ (ne_of_gt (hvpos s₀))]
    ring

/-- **A maximal zero set is not strictly dominated.** If `w` lies in the nonnegative
compatibility class and no class member has a zero set strictly containing `zeroSet w`, then
no class member is coordinatewise strictly below `w`.

This is the `wmax` forcing step: `hstrict` makes `w` strictly positive (hence
`zeroSet w = ∅`), while `exists_zeroCoordinate_of_strictlyDominated` produces a nonnegative
class member vanishing somewhere — a zero set strictly containing `zeroSet w`, contradicting
`hmax`. The instance `[Nonempty S]` is required: for an empty species set `∀ s, z s < w s` is
vacuous and the conclusion would be false. -/
theorem not_lt_of_mem_nonnegativeCompatibilityClass_of_maximal_zeroSet
    (N : Network S) [Nonempty S] {x₀ w z : Concentration S}
    (_hx₀ : x₀.Positive)
    (hw : w ∈ N.nonnegativeCompatibilityClass x₀)
    (hz : z ∈ N.nonnegativeCompatibilityClass x₀)
    (hmax : ∀ y ∈ N.nonnegativeCompatibilityClass x₀, ¬ (zeroSet w) ⊂ (zeroSet y))
    (_hzw : ∀ s, z s ≤ w s) :
    ¬ ∀ s, z s < w s := by
  intro hstrict
  have hwempty : zeroSet w = ∅ := by
    ext s
    constructor
    · intro hs
      have hws : w s = 0 := (mem_zeroSet_iff w s).mp hs
      exact absurd (hstrict s) (by rw [hws]; exact not_lt_of_ge (hz.2 s))
    · intro hs
      simp at hs
  obtain ⟨y, hy, s, hys⟩ :=
    N.exists_zeroCoordinate_of_strictlyDominated hw hz hstrict
  refine hmax y hy ?_
  rw [hwempty]
  refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.empty_subset _, ?_⟩
  intro hEq
  have hmem : s ∈ zeroSet y := (mem_zeroSet_iff y s).mpr hys
  have hmem' : s ∈ (∅ : Finset S) := hEq ▸ hmem
  simp at hmem'

/-! ### C. Maximal zero sets: the finite combinatorics -/

/-- **The maximal zero set of a nonempty family of nonnegative class points.** For any
nonempty family `Ξ` of nonnegative class points there are `wmax ∈ Ξ` and `Pmax := zeroSet wmax`
such that

* every `z ∈ Ξ` has `|zeroSet z| ≤ |Pmax|` (the `hzcard` clause), and
* every `z ∈ Ξ` vanishing on all of `Pmax` vanishes *exactly* on `Pmax` (the `hmaxExact`
  clause).

The first clause is maximum-cardinality, obtained by taking an argmax of `card` over the
(finite) set of zero sets realised in `Ξ`; the second is `Finset.Subset.antisymm` applied to
the two inclusions. This is the purely combinatorial core of
`CRNT.Dynamics.GACOmegaPositive.exists_maximal_zeroSet_omegaPoint`, proved for an arbitrary
family with no ω-limit-set or dynamical machinery. -/
theorem exists_maximal_zeroSet (N : Network S) {x₀ : Concentration S}
    {Ξ : Set (Concentration S)} (_hΞ : ∀ z ∈ Ξ, z ∈ N.nonnegativeCompatibilityClass x₀)
    (hne : Ξ.Nonempty) :
    ∃ (Pmax : Finset S) (wmax : Concentration S), wmax ∈ Ξ ∧
      (∀ s, s ∈ Pmax ↔ wmax s = 0) ∧
      (∀ z ∈ Ξ, (zeroSet z).card ≤ Pmax.card) ∧
      (∀ z ∈ Ξ, (∀ s ∈ Pmax, z s = 0) → ∀ s, z s = 0 ↔ s ∈ Pmax) := by
  classical
  obtain ⟨z₀, hz₀⟩ := hne
  -- the finite set of zero sets realised in `Ξ`, as a subfamily of the powerset of `univ`
  set realized : Finset (Finset S) :=
    Finset.univ.powerset.filter (fun t => ∃ z ∈ Ξ, zeroSet z = t) with hrealized
  have hrealized_mem : ∀ t : Finset S, t ∈ realized ↔ t ⊆ (Finset.univ : Finset S) ∧
      ∃ z ∈ Ξ, zeroSet z = t := by
    intro t
    rw [hrealized, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨Finset.mem_powerset.mp h.1, h.2⟩
    · intro h
      exact ⟨Finset.mem_powerset.mpr h.1, h.2⟩
  have hne' : realized.Nonempty := by
    refine ⟨zeroSet z₀, ?_⟩
    rw [hrealized_mem]
    exact ⟨Finset.subset_univ _, z₀, hz₀, rfl⟩
  obtain ⟨Pmax, hPmax, hmax⟩ := Finset.exists_max_image realized (fun t => t.card) hne'
  obtain ⟨-, wmax, hwmaxΞ, hwmaxzero⟩ := (hrealized_mem Pmax).mp hPmax
  have hPmax' : zeroSet wmax = Pmax := hwmaxzero
  have hmem : ∀ u ∈ Ξ, zeroSet u ∈ realized := by
    intro u hu
    rw [hrealized_mem]
    exact ⟨Finset.subset_univ _, u, hu, rfl⟩
  refine ⟨Pmax, wmax, hwmaxΞ, ?_, fun u hu => hmax _ (hmem u hu), ?_⟩
  · rw [← hPmax']
    exact mem_zeroSet_iff wmax
  · intro u hu hvanish
    have hsub : Pmax ⊆ zeroSet u := by
      intro s hs
      rw [mem_zeroSet_iff u s]
      exact hvanish s hs
    have heq : zeroSet u = Pmax :=
      (Finset.eq_of_subset_of_card_le hsub (hmax _ (hmem u hu))).symm
    rw [← heq]
    exact fun s => (mem_zeroSet_iff u s).symm

end Network
end CRNT