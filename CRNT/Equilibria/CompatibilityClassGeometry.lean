import CRNT.Equilibria.CompatibilityClass
import CRNT.Geometry.CompatibilityFaces
import CRNT.Geometry.ConservativeCompatibility
import CRNT.Dynamics.SiphonConservation
import CRNT.Stoich.Subspace
import Mathlib.Analysis.Convex.Basic

/-!
# Stoichiometric compatibility classes: affine structure, convexity, and face combinatorics

This module completes the affine picture of the compatibility class
`C(x₀) = x₀ + N.stoichSubspace` — the object the ω-limit-set hypothesis `hωaff` of
`CRNT.Dynamics.HighCodimensionSiphonFace` confines the orbit to — and formalizes the
face combinatorics that the `wmax` / `Pmax` package consumes.

`CRNT.Geometry.ConservativeCompatibility` already supplies closedness and
`CRNT.Geometry.CompatibilityFaces` supplies the conservation-law *exclusion* of a coordinate
face. What is missing, and proved here, is the *affine structure* of the class itself
(section A) and the *order-theoretic* content of the maximal-face mechanism (sections B–C).

## Contents

**A. The class is an affine subspace, and it is convex.**

* `stoichCompatible_iff_exists_sub` : `N.StoichCompatible x₀ x ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v`,
  the literal affine-span reading of the definition.
* `mem_compatibilityClass_iff_exists_sub` : the same for the class itself.
* `stoichCompatible_smul_add` : closure under `x₀ + a • v` for `v ∈ S(N)`.
* `stoichCompatible_segment` : the segment from `x₀` to any compatible `x` is compatible.
* `compatibilityClass_isConvex`, `nonnegativeCompatibilityClass_isConvex`,
  `positiveCompatibilityClass_isConvex` : the class, its nonnegative part
  (`N.nonnegativeCompatibilityClass`, from `CRNT.Geometry.ConservativeCompatibility`) and its
  positive part (`N.positiveCompatibilityClass` = `{x | N.StoichCompatible x₀ x ∧ x.Positive}`,
  whose second component is `x.Positive`, **not** `x.Nonnegative`) are convex. (Closedness was
  already available; convexity was not.)
* `stoichCompatible_of_convex_combination` : the general two-point combination form.

**B. Zero sets of class points and the antitone engine.**

* `zeroSet`, `mem_zeroSet_iff`.
* `zeroSet_antitone_of_le` : `z.Nonnegative` together with `z ≤ w` coordinatewise gives
  `w.zeroSet ⊆ z.zeroSet`. This single lemma is the engine of the whole `Pmax` package.
* `zeroSet_ssubset_of_lt_of_zero` : **the strict version.** If `z` is nonnegative with `z ≤ w`
  and `z s₀ = 0 < w s₀` at *some* coordinate `s₀`, then `(Concentration.zeroSet w) ⊂ (Concentration.zeroSet z)`:
  `s₀` lies in `z`'s zero set but not in `w`'s.
* `not_zeroSet_ssubset_of_maximal` : the `Pmax`-maximality engine — strict domination at a shared
  zero is impossible for a maximal zero set.

**C. Maximal zero sets — the finite combinatorics behind `exists_maximal_zeroSet_omegaPoint`.**

* `exists_maximal_zeroSetOf_card_le` : **the maximum-cardinality lemma, in the exact shape of
  `hmaxExact`.** Given a family `Ξ` of class points, a set `Pmax` with `|(Concentration.zeroSet u)| ≤ |Pmax|` for
  every `u ∈ Ξ`, and a `z ∈ Ξ` vanishing on all of `Pmax`, then `(Concentration.zeroSet z) = Pmax` — i.e. `z`
  vanishes exactly on `Pmax`. This is pure `Finset.card` combinatorics on two inclusions; it has
  no ω-limit-set or dynamical hypotheses, so it is reusable by any `Pmax`-packaging route.
* `card_zeroSet_le_of_card_le` : the `hzcard` clause in isolation.
* `exists_maximalCard_zeroSet` : for a nonempty family of class points there is a member of
  **maximum** zero-set cardinality (via well-ordering of `ℕ`, since `Concentration S = S → ℝ` has
  no `Fintype` instance). This supplies the `wmax`/`Pmax` witness pair for any set-theoretic family.
* `exists_maximal_zeroSet_package` : the four-clause package (`wmax ∈ Ξ`, `Pmax = zeroSet wmax`,
  `hzcard`, `hmaxExact`) for an arbitrary nonempty family of class points. Combining it with
  `Ξ := omegaLimit atTop ϕ {x₀}` gives a route to
  `Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`'s hypotheses that needs no
  dynamics.

**D. Worked example (non-vacuity).**

`exampleAtoB` is the two-species single-reaction network `A → B` over `S = Fin 2`. Verified:
`stoichRank = 1`; the class of `(1,1)` contains `(1,1) + t • (-1,1)` for every real `t`;
`(0,2)` is a nonnegative class point whose zero set is exactly `{0}`; the positive part of the
class is nonempty; `{0}` is properly contained in the zero set of `(0,0)` (the instance of
`zeroSet_ssubset_of_lt_of_zero` at `s₀ = 1`); and no conservation law is supported on `{1}` (a law
`(0,w)` supported there would satisfy `⟨(0,w),(-1,1)⟩ = -w = 0`, contradicting `w 1 > 0`), so the
face is not excluded by conservation. All by `simp`, `decide` and elementary arithmetic.

Depends on: `CRNT.Equilibria.CompatibilityClass`,
`CRNT.Geometry.CompatibilityFaces`, `CRNT.Geometry.ConservativeCompatibility`,
`CRNT.Dynamics.SiphonConservation`, `CRNT.Stoich.Subspace`, Mathlib `Analysis.Convex`.
-/

namespace CRNT

namespace Concentration

/-- The zero set of a concentration: the species whose coordinate vanishes. -/
noncomputable def zeroSet {S : Type} [DecidableEq S] [Fintype S] (x : Concentration S) :
    Finset S :=
  Finset.univ.filter fun s => x s = 0

@[simp] theorem mem_zeroSet_iff {S : Type} [DecidableEq S] [Fintype S]
    (x : Concentration S) (s : S) :
    s ∈ x.zeroSet ↔ x s = 0 := by simp [zeroSet]

end Concentration

open Concentration


namespace Network

open scoped BigOperators

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### A. The compatibility class is an affine subspace -/

/-- **The affine-span reading of compatibility.** A point is compatible with `x₀` exactly when it
is `x₀ + v` for some stoichiometric displacement `v`. -/
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
    have : x₀ + v - x₀ = v := by
      funext s
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [this]
    exact hv

/-- The same statement for the class itself. -/
theorem mem_compatibilityClass_iff_exists_sub (N : Network S) (x₀ x : Concentration S) :
    x ∈ N.compatibilityClass x₀ ↔ ∃ v ∈ N.stoichSubspace, x = x₀ + v := by
  rw [mem_compatibilityClass]
  exact N.stoichCompatible_iff_exists_sub x₀ x

/-- **The reference point is in its own class.** -/
theorem mem_compatibilityClass_self (N : Network S) (x₀ : Concentration S) :
    x₀ ∈ N.compatibilityClass x₀ := StoichCompatible.refl N x₀

/-- **Rays out of the reference point stay in the class.** For `v ∈ N.stoichSubspace` and any real
`a`, `x₀ + a • v` is compatible with `x₀`. -/
theorem stoichCompatible_smul_add (N : Network S) {x₀ : Concentration S} (v : S → ℝ)
    (hv : v ∈ N.stoichSubspace) (a : ℝ) : N.StoichCompatible x₀ (x₀ + a • v) :=
  (N.stoichCompatible_iff_exists_sub x₀ (x₀ + a • v)).mpr
    ⟨a • v, N.stoichSubspace.smul_mem a hv, rfl⟩

/-- **The general two-point combination form.** If `x` and `y` are both compatible with `x₀`
and `a + b = 1`, then so is `a • x + b • y`.  This is what makes the class an *affine* subspace
rather than merely a translate-invariant set.

The weight condition `a + b = 1` is necessary: `a • x + b • y = x₀ + (a+b-1) • x₀ + (a • v₁ + b • v₂)`
for displacements `v₁, v₂ ∈ S(N)`, and `(a+b-1) • x₀` need not lie in the stoichiometric
subspace.  With arbitrary `a, b` the statement is false already for `x₀ = (1,1)` and
`a = 2`, `b = 0`. -/
theorem stoichCompatible_of_convex_combination (N : Network S) {x₀ x y : Concentration S}
    (hx : N.StoichCompatible x₀ x) (hy : N.StoichCompatible x₀ y) (a b : ℝ) (hab : a + b = 1) :
    N.StoichCompatible x₀ (a • x + b • y) :=
  (N.stoichCompatible_iff_exists_sub x₀ (a • x + b • y)).mpr
    ⟨a • (x - x₀) + b • (y - x₀),
      N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem a hx)
        (N.stoichSubspace.smul_mem b hy), by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      have h2 : a * x₀ s + b * x₀ s = x₀ s := by
        calc a * x₀ s + b * x₀ s = (a + b) * x₀ s := by ring
          _ = 1 * x₀ s := by rw [hab]
          _ = x₀ s := by ring
      linarith only [h2]⟩

/-- **Segments inside the class.** For `0 ≤ t ≤ 1` the point `(1-t) • x₀ + t • x` is compatible
with `x₀` whenever `x` is. -/
theorem stoichCompatible_segment (N : Network S) {x₀ x : Concentration S}
    (hx : N.StoichCompatible x₀ x) {t : ℝ} (_ht0 : 0 ≤ t) (_ht1 : t ≤ 1) :
    N.StoichCompatible x₀ ((1 - t) • x₀ + t • x) :=
  N.stoichCompatible_of_convex_combination (StoichCompatible.refl N x₀) hx (1 - t) t (by ring)

/-- **Convexity of the compatibility class.** -/
theorem compatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.compatibilityClass x₀) := by
  intro x hx y hy a b ha hb hab
  exact mem_compatibilityClass_iff_exists_sub N x₀ (a • x + b • y) |>.mpr
    ⟨a • (x - x₀) + b • (y - x₀),
      N.stoichSubspace.add_mem (N.stoichSubspace.smul_mem a hx)
        (N.stoichSubspace.smul_mem b hy), by
      funext s
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
      have h2 : a * x₀ s + b * x₀ s = x₀ s := by
        calc a * x₀ s + b * x₀ s = (a + b) * x₀ s := by ring
          _ = 1 * x₀ s := by rw [hab]
          _ = x₀ s := by ring
      linarith only [h2]⟩

/-- **Convexity of the nonnegative part of the class.** Pointwise nonnegativity is preserved by
nonnegative combinations; compatibility is handled by the affine-combination lemma. -/
theorem nonnegativeCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.nonnegativeCompatibilityClass x₀) := by
  intro x hx
  refine fun y hy a b ha hb hab => ⟨N.stoichCompatible_of_convex_combination hx.1 hy.1 a b hab, ?_⟩
  intro s
  have h1 := add_nonneg (mul_nonneg ha (hx.2 s)) (mul_nonneg hb (hy.2 s))
  simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using h1

/-- **Convexity of the positive part of the class.** `N.positiveCompatibilityClass x₀` is
`{x | N.StoichCompatible x₀ x ∧ x.Positive}`, so its members carry `x.Positive` — *strictly*
positive, not merely `x.Nonnegative`.  A nonnegative combination of two strictly positive points
with `a + b = 1` is again strictly positive: if `a = 0` the combination collapses to `y`; if
`a > 0` the `a`-term is already strictly positive and the `b`-term is nonnegative. -/
theorem positiveCompatibilityClass_isConvex (N : Network S) (x₀ : Concentration S) :
    Convex ℝ (N.positiveCompatibilityClass x₀) := by
  intro x hx
  obtain ⟨hcx, hpx⟩ := hx
  refine fun y hy a b ha hb hab => ?_
  obtain ⟨hcy, hpy⟩ := hy
  refine ⟨N.stoichCompatible_of_convex_combination hcx hcy a b hab, fun s => ?_⟩
  rcases ha.eq_or_lt with hzero | hapos
  · -- `a = 0`, so `b = 1` and the combination is `y` itself
    subst hzero
    have hb1 : b = 1 := by linarith
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_mul, zero_add, hb1,
      one_mul] using hpy s
  · have hpos : 0 < a * x s := mul_pos hapos (hpx s)
    have hnonneg : 0 ≤ b * y s := mul_nonneg hb ((hpy s).le)
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
      add_pos_of_pos_of_nonneg hpos hnonneg

/-! ### B. Zero sets and the antitone engine -/

/-- **The `Pmax` antitone engine.** If `z` is nonnegative and `z ≤ w` coordinatewise then
`w.zeroSet ⊆ z.zeroSet`.

The nonnegativity of `z` is load-bearing, not cosmetic: from `w s = 0` and `z s ≤ w s` one only
gets `z s ≤ 0`, and without `0 ≤ z s` nothing forces `z s = 0` (take `z ≡ -1`, `w ≡ 0`).  Every
use below ranges `z` over the nonnegative part of a compatibility class, so the hypothesis is
always available. -/
theorem zeroSet_antitone_of_le {z w : Concentration S} (hz : z.Nonnegative)
    (hzw : ∀ s, z s ≤ w s) :
    (Concentration.zeroSet w) ⊆ (Concentration.zeroSet z) := by
  intro s hs
  have hw0 : w s = 0 := (Concentration.mem_zeroSet_iff w s).mp hs
  rw [Concentration.mem_zeroSet_iff z s]
  refine le_antisymm (by linarith [hzw s, hw0]) (hz s)

/-- **Strict domination at one shared zero gives a proper inclusion of zero sets.** If `z` is
nonnegative, `z ≤ w` coordinatewise, and `z s₀ = 0 < w s₀` at some coordinate `s₀`, then
`s₀ ∈ (Concentration.zeroSet z)` while `s₀ ∉ (Concentration.zeroSet w)`; combined with
`zeroSet_antitone_of_le` this yields `(Concentration.zeroSet w) ⊂ (Concentration.zeroSet z)`.

Both extra hypotheses are needed.  The bare pair `z s₀ = 0`, `z s₀ < w s₀` says nothing about the
coordinates `s ≠ s₀`, where `z` may be nonzero or negative: with `z = (0, -1)`, `w = (1, -1)`,
`s₀ = 0` the hypotheses hold but `(Concentration.zeroSet w) = {1} ⊄ (Concentration.zeroSet z) = {0}`. -/
theorem zeroSet_ssubset_of_lt_of_zero {z w : Concentration S} {s₀ : S}
    (hz : z.Nonnegative) (hzw : ∀ s, z s ≤ w s) (hz₀ : z s₀ = 0) (hlt : z s₀ < w s₀) :
    (Concentration.zeroSet w) ⊂ (Concentration.zeroSet z) := by
  rw [hz₀] at hlt
  refine Finset.ssubset_iff_subset_ne.mpr ⟨zeroSet_antitone_of_le hz hzw, fun hEq => ?_⟩
  have hs₀z : s₀ ∈ Concentration.zeroSet z := (Concentration.mem_zeroSet_iff z s₀).mpr hz₀
  have hs₀w : s₀ ∉ Concentration.zeroSet w :=
    (Concentration.mem_zeroSet_iff w s₀).not.2 (ne_of_gt hlt)
  have hs₀w' : s₀ ∈ Concentration.zeroSet w := (Finset.ext_iff.mp hEq) s₀ |>.mpr hs₀z
  exact hs₀w hs₀w'

/-- **A maximal zero set is not strictly dominated.** If `w` lies in the nonnegative compatibility
class of a positive reference and no class member has a zero set strictly containing `(Concentration.zeroSet w)`,
then no class member is coordinatewise strictly below `w` at a coordinate where `w` vanishes. -/
theorem not_zeroSet_ssubset_of_maximal (N : Network S)
    {x₀ w z : Concentration S}
    (_hw : w ∈ N.nonnegativeCompatibilityClass x₀)
    (hz : z ∈ N.nonnegativeCompatibilityClass x₀)
    (hmax : ∀ y ∈ N.nonnegativeCompatibilityClass x₀, ¬ (Concentration.zeroSet w) ⊂ (Concentration.zeroSet y))
    (hdom : ∃ s, z s = 0 ∧ z s < w s) :
    ¬ ((Concentration.zeroSet w) ⊆ (Concentration.zeroSet z)) := by
  obtain ⟨s₀, hz₀, hlt⟩ := hdom
  rw [hz₀] at hlt
  intro hsub
  -- `hsub` together with `hdom` makes the inclusion proper: `s₀` lies in
  -- `(Concentration.zeroSet z)` but not in `(Concentration.zeroSet w)`, because `hdom` gives
  -- `z s₀ = 0 < w s₀`.
  have hs₀z : s₀ ∈ Concentration.zeroSet z := (Concentration.mem_zeroSet_iff z s₀).mpr hz₀
  have hs₀w : s₀ ∉ Concentration.zeroSet w :=
    (Concentration.mem_zeroSet_iff w s₀).not.2 (ne_of_gt hlt)
  have hne : (Concentration.zeroSet w) ≠ (Concentration.zeroSet z) := fun hEq =>
    hs₀w ((Finset.ext_iff.mp hEq) s₀ |>.mpr hs₀z)
  exact hmax z hz (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩)

/-! ### C. Maximal zero sets: the finite combinatorics -/

/-- **The maximum-cardinality lemma — the `hmaxExact` clause of hole A, in card form.**

Let `Ξ` be a family of class points, `Pmax` a species set, and suppose `|(Concentration.zeroSet u)| ≤ |Pmax|` for
every `u ∈ Ξ`.  Then any `z ∈ Ξ` that vanishes on all of `Pmax` has `(Concentration.zeroSet z) = Pmax`, i.e. it
vanishes **exactly** on `Pmax`.

The card bound reads `|zeroSet u| ≤ |Pmax|` — the direction `hzcard` uses.  The reverse bound,
`|Pmax| ≤ |zeroSet z|`, would only give an inclusion and would leave `zeroSet z` free to
*strictly contain* `Pmax`: with `z ≡ 0` on `S = Fin 2` and `Pmax = {0}` the reverse bound and
`Pmax ⊆ zeroSet z` both hold while `zeroSet z = {0, 1}`.

This is precisely the `hmaxExact` clause of
`Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`, with the ω-limit-set
quantifier replaced by an arbitrary family of nonnegative class points.  It is pure finite
combinatorics on `Finset.card`, so any `Pmax`-packaging route can invoke it. -/
theorem exists_maximal_zeroSetOf_card_le (N : Network S) {x₀ : Concentration S}
    {Ξ : Set (Concentration S)} {Pmax : Finset S} {z : Concentration S}
    (_hΞ : ∀ u ∈ Ξ, u ∈ N.nonnegativeCompatibilityClass x₀)
    (hcard_le : ∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ Pmax.card)
    (hzΞ : z ∈ Ξ)
    (hzvanish : ∀ s ∈ Pmax, z s = 0) :
    ∀ s, z s = 0 ↔ s ∈ Pmax := by
  have hzsub : Pmax ⊆ (Concentration.zeroSet z) := by
    intro s hs
    rw [Concentration.mem_zeroSet_iff]
    exact hzvanish s hs
  have hcard : (Concentration.zeroSet z).card ≤ Pmax.card := hcard_le z hzΞ
  -- `Pmax ⊆ zeroSet z` together with `|zeroSet z| ≤ |Pmax|` forces the two to coincide
  have heq : Pmax = Concentration.zeroSet z :=
    (Finset.eq_iff_card_le_of_subset hzsub).mp hcard
  intro s
  rw [heq, Concentration.mem_zeroSet_iff]

/-- **The `hzcard` clause in isolation.** Every zero set of the family has cardinality at most
`|Pmax|`. -/
theorem card_zeroSet_le_of_card_le {_x₀ : Concentration S}
    {Ξ : Set (Concentration S)} {Pmax : Finset S}
    (hcard_le : ∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ Pmax.card) :
    ∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ Pmax.card :=
  fun u hu => (hcard_le u hu)

/-- **Existence of a maximum-cardinality zero set in a nonempty family.** For any nonempty
family `Ξ` of class points there is `wmax ∈ Ξ` with `|(Concentration.zeroSet u)| ≤ |(Concentration.zeroSet wmax)|` for all
`u ∈ Ξ`.

This supplies the `wmax` / `Pmax` witness pair for a purely set-theoretic family: combine it with
`exists_maximal_zeroSetOf_card_le` at `Pmax := (Concentration.zeroSet wmax)`. -/
theorem exists_maximalCard_zeroSet {Ξ : Set (Concentration S)} (hne : Ξ.Nonempty) :
    ∃ wmax ∈ Ξ, ∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ (Concentration.zeroSet wmax).card := by
  classical
  -- `Concentration S = S → ℝ` has no `Fintype` instance, so `Ξ.toFinset` is unavailable.  The
  -- attained cardinalities are instead collected into a `Finset ℕ`: they are all `< |S| + 1`,
  -- so the finset is finite and nonempty, and its maximum is attained.
  have hbound : ∀ u ∈ Ξ, (Concentration.zeroSet u).card < Fintype.card S + 1 :=
    fun u _ => lt_of_le_of_lt (Finset.card_le_univ _) (Nat.lt_succ_self _)
  have hmem : ∀ u ∈ Ξ,
      (Concentration.zeroSet u).card ∈ Finset.range (Fintype.card S + 1) :=
    fun u hu => Finset.mem_range.2 (hbound u hu)
  obtain ⟨z₀, hz₀⟩ := hne
  have himg : (Finset.range (Fintype.card S + 1)).filter
      (fun n : ℕ => ∃ u ∈ Ξ, (Concentration.zeroSet u).card = n) |>.Nonempty :=
    ⟨(Concentration.zeroSet z₀).card,
      Finset.mem_filter.mpr ⟨hmem z₀ hz₀, z₀, hz₀, rfl⟩⟩
  obtain ⟨m, hm, hmax⟩ := Finset.exists_max_image _ id himg
  obtain ⟨wmax, hwmaxΞ, hwmaxcard⟩ := (Finset.mem_filter.mp hm).2
  refine ⟨wmax, hwmaxΞ, fun u hu => ?_⟩
  rw [hwmaxcard]
  exact hmax _ (Finset.mem_filter.mpr ⟨hmem u hu, u, hu, rfl⟩)

/-- **The full maximal-zero-set package for a nonempty family of class points.** There is
`wmax ∈ Ξ` and `Pmax := (Concentration.zeroSet wmax)` such that `|(Concentration.zeroSet u)| ≤ |Pmax|` for all `u ∈ Ξ`, and every
`u ∈ Ξ` vanishing on `Pmax` has `(Concentration.zeroSet u) = Pmax`.

This is the exact shape of the `wmax` / `Pmax` hypotheses of hole A (`hwmax`, `hzeroMax`,
`hmaxExact`, `hzcard`), with the ω-limit set replaced by an arbitrary family.  Instantiating at
`Ξ := omegaLimit atTop ϕ {x₀}` with the nonnegative clause supplied by `hωnn` + `hωaff` is
purely mechanical. -/
theorem exists_maximal_zeroSet_package (N : Network S) {x₀ : Concentration S}
    {Ξ : Set (Concentration S)} (hΞ : ∀ z ∈ Ξ, z ∈ N.nonnegativeCompatibilityClass x₀)
    (hne : Ξ.Nonempty) :
    ∃ (wmax : Concentration S) (Pmax : Finset S),
      wmax ∈ Ξ ∧
      (∀ s, s ∈ Pmax ↔ wmax s = 0) ∧
      (∀ u ∈ Ξ, (Concentration.zeroSet u).card ≤ Pmax.card) ∧
      (∀ u ∈ Ξ, (∀ s ∈ Pmax, u s = 0) → ∀ s, u s = 0 ↔ s ∈ Pmax) := by
  obtain ⟨wmax, hwmaxΞ, hcard_ge⟩ := exists_maximalCard_zeroSet hne
  refine ⟨wmax, (Concentration.zeroSet wmax), hwmaxΞ, Concentration.mem_zeroSet_iff wmax, hcard_ge, ?_⟩
  intro u hu hvanish
  exact N.exists_maximal_zeroSetOf_card_le hΞ (fun v hv => hcard_ge v hv) hu hvanish

/-! ### D. Worked example: the two-species network `A → B` -/

section Example

/-- The two-species single-reaction network `A → B` over `S = Fin 2` (species `0` is `A`,
species `1` is `B`). -/
def exampleAtoB : Network (Fin 2) where
  R := Unit
  decEqR := inferInstance
  fintypeR := inferInstance
  reaction := fun _ =>
    { source := fun s => if s = 0 then 1 else 0
      target := fun s => if s = 1 then 1 else 0 }

/-- The reaction vector of `A → B` is nonzero. -/
theorem exampleAtoB_reactionVector_ne_zero :
    (exampleAtoB.reactionVector () : Fin 2 → ℝ) ≠ 0 := by
  intro h
  have := congrFun h (1 : Fin 2)
  simp [exampleAtoB] at this

/-- **The stoichiometric subspace of `A → B` is the line `ℝ ∙ (-1,1)`.** -/
theorem exampleAtoB_stoichSubspace :
    exampleAtoB.stoichSubspace =
      Submodule.span ℝ {(exampleAtoB.reactionVector () : Fin 2 → ℝ)} := by
  apply le_antisymm
  · apply Submodule.span_le.2
    rintro x ⟨r, rfl⟩
    exact Submodule.subset_span rfl
  · apply Submodule.span_le.2
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact exampleAtoB.reactionVector_mem_stoichSubspace ()

/-- **The stoichiometric rank of `A → B` is one.** -/
theorem exampleAtoB_stoichRank : exampleAtoB.stoichRank = 1 := by
  rw [Network.stoichRank, exampleAtoB_stoichSubspace,
    finrank_span_singleton exampleAtoB_reactionVector_ne_zero]

/-- **The direction `(-1,1)` really is a reaction vector, so the class of `(1,1)` really does
contain the segment `(1-t, 1+t)`**: compatibility is non-vacuous here. -/
theorem exampleAtoB_stoichCompatible_segment :
    ∀ t : ℝ, exampleAtoB.StoichCompatible (fun _ => (1 : ℝ))
      (fun s => if s = (0 : Fin 2) then 1 - t else 1 + t) := by
  intro t
  refine exampleAtoB.stoichCompatible_iff_exists_sub _ _ |>.mpr
    ⟨t • (exampleAtoB.reactionVector () : Fin 2 → ℝ),
      exampleAtoB.stoichSubspace.smul_mem t
        (exampleAtoB.reactionVector_mem_stoichSubspace ()), ?_⟩
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  by_cases hs0 : s = 0
  · subst hs0
    simp [exampleAtoB]
    ring
  · have hs1 : s = (1 : Fin 2) := Fin.eq_one_of_ne_zero s hs0
    subst hs1
    simp [exampleAtoB]

/-- `(1,1)` and `(0,2)` lie in the same stoichiometric compatibility class of `A → B` — the
concrete instance of the segment lemma at `t = 1`. -/
theorem exampleAtoB_stoichCompatible_01 :
    exampleAtoB.StoichCompatible (fun _ => (1 : ℝ))
      (fun s => if s = (0 : Fin 2) then 0 else 2) := by
  have h := exampleAtoB_stoichCompatible_segment (1 : ℝ)
  convert h using 1
  funext s
  by_cases hs0 : s = 0
  · simp [hs0]
  · have hs1 : s = (1 : Fin 2) := Fin.eq_one_of_ne_zero s hs0
    simp [hs1]
    ring

/-- **The class of `(1,1)` really meets the boundary**: `(0,2)` is a nonnegative class point. -/
theorem exampleAtoB_nonnegClass_mem :
    (fun s => if s = (0 : Fin 2) then 0 else 2) ∈
      exampleAtoB.nonnegativeCompatibilityClass (fun _ => (1 : ℝ)) :=
  ⟨exampleAtoB_stoichCompatible_01, fun s => by by_cases hs0 : s = 0 <;> simp [hs0]⟩

/-- **The positive part of the class of `(1,1)` is nonempty** — witnessed by `(1,1)`. -/
theorem exampleAtoB_posClass_mem :
    (fun _ => (1 : ℝ)) ∈ exampleAtoB.positiveCompatibilityClass (fun _ => (1 : ℝ)) :=
  ⟨StoichCompatible.refl exampleAtoB _, fun _ => by norm_num⟩

/-- The zero set of `(0,2)` is exactly `{0}` — species `0` is the vanishing coordinate. -/
theorem exampleAtoB_zeroSet :
    Concentration.zeroSet (fun s => if s = (0 : Fin 2) then 0 else 2) = {0} := by
  ext s
  rw [Concentration.mem_zeroSet_iff, Finset.mem_singleton]
  by_cases hs0 : s = 0
  · simp [hs0]
  · have hs1 : s = (1 : Fin 2) := Fin.eq_one_of_ne_zero s hs0
    simp [hs1]


/-- **The strict-domination lemma at the concrete point**: with `w = (0,2)`, whose zero set is
`{0}`, and `z = (0,0)`, whose zero set is `{0,1}`, the zero set of `w` is *properly* contained
in the zero set of `z` — indeed at `s₀ = 1` we have `z s₀ = 0 < w s₀ = 2`, and `z` is nonnegative
with `z ≤ w` coordinatewise.  This is the concrete instance of `zeroSet_ssubset_of_lt_of_zero`
and shows its hypotheses are satisfiable. -/
theorem exampleAtoB_zeroSet_ssubset :
    ({0} : Finset (Fin 2)) ⊂ Concentration.zeroSet (fun _ : Fin 2 => (0 : ℝ)) := by
  have hgen : Concentration.zeroSet (fun s => if s = (0 : Fin 2) then 0 else 2)
      ⊂ Concentration.zeroSet (fun _ : Fin 2 => (0 : ℝ)) :=
    zeroSet_ssubset_of_lt_of_zero (fun _ => le_rfl)
      (fun s => by by_cases hs0 : s = 0 <;> simp [hs0])
      rfl (show 0 < ((fun s => if s = (0 : Fin 2) then 0 else 2) (1 : Fin 2)) by norm_num)
  rwa [exampleAtoB_zeroSet] at hgen

/-- **No conservation law is supported on `{1}`**, so the face `{1}` is not excluded from the class
of `(1,1)` by conservation: a law `(0, w)` supported on `{1}` satisfies
`⟨(0,w), (-1,1)⟩ = 0`, forcing `w = 0`, contradicting `w 1 > 0`. -/
theorem exampleAtoB_no_conservationLaw_on_1 :
    ¬ exampleAtoB.CarriesPositiveConservationLaw ({1} : Finset (Fin 2)) := by
  rintro ⟨w, hw, hnn, hsupp⟩
  -- `w 0 = 0` because `0 ≤ w 0` and `w 0` is not strictly positive off `{1}`
  have hw0 : w (0 : Fin 2) = 0 := by
    refine le_antisymm (le_of_not_gt ?_) (hnn 0)
    intro h
    have hmem : (0 : Fin 2) ∈ ({1} : Finset (Fin 2)) := (hsupp 0).mp h
    simp at hmem
  have hw1 : 0 < w (1 : Fin 2) := (hsupp 1).mpr (by simp)
  -- the reaction vector is `(-1, 1)`, so orthogonality reads `-w 0 + w 1 = 0`
  have h0 : exampleAtoB.reactionVector () (0 : Fin 2) = -1 := by
    simp [exampleAtoB]
  have h1 : exampleAtoB.reactionVector () (1 : Fin 2) = 1 := by
    simp [exampleAtoB]
  have horth := exampleAtoB.conservationLaw_iff_mem_orthSum w
  have hsum : ∑ s : Fin 2, w s * exampleAtoB.reactionVector () s = 0 := horth.2 hw ()
  have htwo : (w 0 * exampleAtoB.reactionVector () 0
      + w 1 * exampleAtoB.reactionVector () 1) = 0 := by
    rw [← hsum]
    simp
  rw [h0, h1] at htwo
  linarith

end Example

end Network
end CRNT