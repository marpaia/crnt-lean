import CRNT.Dynamics.FaceDirectionCone

/-!
# The blueprint clauses as explicit inequalities in the concentrations

`CRNT.Network.exists_positive_omegaPoint_of_tiled_faceCores` states its three clauses in terms of
`euclideanStoichState`, `faceLogPart` and `minMaxBarrier` — abstract objects in the intrinsic
stoichiometric space.  For actually *constructing* a blueprint one wants them as inequalities in
the concentrations.  This module supplies that translation.

## The key identity

For `m` in the stoichiometric subspace and any `z`,

```
⟪m, euclideanStoichStateL z⟫ = ∑ s, (m : EuclideanSpace ℝ S) s * z s.
```

The orthogonal projection can be moved onto `m`, where it acts as the identity, so the inner
product never sees the projection at all.  Three consequences:

* the guarded region is a plain **union of halfspaces in concentration space**
  (`minMaxBarrier_euclideanStoichState_le_iff`): `∃ k, -(∑ s, m k s * x s) - b k ≤ R`;
* the angular tile condition is a condition on the weighted log-deviations over the face
  (`inner_faceLogPart_eq_sum`);
* the off-face bound is a condition on the log-deviations off the face
  (`inner_offFaceLogPart_eq_sum`).

## What this buys

`coordinate_floor_of_tilewise` reduces the separation clause `hsep` — the one asking that the
guarded region stay off the boundary of the positive orthant — to finitely many *elementary*
questions, one per (species, tile) pair: does the single linear inequality
`-(∑ u, m k u * x u) - b k ≤ R`, together with positivity and compatibility with `x₀`, force
`x s ≥ ε`?  No cones, no projections, no logarithms.

A structural remark that falls out of this form and is worth recording: a single halfspace
`∑ u, a u * x u ≥ η` with `a ≥ 0` bounds a *combination* of coordinates from below, never an
individual one, so one tile can never satisfy `hsep` for every species by itself.  Several tiles are
needed for the separation clause too, not only for the cone clause `hnear`.  That matches the
staircase shape of Craciun's surface, which has one face nearly orthogonal to each coordinate
direction.

Nothing here is an axiom or a `sorry`.

Depends on: `CRNT.Dynamics.FaceDirectionCone`.
-/

namespace CRNT
namespace Network

open Filter
open scoped RealInnerProductSpace NNReal

variable {S : Type} [DecidableEq S] [Fintype S]

/-! ### The key identity -/

/-- **Pairing with a transported vector is a plain weighted sum.**  The orthogonal projection moves
onto `m`, where it is the identity because `m` already lies in the subspace. -/
theorem inner_euclideanStoichStateL_eq_sum (N : Network S)
    (m : N.euclideanStoichSubspace) (z : S → ℝ) :
    ⟪m, N.euclideanStoichStateL z⟫ = ∑ s, (m : EuclideanSpace ℝ S) s * z s := by
  have hcoe : ((N.euclideanStoichStateL z : N.euclideanStoichSubspace) : EuclideanSpace ℝ S)
      = N.euclideanStoichSubspace.starProjection (CRNT.toEuclid z) := by
    simp only [Network.euclideanStoichStateL, ContinuousLinearMap.coe_comp, Function.comp_apply,
      Submodule.coe_orthogonalProjectionOnto_apply]
    rfl
  have h1 : ⟪m, N.euclideanStoichStateL z⟫
      = ⟪(m : EuclideanSpace ℝ S),
          N.euclideanStoichSubspace.starProjection (CRNT.toEuclid z)⟫ := by
    rw [← hcoe]; rfl
  rw [h1, ← Submodule.inner_starProjection_left_eq_right,
    Submodule.starProjection_eq_self_iff.mpr m.2]
  simp only [PiLp.inner_apply, RCLike.inner_apply, CRNT.toEuclid_apply, starRingEnd_apply,
    star_trivial]
  exact Finset.sum_congr rfl fun s _ => mul_comm _ _

theorem inner_euclideanStoichState_eq_sum (N : Network S)
    (m : N.euclideanStoichSubspace) (x : Concentration S) :
    ⟪m, N.euclideanStoichState x⟫ = ∑ s, (m : EuclideanSpace ℝ S) s * x s :=
  N.inner_euclideanStoichStateL_eq_sum m x

/-- The angular tile condition, explicitly: a weighted sum of log-deviations over the face. -/
theorem inner_faceLogPart_eq_sum (N : Network S) (m : N.euclideanStoichSubspace) (P : Finset S)
    (xstar x : Concentration S) :
    ⟪m, N.faceLogPart P xstar x⟫
      = ∑ s ∈ P, (m : EuclideanSpace ℝ S) s * (Real.log (xstar s) - Real.log (x s)) := by
  rw [Network.faceLogPart, N.inner_euclideanStoichStateL_eq_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => s ∈ P)]
  have h2 : ∑ s ∈ Finset.univ.filter (fun s => ¬ s ∈ P),
      (m : EuclideanSpace ℝ S) s
        * (if s ∈ P then Real.log (xstar s) - Real.log (x s) else 0) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    have : ¬ s ∈ P := (Finset.mem_filter.1 hs).2
    simp [this]
  rw [h2, add_zero]
  refine Finset.sum_congr (by ext s; simp) fun s hs => ?_
  simp [hs]

/-- The off-face bound, explicitly. -/
theorem inner_offFaceLogPart_eq_sum (N : Network S) (m : N.euclideanStoichSubspace) (P : Finset S)
    (xstar x : Concentration S) :
    ⟪m, N.offFaceLogPart P xstar x⟫
      = ∑ s ∈ Finset.univ.filter (fun s => ¬ s ∈ P),
          (m : EuclideanSpace ℝ S) s * (Real.log (xstar s) - Real.log (x s)) := by
  rw [Network.offFaceLogPart, N.inner_euclideanStoichStateL_eq_sum]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s => s ∈ P)]
  have h1 : ∑ s ∈ Finset.univ.filter (fun s => s ∈ P),
      (m : EuclideanSpace ℝ S) s
        * (if s ∈ P then 0 else Real.log (xstar s) - Real.log (x s)) = 0 := by
    refine Finset.sum_eq_zero fun s hs => ?_
    have : s ∈ P := (Finset.mem_filter.1 hs).2
    simp [this]
  rw [h1, zero_add]
  refine Finset.sum_congr rfl fun s hs => ?_
  have : ¬ s ∈ P := (Finset.mem_filter.1 hs).2
  simp [this]

/-! ### The guarded region is a union of halfspaces -/

variable {ι' : Type*} [Fintype ι'] [Nonempty ι']

/-- **The guarded region, explicitly.**  A point is inside the min-max region exactly when it
satisfies one of finitely many linear inequalities in the concentrations. -/
theorem minMaxBarrier_euclideanStoichState_le_iff (N : Network S)
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R : ℝ} {x : Concentration S} :
    PolyhedralBarrier.minMaxBarrier (fun (k : ι') (_ : Unit) => innerSL ℝ (-m k))
        (fun k _ => b k) (N.euclideanStoichState x) ≤ R
      ↔ ∃ k : ι', -(∑ s, (m k : EuclideanSpace ℝ S) s * x s) - b k ≤ R := by
  rw [PolyhedralBarrier.minMaxBarrier_le_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [PolyhedralBarrier.barrier_unique] at hk
    have hval : innerSL ℝ (-m k) (N.euclideanStoichState x)
        = -(∑ s, (m k : EuclideanSpace ℝ S) s * x s) := by
      rw [← N.inner_euclideanStoichState_eq_sum (m k)]
      simp [innerSL_apply_apply]
    rwa [hval] at hk
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    rw [PolyhedralBarrier.barrier_unique]
    have hval : innerSL ℝ (-m k) (N.euclideanStoichState x)
        = -(∑ s, (m k : EuclideanSpace ℝ S) s * x s) := by
      rw [← N.inner_euclideanStoichState_eq_sum (m k)]
      simp [innerSL_apply_apply]
    rwa [hval]

/-! ### Reducing the separation clause -/

/-- **Separation, tile by tile.**  The `hsep` clause of
`Network.exists_positive_omegaPoint_of_tiled_faceCores` follows from finitely many elementary
statements, one per species and tile: that a *single* linear inequality in the concentrations,
together with positivity and compatibility with `x₀`, forces a positive floor on that coordinate.

Given those, take the minimum of the floors over the finitely many tiles. -/
theorem coordinate_floor_of_tilewise (N : Network S)
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R : ℝ} {x₀ : Concentration S}
    (h : ∀ (s : S) (k : ι'), ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive →
      N.StoichCompatible x₀ x →
      -(∑ u, (m k : EuclideanSpace ℝ S) u * x u) - b k ≤ R → ε ≤ x s) :
    ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive → N.StoichCompatible x₀ x →
      PolyhedralBarrier.minMaxBarrier (fun (k : ι') (_ : Unit) => innerSL ℝ (-m k))
        (fun k _ => b k) (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
  intro s
  choose f hfpos hfbound using h s
  refine ⟨Finset.univ.inf' Finset.univ_nonempty f, ?_, ?_⟩
  · rw [Finset.lt_inf'_iff]
    exact fun k _ => hfpos k
  · intro x hxpos hxclass hxregion
    obtain ⟨k, hk⟩ := N.minMaxBarrier_euclideanStoichState_le_iff.mp hxregion
    exact le_trans (Finset.inf'_le f (Finset.mem_univ k)) (hfbound k x hxpos hxclass hk)

/-! ### The convex case: intersections of halfspaces

A `barrier` (max of affine pieces) guards the *intersection* of the halfspaces, and that is the
shape the zero-separating surface actually has: the region above a convex decreasing staircase is
the intersection of the halfspaces above its faces.  Craciun's two-dimensional picture (v3
Figure 3(d)) is exactly of this kind.

The separation clause is far easier for an intersection than for a union: a point of the region
satisfies *every* halfspace, so **one** halfspace per species suffices to force that coordinate's
floor.  For a union every halfspace would have to force every coordinate — see the remark in the
module docstring.

Note this does not conflict with `CRNT.Geometry.ConvexBarrierObstruction`, which rules out a
*globally homogeneous* convex barrier over the arrangement fan in dimension `≥ 3`.  Craciun's
surface lives in a bounded window of log-coordinates and is not homogeneous. -/

/-- **The guarded region of a convex barrier, explicitly**: the intersection of finitely many
halfspaces in the concentrations. -/
theorem barrier_euclideanStoichState_le_iff (N : Network S)
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R : ℝ} {x : Concentration S} :
    PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b (N.euclideanStoichState x) ≤ R
      ↔ ∀ k : ι', -(∑ s, (m k : EuclideanSpace ℝ S) s * x s) - b k ≤ R := by
  have hval : ∀ k : ι', innerSL ℝ (-m k) (N.euclideanStoichState x)
      = -(∑ s, (m k : EuclideanSpace ℝ S) s * x s) := by
    intro k
    rw [← N.inner_euclideanStoichState_eq_sum (m k)]
    simp [innerSL_apply_apply]
  rw [PolyhedralBarrier.barrier_le_iff]
  simp only [hval]

/-- **A halfspace with a dominant coefficient forces a coordinate floor.**

If `a s > 0` and the level `η` exceeds what the other coordinates can contribute, then the
halfspace `η ≤ ∑ u, a u * x u` pins `x s` away from zero.

The contribution bound uses the **positive parts** `max (a u) 0`, not `|a u|`.  That sharpening is
not cosmetic: with `|a u|` the separation clause becomes unsatisfiable on any network carrying the
all-ones conservation law.  There every `m` in the stoichiometric subspace has `∑_u m_u = 0`, which
forces `⟨m, x⟩ ≤ (M/2) ∑_u |m_u|` on the box, and combining that with
`η > M ∑_{u ≠ s} |m_u|` yields `m_s > ∑_{u ≠ s} |m_u| ≥ m_s`.  With positive parts the same
comparison reduces to `m_s > 0`, which is exactly `hpos`.  Since `x` is nonnegative, only the
positive coefficients can push the sum up, so the sharper bound is the correct one. -/
theorem le_of_halfspace_of_dominant {a : S → ℝ} {η M : ℝ} {s : S}
    (hs : 0 < a s) {x : Concentration S}
    (hx : ∀ u, 0 ≤ x u) (hxM : ∀ u, x u ≤ M)
    (hhalf : η ≤ ∑ u, a u * x u) :
    (η - M * ∑ u ∈ Finset.univ.erase s, max (a u) 0) / a s ≤ x s := by
  have hsplit : ∑ u, a u * x u
      = a s * x s + ∑ u ∈ Finset.univ.erase s, a u * x u :=
    (Finset.add_sum_erase Finset.univ (fun u => a u * x u) (Finset.mem_univ s)).symm
  have hrest : ∑ u ∈ Finset.univ.erase s, a u * x u
      ≤ M * ∑ u ∈ Finset.univ.erase s, max (a u) 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    calc a u * x u ≤ max (a u) 0 * x u :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (hx u)
      _ ≤ max (a u) 0 * M := mul_le_mul_of_nonneg_left (hxM u) (le_max_right _ _)
      _ = M * max (a u) 0 := mul_comm _ _
  rw [div_le_iff₀ hs]
  nlinarith [hsplit, hrest, hhalf]

/-- **Separation for a convex barrier.**  If every species has *some* piece whose coefficient at
that species is positive and whose level is high enough relative to the orbit bound `M`, then the
guarded region keeps every coordinate away from zero.

The hypotheses are elementary inequalities in the coefficients: no cones, projections or
logarithms.  Together with `Network.barrier_le_of_toric_descent` this discharges the separation
clause of a blueprint. -/
theorem coordinate_floor_of_dominant_barrier (N : Network S)
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R M : ℝ}
    (piece : S → ι')
    (hpos : ∀ s : S, 0 < ((m (piece s) : EuclideanSpace ℝ S) s))
    (hlevel : ∀ s : S,
      M * (∑ u ∈ Finset.univ.erase s, max ((m (piece s) : EuclideanSpace ℝ S) u) 0)
        < -(R + b (piece s))) :
    ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, (∀ u, 0 ≤ x u) → (∀ u, x u ≤ M) →
      PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
        (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
  intro s
  set k := piece s with hk
  refine ⟨(-(R + b k) - M * ∑ u ∈ Finset.univ.erase s,
      max ((m k : EuclideanSpace ℝ S) u) 0) / ((m k : EuclideanSpace ℝ S) s), ?_, ?_⟩
  · exact div_pos (by linarith [hlevel s]) (hpos s)
  · intro x hx hxM hxregion
    have hhalf : -(R + b k) ≤ ∑ u, (m k : EuclideanSpace ℝ S) u * x u := by
      have := N.barrier_euclideanStoichState_le_iff.mp hxregion k
      linarith
    exact le_of_halfspace_of_dominant (hpos s) hx hxM hhalf

/-! ### Regression guard: why the floor condition must use positive parts

`le_of_halfspace_of_dominant` bounds the contribution of the other coordinates by their **positive
parts**.  An earlier version used absolute values, and the theorems below prove that version
unsatisfiable, so that reverting the sharpening would leave a proof of its own vacuity in the tree.

The setting is any network carrying the all-ones conservation law: then every `m` in the
stoichiometric subspace has `∑_u m_u = 0`, and that is exactly the class for which the bounded-class
hypothesis `hMclass` is automatic.  On such a vector, `⟨m, x⟩ ≤ M ∑_{u ≠ s} |m_u|` holds for *every*
`x` in the box, so no level `η` can satisfy both `η > M ∑_{u ≠ s} |m_u|` (the old floor condition)
and `η ≤ ⟨m, x⟩` (the start condition).

With positive parts the corresponding comparison reduces to `0 < m s`, which is exactly `hpos`. -/

/-- On a coordinate-sum-zero vector, the positive part is at most the off-`s` absolute sum. -/
theorem sum_posPart_le_erase_abs {a : S → ℝ} {s : S} (hs : 0 < a s) (hsum : ∑ u, a u = 0) :
    ∑ u, max (a u) 0 ≤ ∑ u ∈ Finset.univ.erase s, |a u| := by
  have hsplitpn : ∀ u : S, a u = max (a u) 0 - max (-a u) 0 := by
    intro u
    rcases le_or_gt 0 (a u) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith)]; ring
    · rw [max_eq_right h.le, max_eq_left (by linarith)]; ring
  have hpn : ∑ u, max (a u) 0 = ∑ u, max (-a u) 0 := by
    have hc := Finset.sum_congr rfl (fun u (_ : u ∈ Finset.univ) => hsplitpn u)
    rw [hc, Finset.sum_sub_distrib] at hsum
    linarith
  have habs : ∀ u : S, max (a u) 0 + max (-a u) 0 = |a u| := by
    intro u
    rcases le_or_gt 0 (a u) with h | h
    · rw [max_eq_left h, max_eq_right (by linarith), abs_of_nonneg h]; ring
    · rw [max_eq_right h.le, max_eq_left (by linarith), abs_of_neg h]; ring
  have hsumabs : ∑ u, |a u| = 2 * ∑ u, max (a u) 0 := by
    have hc : ∑ u, |a u| = ∑ u, (max (a u) 0 + max (-a u) 0) :=
      Finset.sum_congr rfl fun u _ => (habs u).symm
    rw [hc, Finset.sum_add_distrib, ← hpn]; ring
  have hsplitabs : ∑ u, |a u| = |a s| + ∑ u ∈ Finset.univ.erase s, |a u| :=
    (Finset.add_sum_erase Finset.univ (fun u => |a u|) (Finset.mem_univ s)).symm
  have hasle : a s ≤ ∑ u ∈ Finset.univ.erase s, |a u| := by
    have hsplit : a s + ∑ u ∈ Finset.univ.erase s, a u = 0 := by
      rw [Finset.add_sum_erase Finset.univ a (Finset.mem_univ s)]; exact hsum
    have hneg : -(∑ u ∈ Finset.univ.erase s, a u) ≤ ∑ u ∈ Finset.univ.erase s, |a u| := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun u _ => neg_le_abs _
    linarith
  rw [abs_of_pos hs] at hsplitabs
  linarith

/-- **The absolute-value floor condition is unsatisfiable on a conservative network.**

For every `x` in the box, `⟨a, x⟩ ≤ M ∑_{u ≠ s} |a u|`.  So the old condition
`M ∑_{u ≠ s} |a u| < η` together with `η ≤ ⟨a, x⟩` is contradictory, and any criterion carrying
both was vacuous. -/
theorem inner_le_erase_abs_of_sum_zero {a : S → ℝ} {M : ℝ} (hM : 0 ≤ M) {s : S}
    (hs : 0 < a s) (hsum : ∑ u, a u = 0)
    {x : Concentration S} (hx : ∀ u, 0 ≤ x u) (hxM : ∀ u, x u ≤ M) :
    ∑ u, a u * x u ≤ M * ∑ u ∈ Finset.univ.erase s, |a u| := by
  have h1 : ∑ u, a u * x u ≤ M * ∑ u, max (a u) 0 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    calc a u * x u ≤ max (a u) 0 * x u :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (hx u)
      _ ≤ max (a u) 0 * M := mul_le_mul_of_nonneg_left (hxM u) (le_max_right _ _)
      _ = M * max (a u) 0 := mul_comm _ _
  have h2 := sum_posPart_le_erase_abs hs hsum
  nlinarith [h1, h2, hM]

/-- The contradiction, packaged: no level satisfies the absolute-value floor condition together
with the start condition. -/
theorem not_level_abs_and_start {a : S → ℝ} {M η : ℝ} (hM : 0 ≤ M) {s : S}
    (hs : 0 < a s) (hsum : ∑ u, a u = 0)
    {x : Concentration S} (hx : ∀ u, 0 ≤ x u) (hxM : ∀ u, x u ≤ M)
    (hfloor : M * (∑ u ∈ Finset.univ.erase s, |a u|) < η)
    (hstart : η ≤ ∑ u, a u * x u) : False := by
  have := inner_le_erase_abs_of_sum_zero hM hs hsum hx hxM
  linarith

/-! ### The convex criterion, and eliminating the tile-assignment clause -/

/-- **Convex multi-piece criterion.**  The same statement as
`Network.exists_positive_omegaPoint_of_tiled_faceCores` but for a `barrier` — an *intersection* of
halfspaces — which is the shape the zero-separating surface has.  Obtained from the min-max version
from `Network.barrier_le_of_toric_descent` together with
`Network.exists_positive_omegaPoint_of_coordinate_floors`. -/
theorem exists_positive_omegaPoint_of_convex_tiles (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {Kc : Set (Concentration S)} (hK : IsCompact Kc) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ Kc)
    (hΓcont : ContinuousOn (γ x₀) (Set.Ici 0))
    (hΓpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hclass : ∀ t, 0 ≤ t → N.StoichCompatible (γ x₀ 0) (γ x₀ t))
    {δ : ℝ} (hδ : 0 < δ) {P : Finset S} {B R R' : ℝ} (hRR' : R < R')
    {σ : ι' → Set N.euclideanStoichSubspace}
    {m : ι' → N.euclideanStoichSubspace}
    (hm : ∀ i : ι', ∀ C ∈ N.relevantCones (σ i) δ B, m i ∈ C)
    {b : ι' → ℝ}
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState (γ x₀ 0)) ≤ R)
    (hassign : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ∀ i : ι',
        innerSL ℝ (-m i) (N.euclideanStoichState (γ x₀ t)) - b i
          = PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
              (N.euclideanStoichState (γ x₀ t)) →
        N.faceLogPart P xstar (γ x₀ t) ∈ σ i)
    (hregime : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ‖N.offFaceLogPart P xstar (γ x₀ t)‖ ≤ B)
    (hsep : ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive →
      N.StoichCompatible (γ x₀ 0) x →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R → ε ≤ x s) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  have hnear : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ∀ i : ι',
        innerSL ℝ (-m i) (N.euclideanStoichState (γ x₀ t)) - b i
          = PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
              (N.euclideanStoichState (γ x₀ t)) →
        ∀ C ∈ N.relativeSourceOrderNegativeStoichFan,
          Metric.infDist (N.relativeLogFanState xstar (γ x₀ t))
            (C : Set N.euclideanStoichSubspace) < δ → m i ∈ C := by
    intro t ht hlevel hband i hactive C hCF hCnear
    exact hm i C
      (N.mem_relevantCones_of_infDist_lt P (hassign t ht hlevel hband i hactive)
        (hregime t ht hlevel hband) hCF hCnear)
  have htrap := N.barrier_le_of_toric_descent_in_band κ hxs hcb hδ hRR' hΓcont hΓpos hΓd
    hstart hnear
  refine exists_positive_omegaPoint_of_coordinate_floors hϕγ hK hmaps ?_
  intro s
  obtain ⟨ε, hε, hbound⟩ := hsep s
  exact ⟨ε, hε, fun t ht => hbound (γ x₀ t) (hΓpos t ht) (hclass t ht) (htrap t ht)⟩

/-! ### Why the tile must be taken along the trajectory

The obvious definition of an angular tile — "all relative-log face parts at points where piece `i`
is active" — quantified over *every* positive `x` satisfying the regime bound.  That is too
generous, and the two lemmas below show exactly how it fails.

`relevantCones_eq_fan_of_small`: if a tile contains **any** point of norm `< δ + B`, then *every*
cone of the fan is relevant to it, because `0` belongs to every cone.  `mem_all_cones_of_hm` then
forces the piece's normal into every cone of the fan simultaneously, which is incompatible with
`0 < (m i) s`.

A tile quantified over all `x` does contain such points: taking `x` with `x s ≈ xstar s` for
`s ∈ P` makes `faceLogPart` arbitrarily small while leaving the off-face bound satisfied, and
nothing in the hypotheses rules out the barrier reaching its level there.  So the self-consistency
clause would be unsatisfiable and the reduction vacuous.

The tile is therefore taken along the **trajectory**: only relative-log face parts actually visited
by the orbit while the level is reached.  That is all the criterion ever uses, and it is what
Craciun's surface condition asks for — the cone condition is imposed on the surface where it sits
near the face, not on all of the positive orthant. -/

/-- If an angular tile contains any point of norm `< δ + B`, every cone of the fan is relevant to
it, since `0` lies in every cone. -/
theorem relevantCones_eq_fan_of_small (N : Network S)
    {σ : Set N.euclideanStoichSubspace} {δ B : ℝ} {k : N.euclideanStoichSubspace}
    (hk : k ∈ σ) (hnorm : ‖k‖ < δ + B) :
    N.relevantCones σ δ B = N.relativeSourceOrderNegativeStoichFan := by
  apply Finset.Subset.antisymm
  · intro C hC
    exact (N.mem_relevantCones.1 hC).1
  · intro C hC
    refine N.mem_relevantCones.2 ⟨hC, 0, C.zero_mem, k, hk, ?_⟩
    simpa [dist_eq_norm] using hnorm

/-- Consequence: a small-norm tile point forces the piece's normal into every cone of the fan. -/
theorem mem_all_cones_of_hm (N : Network S)
    {σ : Set N.euclideanStoichSubspace} {δ B : ℝ} {m : N.euclideanStoichSubspace}
    {k : N.euclideanStoichSubspace} (hk : k ∈ σ) (hnorm : ‖k‖ < δ + B)
    (hm : ∀ C ∈ N.relevantCones σ δ B, m ∈ C) :
    ∀ C ∈ N.relativeSourceOrderNegativeStoichFan, m ∈ C := fun C hC =>
  hm C (by rw [N.relevantCones_eq_fan_of_small hk hnorm]; exact hC)

/-- The set of relative-log face parts actually reachable at points where piece `i` is active and
the near-face regime holds.  Taking this as the angular tile of piece `i` makes the
tile-assignment clause hold *by construction*. -/
noncomputable def activeFaceImage (N : Network S) (P : Finset S) (xstar : Concentration S)
    (Γ : ℝ → Concentration S) (m : ι' → N.euclideanStoichSubspace) (b : ι' → ℝ) (R R' : ℝ)
    (i : ι') : Set N.euclideanStoichSubspace :=
  {X | ∃ t : ℝ, 0 ≤ t ∧
    R ≤ PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
      (N.euclideanStoichState (Γ t)) ∧
    PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
      (N.euclideanStoichState (Γ t)) ≤ R' ∧
    innerSL ℝ (-m i) (N.euclideanStoichState (Γ t)) - b i
      = PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
          (N.euclideanStoichState (Γ t)) ∧
    X = N.faceLogPart P xstar (Γ t)}

theorem faceLogPart_mem_activeFaceImage (N : Network S) (P : Finset S)
    {xstar : Concentration S} {Γ : ℝ → Concentration S}
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R R' : ℝ} {i : ι'} {t : ℝ} (ht : 0 ≤ t)
    (hlevel : R ≤ PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
      (N.euclideanStoichState (Γ t)))
    (hband : PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
      (N.euclideanStoichState (Γ t)) ≤ R')
    (hactive : innerSL ℝ (-m i) (N.euclideanStoichState (Γ t)) - b i
      = PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
          (N.euclideanStoichState (Γ t))) :
    N.faceLogPart P xstar (Γ t) ∈ N.activeFaceImage P xstar Γ m b R R' i :=
  ⟨t, ht, hlevel, hband, hactive, rfl⟩

/-- **The tile-assignment clause can be eliminated.**

Take each angular tile to be the set of relative-log face parts actually reachable where that piece
is active — `activeFaceImage`.  Then the clause `hassign` of
`exists_positive_omegaPoint_of_convex_tiles`, which is the log-to-linear coupling and the one place
Craciun still needs his `Ψ` correspondence, holds *by construction*, and what remains is a
**self-consistency condition on finitely many vectors and scalars**:

> each `m i` lies in the core of the cones relevant to its own active image.

No tiles have to be chosen and no correspondence between log-space and state-space regions has to
be established.  The blueprint problem becomes: find `m : ι' → euclideanStoichSubspace`,
`b : ι' → ℝ`, and `R`, `B` with

* `hm`: `m i` lies in every cone relevant to `activeFaceImage … i` for every `i`,
* `hstart`: the orbit starts inside the region,
* `hregime`: the region sits in the near-face regime (off-face part bounded by `B`),
* `hsep`: which `coordinate_floor_of_dominant_barrier` already discharges from elementary
  coefficient inequalities.

The `hm` clause is self-referential — shrinking the region shrinks the active images, which enlarges
their cores by `relevantCore_le_of_subset` — so it is a fixed-point problem, which is what the
`ε(α)` scale hierarchy of v3 §7.4.3 is for. -/
theorem exists_positive_omegaPoint_of_selfConsistent_normals (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {Kc : Set (Concentration S)} (hK : IsCompact Kc) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ Kc)
    (hΓcont : ContinuousOn (γ x₀) (Set.Ici 0))
    (hΓpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hclass : ∀ t, 0 ≤ t → N.StoichCompatible (γ x₀ 0) (γ x₀ t))
    {δ : ℝ} (hδ : 0 < δ) {P : Finset S} {B R R' : ℝ} (hRR' : R < R')
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ}
    (hm : ∀ i : ι', ∀ C ∈ N.relevantCones (N.activeFaceImage P xstar (γ x₀) m b R R' i) δ B,
      m i ∈ C)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState (γ x₀ 0)) ≤ R)
    (hregime : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ‖N.offFaceLogPart P xstar (γ x₀ t)‖ ≤ B)
    (hsep : ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, x.Positive →
      N.StoichCompatible (γ x₀ 0) x →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState x) ≤ R → ε ≤ x s) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive :=
  N.exists_positive_omegaPoint_of_convex_tiles κ hxs hcb hϕγ hK hmaps hΓcont hΓpos hΓd hclass hδ
    hRR' hm hstart
    (fun _t ht hlevel hband _ hactive =>
      N.faceLogPart_mem_activeFaceImage P ht hlevel hband hactive)
    hregime hsep

/-! ### The sharpest form of what remains -/

/-- **The blueprint problem, with separation discharged.**

The pieces are indexed by an arbitrary finite `ι'`, and `piece : S → ι'` assigns to each species
*some* piece that is positive at it with a high enough level.  There is deliberately no assumption
that `piece` is injective or surjective: the construction is expected to need **more** pieces than
species — Craciun's blueprint has one face per tile, and the tiles refine far beyond one per
coordinate direction — while separation only needs one dominant piece per species.

With that data:

* `hsep` is discharged internally by `coordinate_floor_of_dominant_barrier`;
* `hassign` is discharged internally by taking `activeFaceImage` as the tiles;
* descent, trapping and transport are the verified chain of
  `CRNT.Dynamics.ToricBarrierTrapping`.

What is left is exactly `hm`, `hstart` and `hregime`.  In words:

> Find a finite family of stoichiometric vectors `m i` and levels `b i`, with each species covered
> by some `m i` positive at it, such that every `m i` lies in **every** cone of
> `N.relativeSourceOrderNegativeStoichFan` coming within `δ + B` of the set of relative-log face
> parts reachable where `m i` is the active piece.

No dynamics, no analysis, no log-to-linear correspondence.  `relevantCore_le_of_subset` gives the
monotonicity to exploit: more pieces and higher levels shrink each active image, which enlarges the
cone intersection each normal has to sit in.  Since a vector in a *proper* intersection of two
maximal cones can be forced to `0` — which would contradict `hpos` — a coarse family cannot work,
and refining is the only lever.  That is the role of the `ε(α)` scale hierarchy of v3 §7.4.3.

The hypothesis `hMclass` — that the positive compatibility class is bounded by `M` — is automatic
for conservative networks.  It is *not* automatic in general, and the failure is machine-checked:
`CRNT.Examples.OpenSystem.exists_complexBalanced_unbounded_class` exhibits a weakly reversible
network of deficiency zero — hence complex balanced for *every* rate vector, so it carries exactly
the `hxs`/`hcb` a caller of this criterion has — whose stoichiometric subspace is everything, so no
`M` bounds its positive compatibility classes.  Craciun's paper never assumes bounded classes: the
bound there is on the invariant *region*, obtained from the cube `[0,M]ⁿ` around the bounded
trajectory together with a level set of the Horn--Jackson Lyapunov function (v3 §6.1, §9.4
Lemma 9.11), which is what `CRNT.Geometry.ZeroSeparatingSurface`'s compact-band machinery is for.
A criterion that replaced the class-wide `hMclass` by a box bound on the guarded region would match
the paper; it would still be uninstantiable inside
`CRNT.Network.exists_positive_omegaPoint_of_highCodimension_siphonFace`, where any uniform-floor
statement collides with the boundary ω-point `wmax` (see that module's packaging audit). -/
theorem exists_positive_omegaPoint_of_blueprintData (N : Network S) (κ : N.RateConstants)
    {xstar : Concentration S} (hxs : xstar.Positive) (hcb : N.IsComplexBalanced κ xstar)
    {ϕ : Flow ℝ≥0 (Concentration S)}
    {γ : Concentration S → ℝ → Concentration S} {x₀ : Concentration S}
    (hϕγ : ∀ x (t : ℝ≥0), ϕ t x = γ x t)
    {Kc : Set (Concentration S)} (hK : IsCompact Kc) (hmaps : ∀ t : ℝ≥0, ϕ t x₀ ∈ Kc)
    (hΓcont : ContinuousOn (γ x₀) (Set.Ici 0))
    (hΓpos : ∀ t, 0 ≤ t → (γ x₀ t).Positive)
    (hΓd : ∀ t, 0 ≤ t → HasDerivAt (γ x₀) (N.massActionVectorField κ (γ x₀ t)) t)
    (hclass : ∀ t, 0 ≤ t → N.StoichCompatible (γ x₀ 0) (γ x₀ t))
    {δ : ℝ} (hδ : 0 < δ) {P : Finset S} {B R R' M : ℝ} (hRR' : R < R')
    (hMclass : ∀ x : Concentration S, x.Positive → N.StoichCompatible (γ x₀ 0) x →
      ∀ u, x u ≤ M)
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ}
    (piece : S → ι')
    (hpos : ∀ s : S, 0 < ((m (piece s) : EuclideanSpace ℝ S) s))
    (hlevel : ∀ s : S,
      M * (∑ u ∈ Finset.univ.erase s, max ((m (piece s) : EuclideanSpace ℝ S) u) 0)
        < -(R + b (piece s)))
    (hm : ∀ i : ι', ∀ C ∈ N.relevantCones (N.activeFaceImage P xstar (γ x₀) m b R R' i) δ B,
      m i ∈ C)
    (hstart : PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
      (N.euclideanStoichState (γ x₀ 0)) ≤ R)
    (hregime : ∀ t, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) →
      PolyhedralBarrier.barrier (fun i : ι' => innerSL ℝ (-m i)) b
        (N.euclideanStoichState (γ x₀ t)) ≤ R' →
      ‖N.offFaceLogPart P xstar (γ x₀ t)‖ ≤ B) :
    ∃ p ∈ omegaLimit atTop ϕ {x₀}, p.Positive := by
  refine N.exists_positive_omegaPoint_of_selfConsistent_normals κ hxs hcb hϕγ hK hmaps hΓcont
    hΓpos hΓd hclass hδ (P := P) (B := B) hRR' hm hstart hregime ?_
  intro s
  obtain ⟨ε, hε, hbound⟩ :=
    N.coordinate_floor_of_dominant_barrier (M := M) (R := R) (b := b) piece hpos hlevel s
  exact ⟨ε, hε, fun x hxpos hxclass hxregion =>
    hbound x (fun u => (hxpos u).le) (fun u => hMclass x hxpos hxclass u) hxregion⟩

/-! ### Guarding against the vacuity trap

`relevantCones_eq_fan_of_small` is a trap the self-consistency clause can fall into: one tile point
of norm `< δ + B` collapses `hm` into "the normal lies in every cone", which `hpos` forbids.  The
lemmas here let a caller *check* that the trap does not fire, by exhibiting a depth bound `ρ` on the
face part along the orbit.

`hdeep` is a tuning condition on the level `R`, not a consequence of the coefficient conditions: it
says the guarded region's boundary sits **near the face**, which is exactly what `R` is for.  It
does not follow from `hpos`/`hlevel`, which only pin `η j` into the window
`(M ∑_{u ≠ s} |m j u|, M ∑_u |m j u|]` and give coordinate floors *inside* the region, saying
nothing about depth at the boundary. -/

/-- Every point of the trajectory-restricted tile inherits the depth bound `ρ`. -/
theorem norm_ge_of_mem_activeFaceImage (N : Network S) {P : Finset S}
    {xstar : Concentration S} {Γ : ℝ → Concentration S}
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R R' ρ : ℝ} {i : ι'}
    (hdeep : ∀ t : ℝ, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
        (N.euclideanStoichState (Γ t)) →
      PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
        (N.euclideanStoichState (Γ t)) ≤ R' →
      ρ ≤ ‖N.faceLogPart P xstar (Γ t)‖)
    {X : N.euclideanStoichSubspace} (hX : X ∈ N.activeFaceImage P xstar Γ m b R R' i) :
    ρ ≤ ‖X‖ := by
  obtain ⟨t, ht, hlevel, hband, -, hXeq⟩ := hX
  rw [hXeq]
  exact hdeep t ht hlevel hband

/-- **The trap cannot fire.**  With a depth bound `ρ` exceeding `δ + B`, no tile point is small
enough to make every cone of the fan relevant, so `Network.relevantCones_eq_fan_of_small` does not
apply and the self-consistency clause is not self-defeating. -/
theorem not_small_of_mem_activeFaceImage (N : Network S) {P : Finset S}
    {xstar : Concentration S} {Γ : ℝ → Concentration S}
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R R' ρ δ B : ℝ} {i : ι'}
    (hρ : δ + B < ρ)
    (hdeep : ∀ t : ℝ, 0 ≤ t →
      R ≤ PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
        (N.euclideanStoichState (Γ t)) →
      PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
        (N.euclideanStoichState (Γ t)) ≤ R' →
      ρ ≤ ‖N.faceLogPart P xstar (Γ t)‖)
    {X : N.euclideanStoichSubspace} (hX : X ∈ N.activeFaceImage P xstar Γ m b R R' i) :
    ¬ ‖X‖ < δ + B := by
  have := N.norm_ge_of_mem_activeFaceImage hdeep hX
  intro hlt
  linarith

/-! ### Reducing `hm` to a separation condition

`N.relativeSourceOrderNegativeStoichFan` is the **arrangement fan** of the hyperplanes orthogonal
to the projected source-complex differences (`sourceOrderNormal`, i.e.
`proj_V (toEuclid y_{r₂} - toEuclid y_{r₁})`), sign-reversed — Craciun's hyperplane-generated fan of
v3 §3.  Its cones are the chambers and faces of that arrangement.

That makes the self-consistency clause much more tractable than it looks.  `relevantCones σ δ B`
collects the cones coming within `δ + B` of the tile.  If a tile sits inside **one** chamber and is
`δ + B`-separated from every other cone of the fan, that family is the single chamber, and `hm`
collapses to "pick any `m i` in that chamber".

So `hm` is implied by a *separation* condition, which is exactly what a scale hierarchy delivers:
subdivide until each piece's active image lies in one chamber, well away from the walls.  Note also
that `δ` may be taken as small as one likes — `Network.euclideanMassActionField_mem_toricField`
holds for every `δ > 0`, and `toricField` is monotone in `δ` — so the separation only has to beat
`B` plus an arbitrarily small margin. -/

omit [Fintype ι'] [Nonempty ι'] in
/-- **One chamber per piece implies the self-consistency clause.**

If each tile `σ i` lies in a cone `C i` of the fan and is `δ + B`-separated from every *other* cone,
then any `m i ∈ C i` satisfies `hm`.  This replaces a self-referential clause by a separation
condition on the tiles. -/
theorem hm_of_single_chamber (N : Network S) {σ : ι' → Set N.euclideanStoichSubspace}
    {δ B : ℝ} {m : ι' → N.euclideanStoichSubspace}
    {C : ι' → ProperCone ℝ N.euclideanStoichSubspace}
    (hmem : ∀ i, m i ∈ C i)
    (hfar : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, D ≠ C i →
      ∀ y ∈ (D : Set N.euclideanStoichSubspace), ∀ k ∈ σ i, δ + B ≤ dist y k) :
    ∀ i : ι', ∀ D ∈ N.relevantCones (σ i) δ B, m i ∈ D := by
  intro i D hD
  obtain ⟨hDF, y, hyD, k, hk, hdist⟩ := N.mem_relevantCones.1 hD
  by_cases hDC : D = C i
  · rw [hDC]; exact hmem i
  · exact absurd hdist (not_lt.mpr (hfar i D hDF hDC y hyD k hk))

/-- The same conclusion for the trajectory-and-band-restricted tiles, which is the form
`exists_positive_omegaPoint_of_blueprintData` consumes. -/
theorem hm_of_single_chamber_activeFaceImage (N : Network S) (P : Finset S)
    {xstar : Concentration S} {Γ : ℝ → Concentration S}
    {δ B : ℝ} {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R R' : ℝ}
    {C : ι' → ProperCone ℝ N.euclideanStoichSubspace}
    (hmem : ∀ i, m i ∈ C i)
    (hfar : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, D ≠ C i →
      ∀ y ∈ (D : Set N.euclideanStoichSubspace),
      ∀ k ∈ N.activeFaceImage P xstar Γ m b R R' i, δ + B ≤ dist y k) :
    ∀ i : ι', ∀ D ∈ N.relevantCones (N.activeFaceImage P xstar Γ m b R R' i) δ B, m i ∈ D :=
  N.hm_of_single_chamber hmem hfar

/-! ### Normal existence is settled

`hm_of_single_chamber` leaves two things to arrange: the tiles must separate into single chambers,
and the chosen `m i` must be positive at the species it dominates (`hpos`).  The second is now
settled outright, and it costs nothing per network.

The projected coordinate direction `euclideanStoichUnit s` has `s`-coordinate equal to its own
squared norm, so it is positive as soon as that vector is nonzero — which happens exactly when some
stoichiometric vector has a nonzero `s`-component, i.e. exactly outside the degenerate case already
excluded by `Network.ker_finrank_ne_of_face_point`.  Completeness of the fan then puts it in some
chamber.

So **suitable normals always exist**; the whole remaining difficulty is the separation condition. -/

/-- The projected coordinate direction has `s`-coordinate equal to its squared norm. -/
theorem coord_euclideanStoichUnit_self (N : Network S) (s : S) :
    (N.euclideanStoichUnit s : EuclideanSpace ℝ S) s = ‖N.euclideanStoichUnit s‖ ^ 2 := by
  have h := N.inner_euclideanStoichStateL_eq_sum (N.euclideanStoichUnit s) (Pi.single s 1)
  rw [← Network.euclideanStoichUnit] at h
  rw [real_inner_self_eq_norm_sq] at h
  rw [h, Finset.sum_eq_single s (fun u _ hus => by simp [Ne.symm hus])
    (fun h => absurd (Finset.mem_univ s) h)]
  simp

/-- The projected coordinate direction is nonzero as soon as some stoichiometric vector has a
nonzero component there. -/
theorem euclideanStoichUnit_ne_zero (N : Network S) {s : S} {p : Concentration S}
    (hp : p ∈ N.stoichSubspace) (hps : p s ≠ 0) : N.euclideanStoichUnit s ≠ 0 := by
  intro hzero
  have hmem : CRNT.toEuclid p ∈ N.euclideanStoichSubspace := by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨p, hp, rfl⟩
  have h := N.inner_euclideanStoichStateL_eq_sum (⟨CRNT.toEuclid p, hmem⟩) (Pi.single s 1)
  rw [← Network.euclideanStoichUnit, hzero, inner_zero_right] at h
  rw [Finset.sum_eq_single s (fun u _ hus => by simp [Ne.symm hus])
    (fun h => absurd (Finset.mem_univ s) h)] at h
  simp [CRNT.toEuclid_apply] at h
  exact hps h.symm

theorem pos_coord_euclideanStoichUnit (N : Network S) {s : S}
    (h : N.euclideanStoichUnit s ≠ 0) :
    0 < (N.euclideanStoichUnit s : EuclideanSpace ℝ S) s := by
  rw [N.coord_euclideanStoichUnit_self]
  exact pow_pos (norm_pos_iff.mpr h) 2

/-- **A chamber with a positive normal always exists.**  For any species at which some
stoichiometric vector is nonzero, some cone of the fan contains a vector with positive
`s`-coordinate — namely the chamber containing `euclideanStoichUnit s`.  This discharges the
`hpos` side of `hm_of_single_chamber`. -/
theorem exists_chamber_coord_pos (N : Network S) {s : S} {p : Concentration S}
    (hp : p ∈ N.stoichSubspace) (hps : p s ≠ 0) :
    ∃ C ∈ N.relativeSourceOrderNegativeStoichFan, ∃ m ∈ C,
      0 < (m : EuclideanSpace ℝ S) s := by
  obtain ⟨C, hCF, hmem⟩ :=
    (N.relativeSourceOrderNegativeStoichFan_isPolyhedralFan).exists_mem
      (N.euclideanStoichUnit s)
  exact ⟨C, hCF, N.euclideanStoichUnit s, hmem,
    N.pos_coord_euclideanStoichUnit (N.euclideanStoichUnit_ne_zero hp hps)⟩

/-! ### Making the separation condition checkable

`hm_of_single_chamber` asks for a metric separation between each tile and every other cone.  Metric
statements about cones are awkward; signed evaluations against the arrangement's normals are not.
Cauchy--Schwarz converts one into the other: a margin in `⟪a, ·⟫` on the tile, against a normal `a`
that is nonpositive on the other cone, *is* a distance margin.

Combined with `inner_faceLogPart_eq_sum`, the margin becomes an explicit inequality in the
log-deviations,

```
⟪a, faceLogPart P xstar x⟫ = ∑ s ∈ P, (a) s * (log (xstar s) - log (x s)),
```

so the separation condition is a finite family of linear inequalities in `log (xstar s) - log (x s)`
with coefficients read off the arrangement.  That is the form a scale hierarchy can be built
against. -/

/-- **A signed margin is a distance margin.**  If `a` is nonpositive on `y` and at least
`‖a‖ * μ` on `X`, then `X` and `y` are at least `μ` apart. -/
theorem dist_ge_of_separating_margin (N : Network S)
    {a X y : N.euclideanStoichSubspace} {μ : ℝ}
    (ha : a ≠ 0) (hy : ⟪a, y⟫ ≤ 0) (hmargin : ‖a‖ * μ ≤ ⟪a, X⟫) :
    μ ≤ dist X y := by
  have hnorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hcs : ⟪a, X - y⟫ ≤ ‖a‖ * ‖X - y‖ := real_inner_le_norm a (X - y)
  have hsub : ⟪a, X - y⟫ = ⟪a, X⟫ - ⟪a, y⟫ := inner_sub_right a X y
  rw [dist_eq_norm]
  nlinarith [hcs, hsub, hy, hmargin, hnorm]

omit [Fintype ι'] [Nonempty ι'] in
/-- **Separation from signed margins.**  Supplying, for each piece `i` and each other cone `D`, a
nonzero normal that is nonpositive on `D` and has margin `‖a‖ * (δ + B)` on the tile yields the
`hfar` hypothesis of `hm_of_single_chamber`, hence the self-consistency clause. -/
theorem hm_of_separating_margins (N : Network S) {σ : ι' → Set N.euclideanStoichSubspace}
    {δ B : ℝ} {m : ι' → N.euclideanStoichSubspace}
    {C : ι' → ProperCone ℝ N.euclideanStoichSubspace}
    (sep : ι' → ProperCone ℝ N.euclideanStoichSubspace → N.euclideanStoichSubspace)
    (hmem : ∀ i, m i ∈ C i)
    (hsepne : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, D ≠ C i → sep i D ≠ 0)
    (hsepD : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, D ≠ C i →
      ∀ y ∈ (D : Set N.euclideanStoichSubspace), ⟪sep i D, y⟫ ≤ 0)
    (hsepmargin : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, D ≠ C i →
      ∀ k ∈ σ i, ‖sep i D‖ * (δ + B) ≤ ⟪sep i D, k⟫) :
    ∀ i : ι', ∀ D ∈ N.relevantCones (σ i) δ B, m i ∈ D := by
  refine N.hm_of_single_chamber hmem ?_
  intro i D hDF hDC y hyD k hk
  rw [dist_comm]
  exact N.dist_ge_of_separating_margin (hsepne i D hDF hDC) (hsepD i D hDF hDC y hyD)
    (hsepmargin i D hDF hDC k hk)

/-! ### Depth buys margin: the mechanism of the scale hierarchy

Take the tile shape that a blueprint piece actually produces: one face coordinate deep
(`ρ ≤ log (xstar s₀) - log (x s₀)`) and the others shallow (bounded by `κ`).  Against an
arrangement normal `a` with `0 < (a) s₀`, the signed evaluation then satisfies

```
(a) s₀ * ρ  -  κ * ∑_{s ∈ P.erase s₀} |(a) s|   ≤   ⟪a, faceLogPart P xstar x⟫,
```

so the margin grows linearly in the depth `ρ` while the shallow coordinates contribute a fixed
penalty.  `exists_depth_for_margin` says the trade always closes: **any prescribed margin is
achieved by taking the tile deep enough.**

Feeding that into `hm_of_separating_margins` gives the separation, hence `hm`.  This is the content
of Craciun's `ε(α)` hierarchy at a single tile: the scales are chosen so that each piece's active
image is deep in its own coordinate and shallow in the others, which puts it inside one chamber of
the source-complex-difference arrangement with room to spare. -/

/-- Pairing against a projected coordinate direction reads off a coordinate. -/
theorem inner_euclideanStoichUnit (N : Network S) (m : N.euclideanStoichSubspace) (s : S) :
    ⟪m, N.euclideanStoichUnit s⟫ = (m : EuclideanSpace ℝ S) s := by
  have h := N.inner_euclideanStoichStateL_eq_sum m (Pi.single s 1)
  rw [← Network.euclideanStoichUnit] at h
  rw [h, Finset.sum_eq_single s (fun u _ hus => by simp [Ne.symm hus])
    (fun h => absurd (Finset.mem_univ s) h)]
  simp

/-- **Depth in one coordinate, shallowness in the rest, gives a signed lower bound.** -/
theorem inner_faceLogPart_ge_of_depth (N : Network S) (P : Finset S)
    {xstar x : Concentration S} (a : N.euclideanStoichSubspace)
    {s₀ : S} (hs₀ : s₀ ∈ P) {ρ κ : ℝ}
    (hpos : 0 < (a : EuclideanSpace ℝ S) s₀)
    (hdeep : ρ ≤ Real.log (xstar s₀) - Real.log (x s₀))
    (hnn : ∀ s ∈ P.erase s₀, 0 ≤ Real.log (xstar s) - Real.log (x s))
    (hshallow : ∀ s ∈ P.erase s₀, Real.log (xstar s) - Real.log (x s) ≤ κ) :
    (a : EuclideanSpace ℝ S) s₀ * ρ
        - κ * ∑ s ∈ P.erase s₀, |(a : EuclideanSpace ℝ S) s|
      ≤ ⟪a, N.faceLogPart P xstar x⟫ := by
  rw [N.inner_faceLogPart_eq_sum a P xstar x,
    ← Finset.add_sum_erase P (fun s => (a : EuclideanSpace ℝ S) s
      * (Real.log (xstar s) - Real.log (x s))) hs₀]
  have hhead : (a : EuclideanSpace ℝ S) s₀ * ρ
      ≤ (a : EuclideanSpace ℝ S) s₀ * (Real.log (xstar s₀) - Real.log (x s₀)) :=
    mul_le_mul_of_nonneg_left hdeep hpos.le
  have htail : -(κ * ∑ s ∈ P.erase s₀, |(a : EuclideanSpace ℝ S) s|)
      ≤ ∑ s ∈ P.erase s₀, (a : EuclideanSpace ℝ S) s
          * (Real.log (xstar s) - Real.log (x s)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_le_sum fun s hs => ?_
    have h1 : -(|(a : EuclideanSpace ℝ S) s| * (Real.log (xstar s) - Real.log (x s)))
        ≤ (a : EuclideanSpace ℝ S) s * (Real.log (xstar s) - Real.log (x s)) := by
      have hna := neg_abs_le ((a : EuclideanSpace ℝ S) s)
      nlinarith [hnn s hs, hna]
    have h2 : -(κ * |(a : EuclideanSpace ℝ S) s|)
        ≤ -(|(a : EuclideanSpace ℝ S) s| * (Real.log (xstar s) - Real.log (x s))) := by
      have hsh := hshallow s hs
      nlinarith [abs_nonneg ((a : EuclideanSpace ℝ S) s), hsh]
    linarith
  linarith

/-- The margin form consumed by `hm_of_separating_margins`. -/
theorem margin_of_depth (N : Network S) (P : Finset S)
    {xstar x : Concentration S} (a : N.euclideanStoichSubspace)
    {s₀ : S} (hs₀ : s₀ ∈ P) {ρ κ μ : ℝ}
    (hpos : 0 < (a : EuclideanSpace ℝ S) s₀)
    (hdeep : ρ ≤ Real.log (xstar s₀) - Real.log (x s₀))
    (hnn : ∀ s ∈ P.erase s₀, 0 ≤ Real.log (xstar s) - Real.log (x s))
    (hshallow : ∀ s ∈ P.erase s₀, Real.log (xstar s) - Real.log (x s) ≤ κ)
    (hbound : ‖a‖ * μ ≤ (a : EuclideanSpace ℝ S) s₀ * ρ
      - κ * ∑ s ∈ P.erase s₀, |(a : EuclideanSpace ℝ S) s|) :
    ‖a‖ * μ ≤ ⟪a, N.faceLogPart P xstar x⟫ :=
  le_trans hbound (N.inner_faceLogPart_ge_of_depth P a hs₀ hpos hdeep hnn hshallow)

/-- **The depth-for-margin trade always closes.**  For any shallow bound `κ` and any target margin
`μ`, a large enough depth `ρ` achieves it.  This is why a scale hierarchy can always be pushed far
enough to separate a tile from every chamber but its own. -/
theorem exists_depth_for_margin (N : Network S) (P : Finset S)
    (a : N.euclideanStoichSubspace) {s₀ : S}
    (hpos : 0 < (a : EuclideanSpace ℝ S) s₀) (κ μ : ℝ) :
    ∃ ρ : ℝ, ‖a‖ * μ ≤ (a : EuclideanSpace ℝ S) s₀ * ρ
      - κ * ∑ s ∈ P.erase s₀, |(a : EuclideanSpace ℝ S) s| := by
  refine ⟨(‖a‖ * μ + κ * ∑ s ∈ P.erase s₀, |(a : EuclideanSpace ℝ S) s|)
      / (a : EuclideanSpace ℝ S) s₀, ?_⟩
  rw [mul_div_cancel₀ _ (ne_of_gt hpos)]
  linarith

/-- **Scale separation gives the margin.**

This is the `ε(α)` condition of v3 §7.4.3 in its operative form.  Suppose the log-deviation profile
has its `s₀` coordinate deep and all others bounded by the *next* scale `κ ≥ 1`.  Then the margin
`μ` follows as soon as the deepest scale exceeds the next by the factor

```
T = (‖a‖ * μ + ∑_{s ∈ P.erase s₀} |(a) s|) / (a) s₀,
```

i.e. as soon as `κ * T ≤ log (xstar s₀) - log (x s₀)`.  So the hierarchy is a chain of ratio
thresholds between consecutive scales, one per arrangement normal — which is exactly the shape of
Craciun's `ε(α) ≫ ε(α')` conditions.

Combining with `hm_of_separating_margins` and `hm_of_single_chamber`, a scale-separated profile
yields the self-consistency clause outright. -/
theorem margin_of_scale_ratio (N : Network S) (P : Finset S)
    {xstar x : Concentration S} (a : N.euclideanStoichSubspace)
    {s₀ : S} (hs₀ : s₀ ∈ P) {κ μ : ℝ}
    (hpos : 0 < (a : EuclideanSpace ℝ S) s₀) (hκ : 1 ≤ κ) (hμ : 0 ≤ μ)
    (hnn : ∀ s ∈ P.erase s₀, 0 ≤ Real.log (xstar s) - Real.log (x s))
    (hshallow : ∀ s ∈ P.erase s₀, Real.log (xstar s) - Real.log (x s) ≤ κ)
    (hratio : κ * ((‖a‖ * μ + ∑ s ∈ P.erase s₀, |(a : EuclideanSpace ℝ S) s|)
        / (a : EuclideanSpace ℝ S) s₀)
      ≤ Real.log (xstar s₀) - Real.log (x s₀)) :
    ‖a‖ * μ ≤ ⟪a, N.faceLogPart P xstar x⟫ := by
  set A := (a : EuclideanSpace ℝ S) s₀ with hA
  set Sa := ∑ s ∈ P.erase s₀, |(a : EuclideanSpace ℝ S) s| with hSa
  have hSann : 0 ≤ Sa := Finset.sum_nonneg fun s _ => abs_nonneg _
  have hnorm : 0 ≤ ‖a‖ := norm_nonneg a
  have hscaled : κ * (‖a‖ * μ + Sa) ≤ A * (Real.log (xstar s₀) - Real.log (x s₀)) := by
    have := mul_le_mul_of_nonneg_left hratio hpos.le
    rw [mul_comm A (κ * ((‖a‖ * μ + Sa) / A))] at this
    calc κ * (‖a‖ * μ + Sa) = κ * ((‖a‖ * μ + Sa) / A) * A := by
          field_simp
      _ ≤ A * (Real.log (xstar s₀) - Real.log (x s₀)) := this
  refine N.margin_of_depth P a hs₀ hpos le_rfl hnn hshallow ?_
  have hmu : ‖a‖ * μ ≤ κ * (‖a‖ * μ) := by nlinarith [mul_nonneg hnorm hμ]
  nlinarith [hscaled, hmu, hSann, hκ]

/-! ### Correction: separation is only needed from cones that do *not* contain the chosen one

`hm_of_single_chamber` asks each tile to be `δ + B`-separated from every cone **other than** `C i`.
That is too strong, and unsatisfiable for exactly the tiles a blueprint needs most.

Consider a tile sitting on a *wall* — a lower-dimensional cone `C` of the arrangement, which is
where the normal is forced to live when the `δ`-slack reaches across a face.  Every chamber `D`
adjacent to that wall satisfies `C ⊆ D`, so the tile lies inside `D` as well and `dist = 0`: no
separation from `D` is possible.  But none is needed, because `m i ∈ C ⊆ D` already.

The correct condition is therefore separation only from cones that do **not** contain `C i`.  The
lemmas below replace the earlier ones; `hm_of_single_chamber` remains valid but is the special case
where every relevant cone is `C i` itself. -/

omit [Fintype ι'] [Nonempty ι'] in
/-- **Separation from non-containing cones implies the self-consistency clause.**  If each tile
`σ i` lies in a cone `C i` and is `δ + B`-separated from every cone that does not contain `C i`,
then any `m i ∈ C i` satisfies `hm`. -/
theorem hm_of_cone_family (N : Network S) {σ : ι' → Set N.euclideanStoichSubspace}
    {δ B : ℝ} {m : ι' → N.euclideanStoichSubspace}
    {C : ι' → ProperCone ℝ N.euclideanStoichSubspace}
    (hmem : ∀ i, m i ∈ C i)
    (hfar : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, ¬ (C i ≤ D) →
      ∀ y ∈ (D : Set N.euclideanStoichSubspace), ∀ k ∈ σ i, δ + B ≤ dist y k) :
    ∀ i : ι', ∀ D ∈ N.relevantCones (σ i) δ B, m i ∈ D := by
  intro i D hD
  obtain ⟨hDF, y, hyD, k, hk, hdist⟩ := N.mem_relevantCones.1 hD
  by_cases hCD : C i ≤ D
  · exact hCD (hmem i)
  · exact absurd hdist (not_lt.mpr (hfar i D hDF hCD y hyD k hk))

omit [Fintype ι'] [Nonempty ι'] in
/-- The signed-margin form of `hm_of_cone_family`: margins are needed only against normals
separating the tile from cones that do not contain `C i`. -/
theorem hm_of_cone_family_margins (N : Network S) {σ : ι' → Set N.euclideanStoichSubspace}
    {δ B : ℝ} {m : ι' → N.euclideanStoichSubspace}
    {C : ι' → ProperCone ℝ N.euclideanStoichSubspace}
    (sep : ι' → ProperCone ℝ N.euclideanStoichSubspace → N.euclideanStoichSubspace)
    (hmem : ∀ i, m i ∈ C i)
    (hsepne : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, ¬ (C i ≤ D) →
      sep i D ≠ 0)
    (hsepD : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, ¬ (C i ≤ D) →
      ∀ y ∈ (D : Set N.euclideanStoichSubspace), ⟪sep i D, y⟫ ≤ 0)
    (hsepmargin : ∀ i : ι', ∀ D ∈ N.relativeSourceOrderNegativeStoichFan, ¬ (C i ≤ D) →
      ∀ k ∈ σ i, ‖sep i D‖ * (δ + B) ≤ ⟪sep i D, k⟫) :
    ∀ i : ι', ∀ D ∈ N.relevantCones (σ i) δ B, m i ∈ D := by
  refine N.hm_of_cone_family hmem ?_
  intro i D hDF hCD y hyD k hk
  rw [dist_comm]
  exact N.dist_ge_of_separating_margin (hsepne i D hDF hCD) (hsepD i D hDF hCD y hyD)
    (hsepmargin i D hDF hCD k hk)

/-! ### Class-aware floor condition: a ratio bound, not a sum

The positive-parts sharpening of §the regression guard is necessary but **not sufficient**.  Bounding
the other coordinates' contribution by `M * ∑_{u ≠ s} max (a u) 0`, with `M` the coordinate ceiling,
double-counts whenever `a` has two or more positive entries: inside a conservative class
`∑_u c u * x u = T` the coordinates cannot all sit at the ceiling simultaneously, and the achievable
value of `⟪a, x⟫` is only about `T * max_u (a u / c u)`.

Concretely, on `A + B ⇌ 2B, A + C ⇌ 2C` (see `scripts/probe_residual_case_blueprint.py`) the middle
wall normal `(-2/3, 1/3, 1/3)` — the one positive at *both* face species — needs
`η > T/3` from the sum form while the class allows only `η ≤ T/3`.  Infeasible.  The two outer walls
`(-1/2, 1/2, 0)` and `(-1, 0, 1)`, each positive at a single species, need `η > 0` and allow
`η ≤ T/2` and `η ≤ T`: feasible.  So a blueprint for that network must use the outer walls, one per
species, and *not* the convenient middle one.

The correct penalty uses a **ratio bound**: if `a u ≤ β * c u` for every `u ≠ s`, then
`∑_{u ≠ s} a u * x u ≤ β * T`, a single term rather than a sum. -/

/-- **Class-aware coordinate floor.**  Inside a conservative class, the other coordinates'
contribution is bounded by `β * T` where `β` dominates the coefficient ratios `a u / c u`, rather
than by a sum over coordinates. -/
theorem le_of_halfspace_of_dominant_class {a c : S → ℝ} {T η β : ℝ} {s : S}
    (hs : 0 < a s) (hβ : 0 ≤ β)
    {x : Concentration S} (hx : ∀ u, 0 ≤ x u)
    (hcs : 0 ≤ c s)
    (hcons : ∑ u, c u * x u = T)
    (hratio : ∀ u, u ≠ s → a u ≤ β * c u)
    (hhalf : η ≤ ∑ u, a u * x u) :
    (η - β * T) / a s ≤ x s := by
  have hsplita : ∑ u, a u * x u = a s * x s + ∑ u ∈ Finset.univ.erase s, a u * x u :=
    (Finset.add_sum_erase Finset.univ (fun u => a u * x u) (Finset.mem_univ s)).symm
  have hsplitc : ∑ u, c u * x u = c s * x s + ∑ u ∈ Finset.univ.erase s, c u * x u :=
    (Finset.add_sum_erase Finset.univ (fun u => c u * x u) (Finset.mem_univ s)).symm
  have hrest : ∑ u ∈ Finset.univ.erase s, a u * x u
      ≤ β * ∑ u ∈ Finset.univ.erase s, c u * x u := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun u hu => ?_
    have hus : u ≠ s := Finset.ne_of_mem_erase hu
    calc a u * x u ≤ (β * c u) * x u :=
          mul_le_mul_of_nonneg_right (hratio u hus) (hx u)
      _ = β * (c u * x u) := by ring
  have hcsx : 0 ≤ c s * x s := mul_nonneg hcs (hx s)
  have htail : ∑ u ∈ Finset.univ.erase s, c u * x u ≤ T := by
    rw [hsplitc] at hcons
    linarith
  have hchain : ∑ u ∈ Finset.univ.erase s, a u * x u ≤ β * T := by
    exact le_trans hrest (mul_le_mul_of_nonneg_left htail hβ)
  rw [div_le_iff₀ hs]
  nlinarith [hsplita, hchain, hhalf]

/-- The barrier form: a piece per species, dominant there, with the class-aware level condition. -/
theorem coordinate_floor_of_dominant_class_barrier (N : Network S)
    {m : ι' → N.euclideanStoichSubspace} {b : ι' → ℝ} {R T β : ℝ} {c : S → ℝ}
    (hβ : 0 ≤ β) (hc : ∀ u, 0 ≤ c u)
    (piece : S → ι')
    (hpos : ∀ s : S, 0 < ((m (piece s) : EuclideanSpace ℝ S) s))
    (hratio : ∀ s : S, ∀ u, u ≠ s → (m (piece s) : EuclideanSpace ℝ S) u ≤ β * c u)
    (hlevel : ∀ s : S, β * T < -(R + b (piece s))) :
    ∀ s : S, ∃ ε : ℝ, 0 < ε ∧ ∀ x : Concentration S, (∀ u, 0 ≤ x u) →
      (∑ u, c u * x u = T) →
      PolyhedralBarrier.barrier (fun k : ι' => innerSL ℝ (-m k)) b
        (N.euclideanStoichState x) ≤ R → ε ≤ x s := by
  intro s
  set k := piece s with hk
  refine ⟨(-(R + b k) - β * T) / ((m k : EuclideanSpace ℝ S) s), ?_, ?_⟩
  · exact div_pos (by linarith [hlevel s]) (hpos s)
  · intro x hx hcons hxregion
    have hhalf : -(R + b k) ≤ ∑ u, (m k : EuclideanSpace ℝ S) u * x u := by
      have := N.barrier_euclideanStoichState_le_iff.mp hxregion k
      linarith
    exact le_of_halfspace_of_dominant_class (hpos s) hβ hx (hc s) hcons
      (hratio s) hhalf

end Network
end CRNT
