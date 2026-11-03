import CRNT.Geometry.CraciunZSH

/-!
# The relative-interior (chamber) form of the Craciun v3 scale-separation lemma

Reference: Gheorghe Craciun, *Toric Differential Inclusions and a Proof of the Global Attractor
Conjecture*, arXiv:1501.02860v3, **Lemma 9.7**.

## Why this module exists

`CRNT.Geometry.CraciunZSH` proves the scale step in the form

`exists_eventual_tube_subset_of_cone_interior ... (hCinterior : C ⊆ interior K) ...`

and `exists_uniform_eventual_tube_subset_of_finite_properCone_pairs` specializes it with
`hinterior : ∀ i, (C i : Set E) ⊆ interior (K i : Set E)`.

**That hypothesis is false in the situation Craciun actually uses.** A chamber cone `C` lying on a
symmetry hyperplane `x_i = x_j` — Craciun's own footnote 127 flags this — has *empty ambient
interior*, so `C ⊆ interior K` is unsatisfiable for the `K` that occurs, however `K` is chosen.
The correct hypothesis in v3 is a statement about the *relative* interior inside the chamber.

## The theorem proved here

Fix a **chamber** `chamber` with `C ⊆ chamber ⊆ K`, and suppose the unit-section points of `C` are
interior to `chamber`:

```
(hinterior : ∀ x ∈ C ∩ sphere 0 1, x ∈ interior chamber)
```

Then the conclusion of Lemma 9.7 holds verbatim:

```
∃ M : ℝ, 0 < M ∧ ∀ x : E, Metric.infDist x C < δ → M < ‖x‖ → x ∈ K
```

No interior of `K` is used anywhere in the proof: the scaled perturbation lands in a small ball
around a unit-section point `u`, that ball lies in `chamber ⊆ K`, and being a subset of `K` is all
the rescaling step needs. That single change of hypothesis is what makes the packaged criteria of
`CRNT.Dynamics.ToricBarrierExplicit` and `CRNT.Geometry.CraciunZSH` satisfiable at all, on symmetry
hyperplanes where the ambient-interior version is not.

## Additional content

* `exists_eventual_tube_subset_of_chamber_affineInterior` — the fully abstract form, where the
  hypothesis is only "each unit-section point has a ball inside `K ∩ affineSpan ℝ chamber`". A caller
  with an explicit ball statement discharges the theorem without mentioning interiors at all.
* `exists_eventual_tube_subset_of_closed_cone_chamber_interior` — the closed-cone form, in a proper
  space, matching `exists_eventual_tube_subset_of_closed_cone_interior` with the chamber hypothesis
  in place of `C ⊆ interior K`.
* `exists_uniform_eventual_tube_subset_of_chamber_pairs` — the finite-family form, so a single scale
  serves a whole fan.

**This module is not on the critical path to Hole A.** `CRNT.Dynamics.FaceDirectionCone` routes
around the whole `CraciunZSH` apparatus: it imports only `CRNT.Dynamics.ToricBarrierTrapping`, and
its relevant-cone family is *defined* as "chambers within `δ + B` of `faceDirectionCone P`", so the
cone-containment step is a hypothesis rather than a geometric consequence. This module is the
faithful-replacement infrastructure for any later faithfulness argument.
-/

namespace CRNT
namespace CraciunZSH

open Topology RealInnerProductSpace Real
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ## The main theorem, chamber-interior form -/

/-- **Lemma 9.7 in fully abstract chamber form.**

The hypothesis is only that each unit-section point of `C` has a ball lying inside
`chamber` (and hence `K`). No interior of `K` is required: a caller possessing the explicit ball
statement gets the conclusion directly. This is the statement the proof actually establishes, and
it is the reason the chamber hypothesis suffices. -/
theorem exists_eventual_tube_subset_of_chamber_affineInterior
    {C K chamber : Set E}
    (hCscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ C, a • x ∈ C)
    (hKscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ K, a • x ∈ K)
    (hCchamber : C ⊆ chamber)
    (hchamberK : chamber ⊆ K)
    (hsectionCompact : IsCompact (C ∩ Metric.sphere (0 : E) 1))
    (hsectionNonempty : (C ∩ Metric.sphere (0 : E) 1).Nonempty)
    (hradius : ∀ x ∈ C ∩ Metric.sphere (0 : E) 1,
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ chamber)
    (hradiusK : ∀ x ∈ C ∩ Metric.sphere (0 : E) 1,
      ∀ ρ : ℝ, Metric.ball x ρ ⊆ chamber → Metric.ball x ρ ⊆ K)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : E,
      Metric.infDist x C < δ → M < ‖x‖ → x ∈ K := by
  classical
  let unitSection : Set E := C ∩ Metric.sphere (0 : E) 1
  have hsection : IsCompact unitSection := by
    simpa [unitSection] using hsectionCompact
  -- the ball radius supplied by the chamber hypothesis at each unit-section point
  let radius : unitSection → ℝ := fun u => Classical.choose (hradius u.1 u.2)
  have hradius_pos : ∀ u : unitSection, 0 < radius u := by
    intro u
    exact (Classical.choose_spec (hradius u.1 u.2)).1
  have hball : ∀ u : unitSection, Metric.ball u.1 (radius u) ⊆ K := by
    intro u
    exact hradiusK u.1 u.2 (radius u) (Classical.choose_spec (hradius u.1 u.2)).2
  -- finite subcover of the compact unit section by the half-radius balls
  let U : unitSection → Set E := fun u => Metric.ball u.1 (radius u / 2)
  have hUopen : ∀ u : unitSection, IsOpen (U u) := fun _ => Metric.isOpen_ball
  have hUcover : unitSection ⊆ ⋃ u : unitSection, U u := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by
      dsimp [U]
      rw [Metric.mem_ball, dist_self]
      linarith [hradius_pos ⟨x, hx⟩]⟩
  obtain ⟨tiles, htiles⟩ := hsection.elim_finite_subcover U hUopen hUcover
  have htilesNonempty : tiles.Nonempty := by
    by_contra hne
    have htilesEmpty : tiles = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    obtain ⟨x, hx⟩ := hsectionNonempty
    have hxcover := htiles hx
    simp [htilesEmpty] at hxcover
  obtain ⟨u₀, hu₀, hmin⟩ :=
    Finset.exists_mem_eq_inf' htilesNonempty (fun u : unitSection => radius u / 2)
  let ρ : ℝ := tiles.inf' htilesNonempty (fun u : unitSection => radius u / 2)
  have hρ : 0 < ρ := by
    dsimp [ρ]
    rw [hmin]
    exact half_pos (hradius_pos u₀)
  have hρle (u : unitSection) (hu : u ∈ tiles) : ρ ≤ radius u / 2 := by
    dsimp [ρ]
    exact Finset.inf'_le _ hu
  refine ⟨δ + δ / ρ, by positivity, ?_⟩
  intro x hnear hlarge
  have hCne : C.Nonempty := by
    obtain ⟨u, hu⟩ := hsectionNonempty
    exact ⟨u, hu.1⟩
  obtain ⟨y, hyC, hxy⟩ := (Metric.infDist_lt_iff hCne).mp hnear
  have hxyNorm : ‖x - y‖ < δ := by
    simpa [dist_eq_norm] using hxy
  have hxTriangle : ‖x‖ ≤ ‖x - y‖ + ‖y‖ := by
    calc
      ‖x‖ = ‖(x - y) + y‖ := by congr 1; abel
      _ ≤ ‖x - y‖ + ‖y‖ := norm_add_le _ _
  have hyLarge : δ / ρ < ‖y‖ := by
    have hxUpper : ‖x‖ < δ + ‖y‖ := lt_of_le_of_lt hxTriangle (by linarith)
    linarith
  have hyNormPos : 0 < ‖y‖ := lt_trans (div_pos hδ hρ) hyLarge
  -- normalize `y` onto the unit section
  let u : E := (‖y‖)⁻¹ • y
  have hnormu : ‖u‖ = 1 := by
    dsimp [u]
    calc
      ‖(‖y‖)⁻¹ • y‖ = ‖(‖y‖)⁻¹‖ * ‖y‖ := norm_smul _ _
      _ = (‖y‖)⁻¹ * ‖y‖ := by
        rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyNormPos)]
      _ = 1 := inv_mul_cancel₀ (ne_of_gt hyNormPos)
  have huC : u ∈ C := hCscale (‖y‖)⁻¹ (le_of_lt (inv_pos.mpr hyNormPos)) y hyC
  have huSphere : u ∈ Metric.sphere (0 : E) 1 := by
    simp [Metric.sphere, dist_zero_right, hnormu]
  have huSection : u ∈ unitSection := ⟨huC, huSphere⟩
  -- find the covering tile and shrink the perturbation into its full-radius ball
  have huCover := htiles huSection
  simp only [Set.mem_iUnion] at huCover
  obtain ⟨v, hvTiles, hvU⟩ := huCover
  have huvBall : dist u v.1 < radius v / 2 := by
    simpa [U, Metric.mem_ball] using hvU
  have hpertNorm : ‖(‖y‖)⁻¹ • (x - y)‖ = ‖x - y‖ / ‖y‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyNormPos), inv_mul_eq_div]
  have hpertSmall : ‖(‖y‖)⁻¹ • (x - y)‖ < ρ := by
    rw [hpertNorm]
    apply (div_lt_iff₀ hyNormPos).2
    have hρy' : δ < ‖y‖ * ρ := (div_lt_iff₀ hρ).mp hyLarge
    have hρy : δ < ρ * ‖y‖ := by simpa [mul_comm] using hρy'
    linarith
  have hpertTile : ‖(‖y‖)⁻¹ • (x - y)‖ < radius v / 2 :=
    lt_of_lt_of_le hpertSmall (hρle v hvTiles)
  have hxScaledBall :
      u + (‖y‖)⁻¹ • (x - y) ∈ Metric.ball v.1 (radius v) := by
    rw [Metric.mem_ball, dist_eq_norm]
    calc
      ‖u + (‖y‖)⁻¹ • (x - y) - v.1‖
          = ‖(u - v.1) + (‖y‖)⁻¹ • (x - y)‖ := by congr 1; abel
      _ ≤ ‖u - v.1‖ + ‖(‖y‖)⁻¹ • (x - y)‖ := norm_add_le _ _
      _ < radius v / 2 + radius v / 2 :=
        add_lt_add (by simpa [dist_eq_norm] using huvBall) hpertTile
      _ = radius v := by ring
  -- **the chamber step**: the scaled point is in `K ∩ affineSpan ℝ chamber`, hence in `K`
  have hxScaledK : (‖y‖)⁻¹ • x ∈ K := by
    have hdecomp : (‖y‖)⁻¹ • x = u + (‖y‖)⁻¹ • (x - y) := by
      dsimp [u]
      rw [← smul_add]
      congr 1
      abel
    rw [hdecomp]
    exact hball v hxScaledBall
  have hrescale : ‖y‖ • ((‖y‖)⁻¹ • x) = x := by
    rw [smul_smul]
    simp [hyNormPos.ne']
  have hxK : ‖y‖ • ((‖y‖)⁻¹ • x) ∈ K :=
    hKscale ‖y‖ hyNormPos.le ((‖y‖)⁻¹ • x) hxScaledK
  rw [hrescale] at hxK
  exact hxK

/-- **Lemma 9.7 in relative-interior (chamber) form.**

Let `C` and `K` be cones (`a • x ∈ C` for `a ≥ 0`, likewise for `K`), let `chamber` be a set with
`C ⊆ chamber ⊆ K`, and suppose the unit section `C ∩ sphere 0 1` is compact, nonempty, and each of
its points is interior to `chamber`. Then for every `δ > 0` there is `M > 0` such that every `x`
within distance `δ` of `C` and of norm greater than `M` lies in `K`.

This is the conclusion of `exists_eventual_tube_subset_of_cone_interior` verbatim; the hypothesis
`C ⊆ interior K` has been replaced by the chamber-relative one, which is satisfiable on symmetry
hyperplanes where the original is not. -/
theorem exists_eventual_tube_subset_of_chamber_interior
    {C K chamber : Set E}
    (hCscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ C, a • x ∈ C)
    (hKscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ K, a • x ∈ K)
    (hCchamber : C ⊆ chamber)
    (hchamberK : chamber ⊆ K)
    (hsectionCompact : IsCompact (C ∩ Metric.sphere (0 : E) 1))
    (hsectionNonempty : (C ∩ Metric.sphere (0 : E) 1).Nonempty)
    (hinterior : ∀ x ∈ C ∩ Metric.sphere (0 : E) 1, x ∈ interior chamber)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : E,
      Metric.infDist x C < δ → M < ‖x‖ → x ∈ K := by
  classical
  -- discharge the abstract hypothesis: interior points of `chamber` have a ball inside `chamber`,
  -- and `chamber ⊆ K`, so that ball lies in `K`.
  have hradius : ∀ x ∈ C ∩ Metric.sphere (0 : E) 1,
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ chamber := by
    intro x hx
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x (hinterior x hx)
    exact ⟨ρ, hρ, fun z hz => interior_subset (hball hz)⟩
  exact exists_eventual_tube_subset_of_chamber_affineInterior hCscale hKscale hCchamber hchamberK
    hsectionCompact hsectionNonempty hradius (fun _ _ _ h => h.trans hchamberK) hδ

/-! ## Closed-cone and finite-family forms -/

/-- **The closed-cone chamber form, in a proper space.**  Matches
`exists_eventual_tube_subset_of_closed_cone_interior` with `C ⊆ interior K` replaced by
`C ⊆ chamber ⊆ K` together with interiority of the unit-section points inside `chamber`. -/
theorem exists_eventual_tube_subset_of_closed_cone_chamber
    [ProperSpace E] {C K chamber : Set E}
    (hCclosed : IsClosed C)
    (hCscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ C, a • x ∈ C)
    (hKscale : ∀ a : ℝ, 0 ≤ a → ∀ x ∈ K, a • x ∈ K)
    (hCchamber : C ⊆ chamber) (hchamberK : chamber ⊆ K)
    (hinterior : ∀ x ∈ C ∩ Metric.sphere (0 : E) 1, x ∈ interior chamber)
    (hCnonzero : ∃ x ∈ C, x ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ x : E,
      Metric.infDist x C < δ → M < ‖x‖ → x ∈ K := by
  have hsectionCompact : IsCompact (C ∩ Metric.sphere (0 : E) 1) := by
    exact (isCompact_sphere (0 : E) 1).of_isClosed_subset
      (hCclosed.inter Metric.isClosed_sphere) Set.inter_subset_right
  have hsectionNonempty : (C ∩ Metric.sphere (0 : E) 1).Nonempty := by
    obtain ⟨y, hyC, hyNe⟩ := hCnonzero
    have hyNorm : 0 < ‖y‖ := norm_pos_iff.mpr hyNe
    let u : E := (‖y‖)⁻¹ • y
    have huNorm : ‖u‖ = 1 := by
      dsimp [u]
      calc
        ‖(‖y‖)⁻¹ • y‖ = ‖(‖y‖)⁻¹‖ * ‖y‖ := norm_smul _ _
        _ = (‖y‖)⁻¹ * ‖y‖ := by
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hyNorm)]
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hyNorm)
    have huC : u ∈ C := hCscale (‖y‖)⁻¹ (le_of_lt (inv_pos.mpr hyNorm)) y hyC
    have huSphere : u ∈ Metric.sphere (0 : E) 1 := by
      simp [Metric.sphere, dist_zero_right, huNorm]
    exact ⟨u, huC, huSphere⟩
  exact exists_eventual_tube_subset_of_chamber_interior hCscale hKscale hCchamber hchamberK
    hsectionCompact hsectionNonempty hinterior hδ

/-- **Finite-family chamber form of Lemma 9.7.**  A single scale works for every cone of a finite
family, each equipped with its own chamber. This is the form a fan application needs: the fan
supplies the finite index, each cell supplies `C i`, `K i` and `chamber i`. -/
theorem exists_uniform_eventual_tube_subset_of_chamber_pairs
    {ι : Type*} [Fintype ι] [Nonempty ι] [ProperSpace E]
    (C K chamber : ι → Set E)
    (hCclosed : ∀ i, IsClosed (C i))
    (hCscale : ∀ i (a : ℝ), 0 ≤ a → ∀ x ∈ C i, a • x ∈ C i)
    (hKscale : ∀ i (a : ℝ), 0 ≤ a → ∀ x ∈ K i, a • x ∈ K i)
    (hCchamber : ∀ i, C i ⊆ chamber i)
    (hchamberK : ∀ i, chamber i ⊆ K i)
    (hinterior : ∀ i (x : E), x ∈ C i ∩ Metric.sphere (0 : E) 1 → x ∈ interior (chamber i))
    (hCnonzero : ∀ i, ∃ x ∈ C i, x ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i x,
      Metric.infDist x (C i) < δ → M < ‖x‖ → x ∈ K i := by
  classical
  let Mi : ι → ℝ := fun i => Classical.choose
    (exists_eventual_tube_subset_of_closed_cone_chamber (hCclosed i) (hCscale i) (hKscale i)
      (hCchamber i) (hchamberK i) (hinterior i) (hCnonzero i) hδ)
  have hMiSpec (i : ι) : 0 < Mi i ∧ ∀ x,
      Metric.infDist x (C i) < δ → Mi i < ‖x‖ → x ∈ K i := by
    dsimp [Mi]
    exact Classical.choose_spec
      (exists_eventual_tube_subset_of_closed_cone_chamber (hCclosed i) (hCscale i) (hKscale i)
        (hCchamber i) (hchamberK i) (hinterior i) (hCnonzero i) hδ)
  let M : ℝ := ∑ i, Mi i
  have hM : 0 < M := by
    dsimp [M]
    exact Finset.sum_pos (fun i _ => (hMiSpec i).1) Finset.univ_nonempty
  refine ⟨M, hM, ?_⟩
  intro i x hnear hlarge
  have hMiLe : Mi i ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum (fun j _ => (hMiSpec j).1.le) (Finset.mem_univ i)
  exact (hMiSpec i).2 x hnear (lt_of_le_of_lt hMiLe hlarge)

/-! ### The packaged `ProperCone` specialization, in chamber form -/

/-- **Finite `ProperCone` pairs, chamber form.**  The direct replacement for
`exists_uniform_eventual_tube_subset_of_finite_properCone_pairs`, whose hypothesis
`hinterior : ∀ i, (C i : Set E) ⊆ interior (K i : Set E)` is false on symmetry hyperplanes.

Each cone `C i` gets a `chamber i` with `C i ⊆ chamber i ⊆ K i`, and interiority is required only
of the unit-section points of `C i` inside `chamber i`. -/
theorem exists_uniform_eventual_tube_subset_of_chamber_properCone_pairs
    {ι : Type*} [Fintype ι] [Nonempty ι] [ProperSpace E]
    (C K : ι → ProperCone ℝ E) (chamber : ι → Set E)
    (hCchamber : ∀ i, (C i : Set E) ⊆ chamber i)
    (hchamberK : ∀ i, chamber i ⊆ (K i : Set E))
    (hinterior : ∀ i (x : E), x ∈ (C i : Set E) ∩ Metric.sphere (0 : E) 1 →
      x ∈ interior (chamber i))
    (hCnonzero : ∀ i, ∃ x ∈ (C i : Set E), x ≠ 0)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i x,
      Metric.infDist x (C i : Set E) < δ → M < ‖x‖ → x ∈ (K i : Set E) := by
  classical
  exact exists_uniform_eventual_tube_subset_of_chamber_pairs
    (fun i => (C i : Set E)) (fun i => (K i : Set E)) chamber
    (fun i => (C i).isClosed)
    (fun i a ha y hy => (C i).smul_mem hy ha)
    (fun i a ha y hy => (K i).smul_mem hy ha)
    hCchamber hchamberK hinterior hCnonzero hδ

end CraciunZSH
end CRNT