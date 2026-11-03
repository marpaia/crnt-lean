import CRNT.Geometry.ConeFace
import CRNT.Geometry.ToricFan
import CRNT.Geometry.PolyhedralBarrier
import CRNT.Dynamics.ComplexBalanceStoichFanInclusion

/-!
# Fan axioms, the δ-core, and the descent bridge to a polyhedral barrier

`CRNT.Geometry.ConeFace` already records the fan axioms of Craciun v3 Definition 4.1 as
`CRNT.IsPolyhedralFan` (closure under exposed faces, pairwise intersections again cones of the
family, and covering), and `Network.relativeSourceOrderNegativeStoichFan_isPolyhedralFan` proves
them for the fan the complex-balanced embedding uses.  This module

* derives from those axioms that the family is closed under lattice intersection, and builds the
  **δ-core** of a point — the intersection of all cones of the fan within distance `δ` — showing it
  is again a cone of the fan;
* proves the descent bridge (Craciun v3 Remark 4.5): a vector lying in every cone within `δ` of `X`
  has nonnegative inner product against the whole toric field at `X`;
* combines that with `CRNT.PolyhedralBarrier` to give forward invariance of a polyhedral region for
  the toric differential inclusion.

## The sign convention

`CRNT.coneDual s` is the **dual** cone, `{y | ∀ x ∈ s, 0 ≤ ⟪x, y⟫}`, whereas Craciun's `Cᵒ` is the
**polar** cone `{y | ∀ x ∈ C, ⟪x, y⟫ ≤ 0}`.  `toricField` is built from `coneDual`, so admissible
velocities `v` satisfy `0 ≤ ⟪n, v⟫` for `n` in the relevant cones.  A barrier must *decrease*, so
the barrier normals are the negatives: the guarded region is a sublevel set of
`barrier (fun i => innerSL ℝ (-n i)) b`.  This is bookkeeping only, and it is done once, in
`forwardInvariant_barrier_toricInclusion` below.

## What this does and does not supply

It supplies the descent half of Craciun's Theorem B: *given* one normal per tile with the normal
lying in every fan cone near that tile, the polyhedral region traps the flow.  It does **not**
construct those normals and tiles; that is the §7 blueprint, still open.  See
`HANDOFF_gac_hole.md` §4 for why the tiles cannot be taken to bound a convex region, and
`CRNT.Geometry.ConvexBarrierObstruction` for the formalized obstruction.

Nothing here is an axiom or a `sorry`.

Depends on: `CRNT.Geometry.ToricFan`, `CRNT.Geometry.PolyhedralBarrier`, Mathlib cone faces.
-/

namespace CRNT

open scoped InnerProductSpace

section FanAxioms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Closure under intersection -/

namespace IsPolyhedralFan

variable {F : Fan E}

/-- A polyhedral fan is closed under lattice intersection.  The `inter_common` axiom produces a
cone of `F` whose *carrier* is `C ∩ D`, and a proper cone is determined by its carrier, so that
cone is `C ⊓ D` on the nose. -/
theorem inf_mem (hF : IsPolyhedralFan F) {C D : ProperCone ℝ E} (hC : C ∈ F) (hD : D ∈ F) :
    C ⊓ D ∈ F := by
  obtain ⟨G, hGF, hGset⟩ := hF.inter_common C hC D hD
  have : G = C ⊓ D := by
    apply SetLike.coe_injective
    rw [hGset]
    rfl
  rwa [this] at hGF

/-- Completeness in the form the constructions below use: every point lies in some cone. -/
theorem exists_mem (hF : IsPolyhedralFan F) (X : E) : ∃ C ∈ F, X ∈ C := by
  have hX : X ∈ (Set.univ : Set E) := Set.mem_univ X
  rw [← hF.covers, Set.mem_iUnion₂] at hX
  obtain ⟨C, hCF, hXC⟩ := hX
  exact ⟨C, hCF, hXC⟩

end IsPolyhedralFan

/-! ### The δ-core -//-! ### Finite intersections of fan cones -/

/-- The intersection of a nonempty finite family of cones.  Both the δ-core below and the
face-relevant core of `CRNT.Dynamics.FaceDirectionCone` are instances of it. -/
noncomputable def subfanCore (s : Finset (ProperCone ℝ E)) (h : s.Nonempty) : ProperCone ℝ E :=
  s.inf' h id

omit [CompleteSpace E] in
theorem subfanCore_le {s : Finset (ProperCone ℝ E)} (h : s.Nonempty)
    {C : ProperCone ℝ E} (hC : C ∈ s) : subfanCore s h ≤ C :=
  Finset.inf'_le (f := id) hC

omit [CompleteSpace E] in
theorem mem_of_mem_subfanCore {s : Finset (ProperCone ℝ E)} (h : s.Nonempty) {n : E}
    (hn : n ∈ subfanCore s h) : ∀ C ∈ s, n ∈ C :=
  fun _ hC => subfanCore_le h hC hn

/-- **A finite intersection of cones of a fan is a cone of the fan.**  The axioms make the family
closed under binary intersection, and a set closed under `⊓` contains the `inf'` of every nonempty
finite subfamily of it. -/
theorem subfanCore_mem {F : Fan E} (hF : IsPolyhedralFan F) {s : Finset (ProperCone ℝ E)}
    (hs : ∀ C ∈ s, C ∈ F) (h : s.Nonempty) : subfanCore s h ∈ F :=
  Finset.inf'_mem (↑F : Set (ProperCone ℝ E)) (fun _ hC _ hD => hF.inf_mem hC hD) _ h id hs

/-! ### The δ-core -/

/-- The cones of `F` lying within distance `δ` of `X` — exactly the cones whose polars generate the
toric field at `X`. -/
noncomputable def nearCones (F : Fan E) (δ : ℝ) (X : E) : Finset (ProperCone ℝ E) :=
  letI := Classical.decPred fun C : ProperCone ℝ E => Metric.infDist X (C : Set E) < δ
  F.filter fun C => Metric.infDist X (C : Set E) < δ

theorem mem_nearCones {F : Fan E} {δ : ℝ} {X : E} {C : ProperCone ℝ E} :
    C ∈ nearCones F δ X ↔ C ∈ F ∧ Metric.infDist X (C : Set E) < δ := by
  classical
  simp only [nearCones, Finset.mem_filter]

/-- Completeness makes the near-cone family nonempty: the cone containing `X` is at distance `0`. -/
theorem nearCones_nonempty {F : Fan E} (hF : IsPolyhedralFan F) {δ : ℝ} (hδ : 0 < δ) (X : E) :
    (nearCones F δ X).Nonempty := by
  obtain ⟨C, hCF, hXC⟩ := hF.exists_mem X
  refine ⟨C, mem_nearCones.2 ⟨hCF, ?_⟩⟩
  rw [Metric.infDist_zero_of_mem hXC]
  exact hδ

/-- **The δ-core of `X`.**  The intersection of every cone of `F` within distance `δ` of `X`.  By
Craciun v3 Remark 4.5, the outer normal of a zero-separating hypersurface at a point `P` must lie
in this cone, and conversely any vector in it certifies the non-crossing condition at `P`. -/
noncomputable def deltaCore (F : Fan E) (δ : ℝ) (X : E)
    (h : (nearCones F δ X).Nonempty) : ProperCone ℝ E :=
  (nearCones F δ X).inf' h id

theorem deltaCore_eq_subfanCore {F : Fan E} {δ : ℝ} {X : E} (h : (nearCones F δ X).Nonempty) :
    deltaCore F δ X h = subfanCore (nearCones F δ X) h := rfl

theorem deltaCore_le {F : Fan E} {δ : ℝ} {X : E} (h : (nearCones F δ X).Nonempty)
    {C : ProperCone ℝ E} (hC : C ∈ nearCones F δ X) :
    deltaCore F δ X h ≤ C :=
  Finset.inf'_le (f := id) hC

/-- Anything in the δ-core lies in every cone of `F` within `δ` of `X` — the hypothesis the descent
bridge below consumes. -/
theorem mem_of_mem_deltaCore {F : Fan E} {δ : ℝ} {X n : E} (h : (nearCones F δ X).Nonempty)
    (hn : n ∈ deltaCore F δ X h) :
    ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → n ∈ C := by
  intro C hCF hCd
  exact deltaCore_le h (mem_nearCones.2 ⟨hCF, hCd⟩) hn

/-- **The δ-core is a cone of the fan.**  The fan axioms make `F` closed under intersection, and a
finite intersection of a nonempty subfamily stays inside a set closed under binary intersection. -/
theorem deltaCore_mem {F : Fan E} (hF : IsPolyhedralFan F) {δ : ℝ} {X : E}
    (h : (nearCones F δ X).Nonempty) :
    deltaCore F δ X h ∈ F := by
  refine Finset.inf'_mem (↑F : Set (ProperCone ℝ E)) ?_ _ h id ?_
  · intro C hC D hD
    exact hF.inf_mem hC hD
  · intro C hC
    exact (mem_nearCones.1 hC).1

/-! ### The descent bridge (Craciun v3, Remark 4.5) -/

/-- **A vector in every nearby cone descends against the whole toric field.**

If `n` lies in every cone of `F` within distance `δ` of `X`, then `0 ≤ ⟪n, v⟫` for every admissible
velocity `v` of the toric field at `X`.  The generators of the field are the *dual* cones of those
cones, so each generator already satisfies the inequality; the inequality defines the dual cone of
`{n}`, which is itself a cone, so it survives taking the conical hull. -/
theorem inner_nonneg_of_mem_toricField {F : Fan E} {δ : ℝ} {X n : E}
    (hn : ∀ C ∈ F, Metric.infDist X (C : Set E) < δ → n ∈ C) :
    ∀ v ∈ toricField F δ X, 0 ≤ ⟪n, v⟫_ℝ := by
  have hle : toricField F δ X ≤ (coneDual ({n} : Set E)).toSubmodule := by
    refine Submodule.span_le.mpr ?_
    intro y hy
    obtain ⟨C, hCF, hCd, hyC⟩ := mem_toricGenerators.1 hy
    refine mem_coneDual.2 ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact mem_coneDual.1 hyC (hn C hCF hCd)
  intro v hv
  exact mem_coneDual.1 (hle hv) (Set.mem_singleton n)

/-- The δ-core form of the descent bridge. -/
theorem inner_nonneg_of_mem_deltaCore {F : Fan E} {δ : ℝ} {X n : E}
    (h : (nearCones F δ X).Nonempty) (hn : n ∈ deltaCore F δ X h) :
    ∀ v ∈ toricField F δ X, 0 ≤ ⟪n, v⟫_ℝ :=
  inner_nonneg_of_mem_toricField (mem_of_mem_deltaCore h hn)

end FanAxioms

/-! ### Forward invariance of a polyhedral region for the toric inclusion -/

section Inclusion

open scoped RealInnerProductSpace

variable {S : Type*} [Fintype S]
variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- **A polyhedral barrier whose normals lie in the nearby fan cones traps the toric inclusion.**

The data is one normal `n i` and one level `b i` per piece.  The hypothesis is the localised
Craciun condition: wherever piece `i` is the active one and the barrier has reached the level `R`,
the normal `n i` lies in *every* cone of `F` within `δ` of the log-coordinates of that point.
Nothing is required of the inactive pieces, and nothing at all below the level.

The guarded region is a sublevel set of the barrier built from the *negated* normals, because
`toricField` is generated by `coneDual` (nonnegative inner product) while a barrier must decrease;
see the module docstring.

This is the descent half of Craciun v3 Theorem B.  The missing half is the construction of the
normals and their tiles — the §7 blueprint. -/
theorem forwardInvariant_barrier_toricInclusion
    {F : Fan (EuclideanSpace ℝ S)} {δ : ℝ}
    {n : ι → EuclideanSpace ℝ S} {b : ι → ℝ} {R : ℝ}
    (hn : ∀ y : EuclideanSpace ℝ S,
      R ≤ PolyhedralBarrier.barrier (fun i => innerSL ℝ (-n i)) b y →
      ∀ i : ι,
        innerSL ℝ (-n i) y - b i
          = PolyhedralBarrier.barrier (fun i => innerSL ℝ (-n i)) b y →
        ∀ C ∈ F, Metric.infDist (logCoords y) (C : Set (EuclideanSpace ℝ S)) < δ → n i ∈ C) :
    DifferentialInclusion.ForwardInvariant (toricInclusionField F δ)
      {x : EuclideanSpace ℝ S |
        PolyhedralBarrier.barrier (fun i => innerSL ℝ (-n i)) b x ≤ R} := by
  refine PolyhedralBarrier.forwardInvariant_barrierSublevel ?_
  intro y hlevel i hactive c hc
  have hfield : 0 ≤ ⟪n i, c⟫ :=
    inner_nonneg_of_mem_toricField (hn y hlevel i hactive) c
      (mem_toricInclusionField.1 hc)
  have : innerSL ℝ (-n i) c = -⟪n i, c⟫ := by
    simp [innerSL_apply_apply]
  rw [this]
  linarith

end Inclusion

/-! ### The complex-balanced mass-action case -/

section MassAction

open scoped RealInnerProductSpace

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The mass-action velocity, transported into the intrinsic Euclidean stoichiometric space where
the source-order fan lives.  This is the subtype term that
`Network.massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan` produces. -/
noncomputable def Network.euclideanMassActionField (N : Network S) (κ : N.RateConstants)
    (x : Concentration S) : N.euclideanStoichSubspace :=
  ⟨CRNT.toEuclid (N.massActionVectorField κ x), by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨N.massActionVectorField κ x, N.massActionVectorField_mem_stoichSubspace κ x, rfl⟩⟩

/-- The point of the intrinsic stoichiometric space at which the fan is read: minus the
stoichiometric projection of the relative logarithm `log x - log x*`. -/
noncomputable def Network.relativeLogFanState (N : Network S) (xstar x : Concentration S) :
    N.euclideanStoichSubspace :=
  -⟨CRNT.toEuclid (N.relativeLogStoichProjection fun s => Real.log (x s) - Real.log (xstar s)), by
    rw [Network.euclideanStoichSubspace, Submodule.mem_map]
    exact ⟨_, N.relativeLogStoichProjection_mem _, rfl⟩⟩

/-- Restatement of the complex-balanced embedding (Craciun v3 Theorem 3.1, already proved in
`CRNT.Dynamics.ComplexBalanceStoichFanInclusion`) in the named form used below. -/
theorem Network.euclideanMassActionField_mem_toricField (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ) :
    N.euclideanMassActionField κ x ∈
      CRNT.toricField N.relativeSourceOrderNegativeStoichFan δ
        (N.relativeLogFanState xstar x) := by
  simpa [Network.euclideanMassActionField, Network.relativeLogFanState] using
    N.massActionVectorField_mem_toricField_relativeSourceOrderNegativeStoichFan κ hx hxs hcb hδ

/-- The near-cone family of the source-order fan is never empty, by completeness of the fan. -/
theorem Network.nearCones_nonempty (N : Network S) {δ : ℝ} (hδ : 0 < δ)
    (X : N.euclideanStoichSubspace) :
    (nearCones N.relativeSourceOrderNegativeStoichFan δ X).Nonempty :=
  CRNT.nearCones_nonempty N.relativeSourceOrderNegativeStoichFan_isPolyhedralFan hδ X

/-- **The δ-core of the source-order fan is a cone of that fan.**  This is the cone Craciun's
Remark 4.5 forces the outer normal of the zero-separating hypersurface to lie in, and the fan
axioms — already proved for this fan — make it an actual member of the family, so the blueprint
construction has a canonical target to pick its normals from. -/
theorem Network.deltaCore_mem (N : Network S) {δ : ℝ} {X : N.euclideanStoichSubspace}
    (h : (nearCones N.relativeSourceOrderNegativeStoichFan δ X).Nonempty) :
    deltaCore N.relativeSourceOrderNegativeStoichFan δ X h ∈
      N.relativeSourceOrderNegativeStoichFan :=
  CRNT.deltaCore_mem N.relativeSourceOrderNegativeStoichFan_isPolyhedralFan h

/-- **Descent of a fan normal against the complex-balanced mass-action field.**

If `n` lies in every cone of the source-order fan within `δ` of the relative-log state of `x`, then
`n` pairs nonnegatively with the mass-action velocity at `x`.  Equivalently `-n` is a valid
barrier normal there: this is the single inequality a polyhedral zero-separating surface needs at
each of its faces. -/
theorem Network.inner_euclideanMassActionField_nonneg (N : Network S) (κ : N.RateConstants)
    {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ)
    {n : N.euclideanStoichSubspace}
    (hn : ∀ C ∈ N.relativeSourceOrderNegativeStoichFan,
      Metric.infDist (N.relativeLogFanState xstar x) (C : Set N.euclideanStoichSubspace) < δ →
        n ∈ C) :
    0 ≤ ⟪n, N.euclideanMassActionField κ x⟫ :=
  inner_nonneg_of_mem_toricField hn _
    (N.euclideanMassActionField_mem_toricField κ hx hxs hcb hδ)

/-- The δ-core form: any vector of the δ-core at the relative-log state descends against the
mass-action field. -/
theorem Network.inner_euclideanMassActionField_nonneg_of_mem_deltaCore (N : Network S)
    (κ : N.RateConstants) {x xstar : Concentration S} (hx : x.Positive) (hxs : xstar.Positive)
    (hcb : N.IsComplexBalanced κ xstar) {δ : ℝ} (hδ : 0 < δ)
    (h : (nearCones N.relativeSourceOrderNegativeStoichFan δ
      (N.relativeLogFanState xstar x)).Nonempty)
    {n : N.euclideanStoichSubspace}
    (hn : n ∈ deltaCore N.relativeSourceOrderNegativeStoichFan δ
      (N.relativeLogFanState xstar x) h) :
    0 ≤ ⟪n, N.euclideanMassActionField κ x⟫ :=
  N.inner_euclideanMassActionField_nonneg κ hx hxs hcb hδ (mem_of_mem_deltaCore h hn)

end MassAction

end CRNT
