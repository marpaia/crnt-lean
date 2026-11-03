import CRNT.Oscillation.Basic

/-!
# The concentration space with its `ℓ²` structure

`Concentration S` is the abbreviation `S → ℝ` and therefore carries Mathlib's **sup** norm
(`Pi.normedAddCommGroup`), which is not induced by an inner product.  The transversal-section
API (`CRNT.TransversalSection`) defines its affine section by `⟪y - point, normal⟫` and so
requires `InnerProductSpace ℝ E`; `CRNT.PersistentReturnOrbitData` and
`CRNT.ScalarPersistentReturnOrbitData` inherit that requirement because they carry a
`TransversalSection`.

Instantiating any of those at `Concentration S` therefore does not typecheck, and the failure
cannot be repaired by adding an instance: no inner product induces the sup norm.  This module
supplies the `ℓ²` model

    ConcentrationE S = EuclideanSpace ℝ S

together with the transport of vector fields and of periodic trajectories across the
identification.  In finite dimension the two norms are equivalent, so neighbourhood filters,
continuity and persistence statements transfer unchanged; only the inner-product structure is
added.

This is the same correction already carried by `Phase2`, which is `EuclideanSpace ℝ (Fin 2)`
rather than `Fin 2 → ℝ` for exactly this reason.

Depends on: `CRNT.Oscillation.Basic`.
-/

namespace CRNT

variable {S : Type} [DecidableEq S] [Fintype S]

/-- The concentration space carried with the `ℓ²` inner product. -/
abbrev ConcentrationE (S : Type) := EuclideanSpace ℝ S

/-- The `ℓ²`/sup identification of the concentration space, as a continuous linear
equivalence.  It is the identity on underlying functions. -/
noncomputable def concentrationE : ConcentrationE S ≃L[ℝ] Concentration S :=
  PiLp.continuousLinearEquiv 2 ℝ (fun _ : S => ℝ)

omit [DecidableEq S] [Fintype S] in
@[simp] theorem concentrationE_apply (x : ConcentrationE S) :
    concentrationE x = WithLp.ofLp x := rfl

omit [DecidableEq S] [Fintype S] in
@[simp] theorem concentrationE_symm_apply (x : Concentration S) :
    (concentrationE (S := S)).symm x = WithLp.toLp 2 x := rfl

/-- Transport a concentration vector field to the `ℓ²` model.  The underlying function is
unchanged; only the norm on the source and target differs. -/
def euclideanField (f : Concentration S → Concentration S) :
    ConcentrationE S → ConcentrationE S :=
  fun x => WithLp.toLp 2 (f (WithLp.ofLp x))

omit [DecidableEq S] [Fintype S] in
@[simp] theorem ofLp_euclideanField (f : Concentration S → Concentration S)
    (x : ConcentrationE S) :
    WithLp.ofLp (euclideanField f x) = f (WithLp.ofLp x) := rfl

/-- A periodic trajectory of the transported field is a periodic trajectory of the original
field.  The orbit is literally the same function; the derivative is transported along the
continuous linear equivalence, which is why no regularity is lost. -/
noncomputable def PeriodicTrajectory.ofEuclidean
    {f : Concentration S → Concentration S}
    (P : PeriodicTrajectory (euclideanField f)) : PeriodicTrajectory f where
  orbit := fun t => WithLp.ofLp (P.orbit t)
  period := P.period
  period_pos := P.period_pos
  solution := fun t => by
    have h := (concentrationE (S := S)).hasFDerivAt.comp_hasDerivAt t (P.solution t)
    simpa [Function.comp_def] using h
  periodic := fun t => congrArg WithLp.ofLp (P.periodic t)
  nonconstant := by
    obtain ⟨t, ht⟩ := P.nonconstant
    exact ⟨t, fun h => ht (concentrationE.injective h)⟩

@[simp] theorem PeriodicTrajectory.ofEuclidean_orbit
    {f : Concentration S → Concentration S}
    (P : PeriodicTrajectory (euclideanField f)) (t : ℝ) :
    (PeriodicTrajectory.ofEuclidean P).orbit t = WithLp.ofLp (P.orbit t) := rfl

end CRNT
