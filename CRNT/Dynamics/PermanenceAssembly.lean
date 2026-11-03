import CRNT.Dynamics.GlobalPermanence
import CRNT.Theorems.DeficiencyZero.AsymptoticStability

/-!
# Generic assembly of class-uniform permanence

This module isolates the final, network-independent step in the standard permanence argument.
If every positive orbit in a stoichiometric compatibility class eventually enters a set `Υ`, and
all forward trajectories starting in `Υ` admit one common positive coordinate lower bound and one
common upper bound, then the class has a compact interior absorbing set.

The point is to separate the hard CRNT input (obtaining uniform bounds, e.g. from tier/Lyapunov
arguments) from the generic flow/topology argument turning those bounds into standard permanence.
-/

open scoped BigOperators NNReal ENNReal Topology
open Filter

namespace CRNT
namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]

/-- A genuine mass-action forward flow preserves stoichiometric compatibility with its starting
point. -/
theorem IsMassActionFlow.stoichCompatible {N : Network S} {κ : N.RateConstants}
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hflow : N.IsMassActionFlow κ ϕ γ) (x₀ : Concentration S) (t : ℝ≥0) :
    N.StoichCompatible x₀ (ϕ t x₀) := by
  rcases hflow with ⟨hzero, hflowγ, hsol⟩
  rw [StoichCompatible, hflowγ x₀ t]
  have h := N.sub_mem_stoichSubspace_of_solution κ t.coe_nonneg
    (fun u hu => hsol x₀ u hu.1)
  rwa [hzero x₀] at h

/-- A fixed stoichiometric compatibility class is closed. -/
theorem isClosed_compatibilityClass (N : Network S) (xref : Concentration S) :
    IsClosed (N.compatibilityClass xref) := by
  have hcont : Continuous (fun x : Concentration S => x - xref) :=
    continuous_id.sub continuous_const
  -- `⁻¹'` and the set-builder form of `compatibilityClass` are definitionally equal, so `exact`
  -- goes through where `simpa` stalls on the `Set.preimage` vs `setOf` mismatch.
  exact (Submodule.closed_of_finiteDimensional N.stoichSubspace).preimage hcont

/-- The closed coordinate box `[m,M]^S`. -/
def coordinateBox (m M : ℝ) : Set (Concentration S) :=
  {x | ∀ s : S, x s ∈ Set.Icc m M}

/-- Finite coordinate boxes are compact. -/
theorem isCompact_coordinateBox (m M : ℝ) :
    IsCompact (coordinateBox (S := S) m M) := by
  simpa [coordinateBox] using
    (isCompact_pi_infinite (s := fun _ : S => Set.Icc m M) (fun _ => isCompact_Icc))

/-- A compatibility-class slice of a coordinate box. -/
def classInteriorBox (N : Network S) (xref : Concentration S) (m M : ℝ) :
    Set (Concentration S) :=
  N.compatibilityClass xref ∩ coordinateBox (S := S) m M

/-- A compatibility-class coordinate box is compact. -/
theorem isCompact_classInteriorBox (N : Network S) (xref : Concentration S) (m M : ℝ) :
    IsCompact (N.classInteriorBox xref m M) := by
  exact (isCompact_coordinateBox (S := S) m M).inter_left (N.isClosed_compatibilityClass xref)

/-- If the lower coordinate bound is positive, the class box lies in the positive compatibility
class. -/
theorem classInteriorBox_subset_positiveCompatibilityClass (N : Network S)
    (xref : Concentration S) {m M : ℝ} (hm : 0 < m) :
    N.classInteriorBox xref m M ⊆ N.positiveCompatibilityClass xref := by
  intro x hx
  refine ⟨hx.1, ?_⟩
  intro s
  exact lt_of_lt_of_le hm (hx.2 s).1

/-- Every trajectory starting in `Υ` shares one positive coordinate lower bound and one coordinate
upper bound, uniformly over all future times and species. -/
def UniformForwardCoordinateBounds (ϕ : Flow ℝ≥0 (Concentration S))
    (Υ : Set (Concentration S)) : Prop :=
  ∃ m M : ℝ, 0 < m ∧
    ∀ x ∈ Υ, ∀ t : ℝ≥0, ∀ s : S, m ≤ ϕ t x s ∧ ϕ t x s ≤ M

/-- Every positive orbit in the class of `xref` reaches `Υ` at some forward time. -/
def EveryPositiveClassOrbitEnters (N : Network S) (ϕ : Flow ℝ≥0 (Concentration S))
    (xref : Concentration S) (Υ : Set (Concentration S)) : Prop :=
  ∀ x₀ ∈ N.positiveCompatibilityClass xref, ∃ τ : ℝ≥0, ϕ τ x₀ ∈ Υ

/-- **Generic permanence assembly theorem.**

Suppose every positive orbit in the class of `xref` eventually reaches `Υ`, and every trajectory
starting in `Υ` subsequently has common coordinate bounds `m ≤ x_s(t) ≤ M` with `m > 0`.  For a
genuine mass-action flow, the compatibility class is invariant.  Therefore the fixed compact set

`compatibilityClass(xref) ∩ [m,M]^S`

absorbs a tail of every positive orbit in the class.  This is exactly standard class-uniform
permanence. -/
theorem permanentOnPositiveClass_of_entry_and_uniform_bounds
    {N : Network S} {κ : N.RateConstants}
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hflow : N.IsMassActionFlow κ ϕ γ) {xref : Concentration S} {Υ : Set (Concentration S)}
    (hentry : N.EveryPositiveClassOrbitEnters ϕ xref Υ)
    (hbounds : UniformForwardCoordinateBounds ϕ Υ) :
    N.PermanentOnPositiveClass ϕ xref := by
  obtain ⟨m, M, hm, hbounds⟩ := hbounds
  refine ⟨N.classInteriorBox xref m M, N.isCompact_classInteriorBox xref m M,
    N.classInteriorBox_subset_positiveCompatibilityClass xref hm, ?_⟩
  intro x₀ hx₀
  obtain ⟨τ, hτΥ⟩ := hentry x₀ hx₀
  refine ⟨Set.Ici τ, Ici_mem_atTop τ, ?_⟩
  apply closure_minimal
  · rintro y ⟨u, hu, z, hz, rfl⟩
    have hz0 : z = x₀ := by simpa using hz
    subst z
    have htail : ϕ (u - τ) (ϕ τ x₀) = ϕ u x₀ := by
      rw [← ϕ.map_add, tsub_add_cancel_of_le hu]
    have hb := hbounds (ϕ τ x₀) hτΥ (u - τ)
    refine ⟨?_, ?_⟩
    · exact hx₀.1.trans (hflow.stoichCompatible x₀ u)
    · intro s
      simpa [htail] using hb s
  · exact (N.isCompact_classInteriorBox xref m M).isClosed

/-- Flow-level wrapper for the generic permanence assembly theorem. -/
theorem permanentForFlow_of_entry_and_uniform_bounds
    {N : Network S} {κ : N.RateConstants}
    {ϕ : Flow ℝ≥0 (Concentration S)} {γ : Concentration S → ℝ → Concentration S}
    (hflow : N.IsMassActionFlow κ ϕ γ)
    (h : ∀ xref : Concentration S, xref.Positive →
      ∃ Υ : Set (Concentration S),
        N.EveryPositiveClassOrbitEnters ϕ xref Υ ∧ UniformForwardCoordinateBounds ϕ Υ) :
    N.PermanentForFlow κ ϕ γ := by
  intro _hflow xref hxref
  obtain ⟨Υ, hentry, hbounds⟩ := h xref hxref
  exact permanentOnPositiveClass_of_entry_and_uniform_bounds hflow hentry hbounds

end Network
end CRNT
