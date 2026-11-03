import CRNT.Oscillation.PlanarLocalReturnLoops
import CRNT.Oscillation.PlanarReturnMonotonicity

/-!
# Local Jordan side and chronological return ordering

A simple Jordan loop whose boundary contains a nondegenerate straight segment has a consistent local
inside/outside side along the relative interior of that segment.  This is the only local-topology
fact used by the transversal-ordering proof.  Once it is stated explicitly, the return-ordering
argument is elementary: all local section crossings have positive signed speed, so two consecutive
crossings cannot traverse the same boundary edge in the same direction.
-/

namespace CRNT

-- `⟪x, y⟫_ℝ` lives in the `InnerProductSpace` scope; without this open the bracket is
-- not a valid token.
open scoped InnerProductSpace
open Filter Topology

namespace Planar

open Set

/-- Local one-sidedness of the bounded component along a straight edge of a Jordan loop.

`normalCoord` vanishes on the edge.  The sign `sigma` is either positive or negative and chooses which side is interior.  Around
every point in the relative interior of the edge, the two complement components coincide locally
with the positive/negative sign regions. -/
structure StraightEdgeLocalSide
    (L : SimplePlanarLoop) (J : L.Separation)
    (edgePoint : ℝ → Phase2) (a b : ℝ)
    (normalCoord : Phase2 → ℝ) where
  sign : ℝ
  sign_sq : sign ^ 2 = 1
  edge_in_trace : ∀ u ∈ Set.uIcc a b, edgePoint u ∈ L.trace
  coord_edge : ∀ u, normalCoord (edgePoint u) = 0
  local_side : ∀ u ∈ Set.uIoo a b,
    ∃ U ∈ 𝓝 (edgePoint u),
      (∀ x ∈ U, x ∈ J.interior ↔ 0 < sign * normalCoord x) ∧
      (∀ x ∈ U, x ∈ J.exterior ↔ sign * normalCoord x < 0)

/-- Universal local-side corollary of Jordan separation for a straight boundary edge. -/
def BasicStraightEdgeJordanSideTarget : Prop :=
  ∀ (L : SimplePlanarLoop) (J : L.Separation)
    (edgePoint : ℝ → Phase2) (a b : ℝ) (normalCoord : Phase2 → ℝ),
    a ≠ b → Function.Injective edgePoint →
    (∀ u ∈ Set.uIcc a b, edgePoint u ∈ L.trace) →
    (∀ u, normalCoord (edgePoint u) = 0) →
    Nonempty (StraightEdgeLocalSide L J edgePoint a b normalCoord)

/-- Two consecutive local return arcs sharing the middle return. -/
structure LocalReturnTriple {field : Phase2 → Phase2}
    (D : FlowTrappingData field) (q : Phase2) (rho : ℝ) : Type where
  first : LocalCanonicalReturn D q rho
  middle : LocalCanonicalReturn D q rho
  last : LocalCanonicalReturn D q rho
  first_middle : ConsecutiveLocalReturns D q rho
  middle_last : ConsecutiveLocalReturns D q rho
  fm_first : first_middle.first = first
  fm_second : first_middle.second = middle
  ml_first : middle_last.first = middle
  ml_second : middle_last.second = last

/-- Oriented crossing consequence for one consecutive-return triple.  This is kept as an explicit
target because the local-side existence statement alone does not supply the required component
comparison along the two orbit arcs. -/
def LocalReturnTripleIncrementTarget : Prop :=
  ∀ (hJordan : SimplePlanarLoop.JordanSeparationTarget)
    (hside : BasicStraightEdgeJordanSideTarget)
    (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D) (q : Phase2) (rho : ℝ),
    q ∈ M.carrier → 0 < rho → ContDiff ℝ 1 field → field q ≠ 0 →
    (∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ) →
    ¬ HasPeriodicTrajectoryThrough field q →
    ∀ T : LocalReturnTriple D q rho,
      0 < (T.middle.scalar - T.first.scalar) *
        (T.last.scalar - T.middle.scalar)

/-- Finite chronological induction from strict consecutive increments to the first-return order.
This is the separate combinatorial residue after the oriented triple step is supplied. -/
def ConsecutiveReturnOrderFromStepsTarget : Prop :=
  ∀ (field : Phase2 → Phase2) (D : FlowTrappingData field)
    (M : MinimalOmegaData D) (q : Phase2) (rho : ℝ),
    q ∈ M.carrier → ContDiff ℝ 1 field →
    (∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ) →
    ¬ HasPeriodicTrajectoryThrough field q →
    (∀ T : LocalReturnTriple D q rho,
      0 < (T.middle.scalar - T.first.scalar) *
        (T.last.scalar - T.middle.scalar)) →
    ∀ H₁ : FirstLocalReturn D q rho,
      ∀ H₂ : LocalCanonicalReturn D q rho,
        H₁.time < H₂.time → ReturnFartherFromBase H₁.scalar H₂.scalar

/-- Bundled support required to turn Jordan separation into the full return ordering.  In addition
to the straight-edge local-side fact, the oriented triple step and the finite chronological induction
remain explicit mathematical targets. -/
def StraightEdgeJordanSideTarget : Prop :=
  BasicStraightEdgeJordanSideTarget ∧
    LocalReturnTripleIncrementTarget ∧ ConsecutiveReturnOrderFromStepsTarget

namespace LocalReturnTriple

variable {field : Phase2 → Phase2} {D : FlowTrappingData field}
  {q : Phase2} {rho : ℝ}

/-- Consecutive increments preserve their sign.  The proof is the Jordan local-side argument. -/
theorem increments_same_sign
    (T : LocalReturnTriple D q rho)
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier) (hrho : 0 < rho)
    (hsmooth : ContDiff ℝ 1 field)
    (hne : field q ≠ 0)
    (horient : ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ)
    (haper : ¬ HasPeriodicTrajectoryThrough field q)
    (hJordan : SimplePlanarLoop.JordanSeparationTarget)
    (hside : StraightEdgeJordanSideTarget) :
    0 < (T.middle.scalar - T.first.scalar) *
      (T.last.scalar - T.middle.scalar) :=
  hside.2.1 hJordan hside.1 field D M q rho hq hrho hsmooth hne
    horient haper T

end LocalReturnTriple

/-- Finite chronological induction: if every consecutive triple preserves increment sign, then the
first return orders every later local return away from scalar zero. -/
theorem firstReturn_orders_later_of_step
    (hprop : ConsecutiveReturnOrderFromStepsTarget)
    {field : Phase2 → Phase2} {D : FlowTrappingData field}
    {M : MinimalOmegaData D} {q : Phase2} {rho : ℝ}
    (M : MinimalOmegaData D) (hq : q ∈ M.carrier)
    (hsmooth : ContDiff ℝ 1 field)
    (horient : ∀ u ∈ Set.Icc (-rho) rho,
      0 < ⟪field (canonicalSectionPoint field q u), field q⟫_ℝ)
    (haper : ¬ HasPeriodicTrajectoryThrough field q)
    (hstep : ∀ T : LocalReturnTriple D q rho,
      0 < (T.middle.scalar - T.first.scalar) *
        (T.last.scalar - T.middle.scalar))
    (H₁ : FirstLocalReturn D q rho)
    (H₂ : LocalCanonicalReturn D q rho)
    (htime : H₁.time < H₂.time) :
    ReturnFartherFromBase H₁.scalar H₂.scalar :=
  hprop field D M q rho hq hsmooth horient haper hstep H₁ H₂ htime

/-- Jordan separation plus the straight-edge local-side theorem prove the full return-ordering
kernel. -/
theorem jordanReturnOrdering_of_localSide
    (hJordan : SimplePlanarLoop.JordanSeparationTarget)
    (hside : StraightEdgeJordanSideTarget)
    (hflow : CanonicalFlowRegularityTarget) :
    JordanLocalReturnOrderingTarget := by
  intro field D M q rho hq hrho hsmooth horient haper H₁ H₂ htime
  have hstep : ∀ T : LocalReturnTriple D q rho,
      0 < (T.middle.scalar - T.first.scalar) *
        (T.last.scalar - T.middle.scalar) := by
    intro T
    exact T.increments_same_sign M hq hrho hsmooth
      (M.equilibriumFree q hq) horient haper hJordan hside
  exact firstReturn_orders_later_of_step hside.2.2
    (field := field) (D := D) (M := M) (q := q) (rho := rho)
    M hq hsmooth horient haper hstep H₁ H₂ htime

end Planar
end CRNT
