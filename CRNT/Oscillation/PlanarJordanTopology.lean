import CRNT.Oscillation.PlanarJordanCrossingOrder

/-!
# Jordan topology interfaces used by the planar oscillation layer

This file collects the universal planar-topology targets used by Poincare--Bendixson and
Bendixson--Dulac. It is independent of CRNs and ODEs. The Jordan-separation and straight-edge
side results are represented by explicit propositions in the imported interface modules; this
file does not treat the unavailable Schoenflies and local-component arguments as completed proofs.
-/

namespace CRNT
namespace Planar

open Set Topology Filter

/-- Standard open unit disk in the repository's planar phase space. -/
def unitDisk : Set Phase2 := {x | ‖x‖ < 1}

/-- Standard exterior of the closed unit disk. -/
def unitExterior : Set Phase2 := {x | 1 < ‖x‖}

/-- Standard unit circle. -/
def unitCircle : Set Phase2 := {x | ‖x‖ = 1}

/-- The universal planar-topology facts required by the oscillation layer. The separation theorem
and the stronger straight-edge local-side package remain supplied inputs. -/
structure JordanTopologyKernelBundle : Prop where
  separation : SimplePlanarLoop.JordanSeparationTarget
  straightEdgeSide : StraightEdgeJordanSideTarget

namespace SimplePlanarLoop

/-- Forward an explicit Jordan-separation certificate through the topology interface. -/
theorem jordanSeparation_of_target
    (hJordan : JordanSeparationTarget) : JordanSeparationTarget := hJordan

end SimplePlanarLoop

/-- Forward an explicit straight-edge side certificate through the topology interface. -/
theorem straightEdgeJordanSide_of_target
    (hside : StraightEdgeJordanSideTarget) : StraightEdgeJordanSideTarget := hside

end Planar
end CRNT
