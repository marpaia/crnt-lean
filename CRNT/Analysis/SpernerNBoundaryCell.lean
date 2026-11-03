import CRNT.Analysis.SpernerNBoundary
import CRNT.Analysis.SpernerNDoor

/-!
# The restricted coloring on the boundary face

The dimension induction for n-dimensional Sperner restricts an `(n+1)`-dimensional Sperner coloring to
the distinguished boundary face `x_last = 0` (carried by `boundaryEquiv` to the `n`-dimensional
lattice). On that face the top color `Fin.last (n+1)` cannot occur (it would force the last
barycentric coordinate positive, contradicting membership in the face), so the colors land in
`Fin (n+1)` and `restrictColoring` is a genuine `n`-dimensional Sperner coloring.

Depends on: `CRNT.Analysis.SpernerNBoundary`,
`CRNT.Analysis.SpernerNDoor`.
-/

namespace CRNT.Analysis.SpernerN

variable {n N : ℕ}

/-- The lift of a point of the `n`-dimensional lattice to the boundary face of the `(n+1)`-simplex is
never colored with the top color `Fin.last (n+1)`. -/
private theorem lift_color_ne_last (col : SpernerColoring (n + 1) N) (q : Pt n N) :
    col.color ((boundaryEquiv n N).symm q).1 ≠ Fin.last (n + 1) := by
  intro hlast
  have hpos := col.proper _ _ hlast
  rw [boundaryEquiv_symm_apply_last] at hpos
  exact absurd hpos (lt_irrefl 0)

/-- **The restricted coloring.** An `(n+1)`-dimensional Sperner coloring, restricted along the
boundary face `x_last = 0`, is an `n`-dimensional Sperner coloring: color a point `q : Pt n N` by the
(non-top) color of its boundary lift, with the top index dropped. -/
def restrictColoring (col : SpernerColoring (n + 1) N) : SpernerColoring n N where
  color q := (col.color ((boundaryEquiv n N).symm q).1).castPred (lift_color_ne_last col q)
  proper q i hi := by
    have hlift : col.color ((boundaryEquiv n N).symm q).1 = i.castSucc := by
      conv_lhs => rw [← Fin.castSucc_castPred _ (lift_color_ne_last col q)]
      rw [hi]
    have hpos := col.proper _ _ hlift
    rwa [boundaryEquiv_symm_apply_castSucc] at hpos

/-- The restricted coloring, re-cast up: `castSucc` of the restricted color is the original color of
the boundary lift. -/
@[simp] theorem restrictColoring_color (col : SpernerColoring (n + 1) N) (q : Pt n N) :
    ((restrictColoring col).color q).castSucc = col.color ((boundaryEquiv n N).symm q).1 := by
  simp only [restrictColoring, Fin.castSucc_castPred]

/-- **Color bridge on the boundary face.** For a point `p` on the boundary face `x_last = 0`, the
restricted color of its projection `boundaryEquiv ⟨p, _⟩`, recast up by `castSucc`, is the original
color `col.color p`. This ties the original `(n+1)`-coloring to the restricted `n`-coloring on the
face, the link the door ↔ rainbow correspondence runs through. -/
theorem restrictColoring_color_of_boundary (col : SpernerColoring (n + 1) N) (p : Pt (n + 1) N)
    (hp : p.1 (Fin.last (n + 1)) = 0) :
    ((restrictColoring col).color (boundaryEquiv n N ⟨p, hp⟩)).castSucc = col.color p := by
  rw [restrictColoring_color]
  congr 1
  apply Subtype.ext
  exact congrArg (fun q : BoundaryFace n N => q.1.1)
    (Equiv.symm_apply_apply (boundaryEquiv n N) ⟨p, hp⟩)

end CRNT.Analysis.SpernerN
