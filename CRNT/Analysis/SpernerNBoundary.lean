import CRNT.Analysis.SpernerLatticeN

/-!
# The boundary face of the `(n+1)`-simplex and its reduction to dimension `n`

The dimension induction for n-dimensional Sperner reduces along the distinguished boundary face
`x (Fin.last (n+1)) = 0` of the `(n+1)`-subdivision — the face opposite the top colour. Dropping that
last barycentric coordinate is a bijection `BoundaryFace n N ≃ Pt n N`, carrying the boundary
subproblem to a genuine `n`-dimensional lattice. This is the geometric core of the recursion: a
`(n+1)`-dimensional door facet lands on this face, where it becomes an `n`-dimensional Sperner datum
discharged by the inductive hypothesis.

Depends on: `CRNT.Analysis.SpernerLatticeN`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators

variable {n N : ℕ}

/-- The distinguished **boundary face** of the `(n+1)`-simplex: lattice points whose last barycentric
coordinate vanishes. -/
def BoundaryFace (n N : ℕ) : Type := {x : Pt (n + 1) N // x.1 (Fin.last (n + 1)) = 0}

/-- **Dropping the last coordinate** is a bijection from the boundary face to the `n`-dimensional
lattice; its inverse extends a point by a zero in the last coordinate. -/
def boundaryEquiv (n N : ℕ) : BoundaryFace n N ≃ Pt n N where
  toFun p := ⟨fun i => p.1.1 i.castSucc, by
    have h := p.1.2
    rw [Fin.sum_univ_castSucc, p.2, add_zero] at h
    exact h⟩
  invFun q := ⟨⟨Fin.lastCases 0 q.1, by
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.lastCases_castSucc, Fin.lastCases_last, add_zero]
      exact q.2⟩, by simp⟩
  left_inv p := by
    apply Subtype.ext; apply Pt.ext; funext j
    induction j using Fin.lastCases with
    | last => simpa using p.2.symm
    | cast i => simp
  right_inv q := by
    apply Pt.ext; funext i; simp

@[simp] theorem boundaryEquiv_apply (p : BoundaryFace n N) (i : Fin (n + 1)) :
    (boundaryEquiv n N p).1 i = p.1.1 i.castSucc := rfl

@[simp] theorem boundaryEquiv_symm_apply_castSucc (q : Pt n N) (i : Fin (n + 1)) :
    ((boundaryEquiv n N).symm q).1.1 i.castSucc = q.1 i := by
  change Fin.lastCases 0 q.1 i.castSucc = q.1 i
  simp

@[simp] theorem boundaryEquiv_symm_apply_last (q : Pt n N) :
    ((boundaryEquiv n N).symm q).1.1 (Fin.last (n + 1)) = 0 := by
  change Fin.lastCases 0 q.1 (Fin.last (n + 1)) = 0
  simp

end CRNT.Analysis.SpernerN
