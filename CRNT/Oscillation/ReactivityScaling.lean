import CRNT.Oscillation.ChildSelectionReactivity

/-!
# Positive column scaling of reactivity matrices

A D-Hopf witness acts by positive **right diagonal scaling** of a Jacobian.  In the symbolic CRN
factorization `G = S R`, that operation has a direct kinetic interpretation: scale column `s` of the
reactivity matrix by the positive scalar `d_s`.

This file proves the exact identity

`symbolicJacobian (scaleReactivity R d) = symbolicJacobian R * diagonal d`

and its selected-child-block analogue.  Thus the two diagonal endpoints of a D-Hopf certificate
are genuine admissible reactivity matrices, not abstract matrices detached from the CRN.
-/

namespace CRNT

open scoped BigOperators

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

/-- Scale each species column of a reaction-by-species reactivity matrix. -/
def scaleReactivity (N : Network S) (R : N.ReactivityMatrix) (d : S → ℝ) :
    N.ReactivityMatrix :=
  fun r s => R r s * d s

/-- Positive column scaling preserves the admissible reactivity sign/support pattern. -/
theorem IsReactivityMatrix.scaleReactivity
    {R : N.ReactivityMatrix} (hR : N.IsReactivityMatrix R)
    {d : S → ℝ} (hd : ∀ s, 0 < d s) :
    N.IsReactivityMatrix (N.scaleReactivity R d) := by
  constructor
  · intro r s hrs
    exact mul_pos (hR.positive_on_reactants r s hrs) (hd s)
  · intro r s hrs
    change R r s * d s = 0
    rw [hR.zero_off_reactants r s hrs, zero_mul]

/-- The symbolic Jacobian intertwines reactivity column scaling and right diagonal matrix scaling. -/
theorem symbolicJacobian_scaleReactivity
    (N : Network S) (R : N.ReactivityMatrix) (d : S → ℝ) :
    N.symbolicJacobian (N.scaleReactivity R d) =
      N.symbolicJacobian R * Matrix.diagonal d := by
  classical
  ext i j
  simp [symbolicJacobian, scaleReactivity, Matrix.mul_apply, Matrix.diagonal_apply,
    Finset.sum_mul, mul_assoc]

@[simp] theorem scaleReactivity_one (N : Network S) (R : N.ReactivityMatrix) :
    N.scaleReactivity R (fun _ => 1) = R := by
  funext r s
  simp [scaleReactivity]

/-- Composition of two column scalings multiplies their diagonal factors pointwise. -/
theorem scaleReactivity_scaleReactivity
    (N : Network S) (R : N.ReactivityMatrix) (d e : S → ℝ) :
    N.scaleReactivity (N.scaleReactivity R d) e =
      N.scaleReactivity R (fun s => d s * e s) := by
  funext r s
  simp [scaleReactivity, mul_assoc]

namespace IndexedChildSelection

variable {I : Type} [DecidableEq I] [Fintype I]

/-- Restrict an ambient species scaling to the selected species. -/
def restrictDiagonal (C : N.IndexedChildSelection I) (d : S → ℝ) : I → ℝ :=
  fun i => d (C.species i)

/-- Scaling the full reactivity matrix right-diagonally scales the selected symbolic block by the
restricted positive diagonal. -/
theorem selectedSymbolicBlock_scaleReactivity
    (C : N.IndexedChildSelection I) (R : N.ReactivityMatrix) (d : S → ℝ) :
    C.selectedSymbolicBlock (N.scaleReactivity R d) =
      C.selectedSymbolicBlock R * Matrix.diagonal (C.restrictDiagonal d) := by
  classical
  ext i j
  let M : Matrix I I ℝ := C.selectedSymbolicBlock R
  have hselected :
      (M * Matrix.diagonal (C.restrictDiagonal d)) i j =
        N.symbolicJacobian R (C.species i) (C.species j) * d (C.species j) := by
    rw [Matrix.mul_apply]
    rw [Fintype.sum_eq_single j (fun k hk => by
      simp [Matrix.diagonal_apply, hk])]
    dsimp [M, selectedSymbolicBlock, restrictDiagonal]
    simp [restrictDiagonal]
  change C.selectedSymbolicBlock (N.scaleReactivity R d) i j =
    (M * Matrix.diagonal (C.restrictDiagonal d)) i j
  rw [hselected]
  change N.symbolicJacobian (N.scaleReactivity R d) (C.species i) (C.species j) = _
  rw [N.symbolicJacobian_scaleReactivity]
  simp [Matrix.mul_apply, Matrix.diagonal_apply]

/-- Extend a selected diagonal by `1` outside the selected species. -/
noncomputable def extendDiagonal (C : N.IndexedChildSelection I) (d : I → ℝ) : S → ℝ :=
  fun s => if h : ∃ i : I, C.species i = s then d (Classical.choose h) else 1

/-- On selected species, the extension recovers the original selected diagonal. -/
theorem extendDiagonal_species (C : N.IndexedChildSelection I) (d : I → ℝ) (i : I) :
    C.extendDiagonal d (C.species i) = d i := by
  classical
  unfold extendDiagonal
  have h : ∃ j : I, C.species j = C.species i := ⟨i, rfl⟩
  rw [dif_pos h]
  have hc : Classical.choose h = i :=
    C.species_injective (Classical.choose_spec h)
  rw [hc]

/-- Positivity of a selected diagonal is preserved by extension by ones. -/
theorem extendDiagonal_positive
    (C : N.IndexedChildSelection I) {d : I → ℝ} (hd : ∀ i, 0 < d i) :
    ∀ s, 0 < C.extendDiagonal d s := by
  classical
  intro s
  unfold extendDiagonal
  split_ifs with h
  · exact hd (Classical.choose h)
  · exact zero_lt_one

/-- Restricting an extended selected diagonal is exactly the original selected diagonal. -/
@[simp] theorem restrictDiagonal_extendDiagonal
    (C : N.IndexedChildSelection I) (d : I → ℝ) :
    C.restrictDiagonal (C.extendDiagonal d) = d := by
  funext i
  exact C.extendDiagonal_species d i

/-- The two diagonal endpoints of a strong D-Hopf witness lift to admissible full-CRN reactivity
matrices whose selected blocks are exactly the certified scaled matrices. -/
structure LiftedDHopfReactivityEndpoints
    (C : N.IndexedChildSelection I) (R : N.ReactivityMatrix)
    (hR : N.IsReactivityMatrix R)
    (hcore : Matrix.StrongDHopfWitness (C.selectedSymbolicBlock R)) : Type where
  stableReactivity : N.ReactivityMatrix
  unstableReactivity : N.ReactivityMatrix
  stableAdmissible : N.IsReactivityMatrix stableReactivity
  unstableAdmissible : N.IsReactivityMatrix unstableReactivity
  stableBlock : C.selectedSymbolicBlock stableReactivity =
    C.selectedSymbolicBlock R * Matrix.diagonal hcore.stableDiagonal
  unstableBlock : C.selectedSymbolicBlock unstableReactivity =
    C.selectedSymbolicBlock R * Matrix.diagonal hcore.unstableDiagonal

/-- Construct the lifted D-Hopf endpoint reactivities by extending selected diagonal factors by one. -/
noncomputable def liftDHopfReactivityEndpoints
    (C : N.IndexedChildSelection I) (R : N.ReactivityMatrix)
    (hR : N.IsReactivityMatrix R)
    (hcore : Matrix.StrongDHopfWitness (C.selectedSymbolicBlock R)) :
    C.LiftedDHopfReactivityEndpoints R hR hcore := by
  let d₀ : S → ℝ := C.extendDiagonal hcore.stableDiagonal
  let d₁ : S → ℝ := C.extendDiagonal hcore.unstableDiagonal
  refine
    { stableReactivity := N.scaleReactivity R d₀
      unstableReactivity := N.scaleReactivity R d₁
      stableAdmissible := hR.scaleReactivity (C.extendDiagonal_positive hcore.stablePositive)
      unstableAdmissible := hR.scaleReactivity (C.extendDiagonal_positive hcore.unstablePositive)
      stableBlock := ?_
      unstableBlock := ?_ }
  · rw [C.selectedSymbolicBlock_scaleReactivity]
    simp [d₀]
  · rw [C.selectedSymbolicBlock_scaleReactivity]
    simp [d₁]

end IndexedChildSelection

end Network
end CRNT
