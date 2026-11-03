import CRNT.Oscillation.DHopf

/-!
# Child-selection reactivity embeddings

This file formalizes the algebraic construction used in the oscillatory-core realization argument.
For an indexed child selection `C`, the paired reaction/species derivatives are fixed at `1`; every
other allowed reactant derivative is assigned a common parameter `eps`; forbidden derivatives stay
zero.  Thus for `eps > 0` the matrix is an admissible reactivity matrix, while at `eps = 0` the
selected symbolic-Jacobian block is exactly the child-selection stoichiometric matrix.

The important separation is intentional:

* this file proves the exact finite CRN/symbolic-Jacobian embedding;
* openness/persistence of the D-Hopf property for sufficiently small positive `eps` is a finite
  matrix perturbation theorem;
* parameter-rich kinetics then realizes that admissible reactivity matrix dynamically.
-/

namespace CRNT

open scoped BigOperators

namespace Network

variable {S : Type} [DecidableEq S] [Fintype S]
variable {N : Network S}

namespace IndexedChildSelection

variable {I : Type} [DecidableEq I] [Fintype I]

/-- A reaction/species incidence is the distinguished pair chosen by the child selection. -/
def IsPaired (C : N.IndexedChildSelection I) (r : N.R) (s : S) : Prop :=
  ∃ i : I, C.reaction i = r ∧ C.species i = s

instance instDecidableIsPaired (C : N.IndexedChildSelection I) (r : N.R) (s : S) :
    Decidable (C.IsPaired r s) := by
  unfold IsPaired
  infer_instance

/-- The distinguished sparse reactivity matrix.  It is `1` on paired entries and `0` elsewhere.
It need not itself be admissible because unpaired reactant incidences are zero. -/
noncomputable def coreReactivity (C : N.IndexedChildSelection I) : N.ReactivityMatrix := by
  classical
  exact fun r s => if C.IsPaired r s then 1 else 0

/-- Fill every unpaired but chemically allowed reactant incidence by `eps`. -/
noncomputable def epsilonReactivity (C : N.IndexedChildSelection I) (ε : ℝ) : N.ReactivityMatrix := by
  classical
  exact fun r s =>
    if (N.reaction r).source s = 0 then 0
    else if C.IsPaired r s then 1 else ε

/-- At `eps = 0`, the filled matrix is exactly the sparse core reactivity. -/
theorem epsilonReactivity_zero (C : N.IndexedChildSelection I) :
    C.epsilonReactivity 0 = C.coreReactivity := by
  funext r s
  unfold epsilonReactivity coreReactivity
  by_cases hsrc : (N.reaction r).source s = 0
  · rw [if_pos hsrc]
    have hnpair : ¬ C.IsPaired r s := by
      intro hp
      obtain ⟨i, hir, his⟩ := hp
      subst r
      subst s
      exact (Nat.ne_of_gt (C.reactant i)) hsrc
    rw [if_neg hnpair]
  · rw [if_neg hsrc]

/-- Every paired incidence is necessarily a genuine reactant incidence. -/
theorem source_pos_of_isPaired (C : N.IndexedChildSelection I)
    {r : N.R} {s : S} (h : C.IsPaired r s) : 0 < (N.reaction r).source s := by
  obtain ⟨i, hir, his⟩ := h
  subst r
  subst s
  exact C.reactant i

/-- The selected species/reaction pair at index `i` is recognized as paired. -/
theorem isPaired_self (C : N.IndexedChildSelection I) (i : I) :
    C.IsPaired (C.reaction i) (C.species i) :=
  ⟨i, rfl, rfl⟩

/-- If a selected reaction is paired with a selected species, the indices coincide. -/
theorem isPaired_selected_iff (C : N.IndexedChildSelection I) (i j : I) :
    C.IsPaired (C.reaction i) (C.species j) ↔ i = j := by
  constructor
  · rintro ⟨k, hkr, hks⟩
    have hki : k = i := C.reaction_injective hkr
    have hkj : k = j := C.species_injective hks
    exact hki.symm.trans hkj
  · intro hij
    subst j
    exact C.isPaired_self i

/-- For every strictly positive `eps`, the filled matrix has exactly the sign/support pattern of an
admissible reactivity matrix. -/
theorem epsilonReactivity_isReactivityMatrix
    (C : N.IndexedChildSelection I) {ε : ℝ} (hε : 0 < ε) :
    N.IsReactivityMatrix (C.epsilonReactivity ε) := by
  constructor
  · intro r s hrs
    unfold epsilonReactivity
    have hsrc : (N.reaction r).source s ≠ 0 := Nat.ne_of_gt hrs
    rw [if_neg hsrc]
    by_cases hp : C.IsPaired r s
    · simp [hp]
    · simpa [hp] using hε
  · intro r s hrs
    simp [epsilonReactivity, hrs]

/-- Selected square block of any symbolic Jacobian, written in the child-selection indexing. -/
def selectedSymbolicBlock (C : N.IndexedChildSelection I)
    (R : N.ReactivityMatrix) : Matrix I I ℝ :=
  fun i j => N.symbolicJacobian R (C.species i) (C.species j)

/-- The sparse `eps=0` symbolic block is exactly the child-selection matrix.  This is the key finite
algebraic identity in the oscillatory-core embedding. -/
theorem selectedSymbolicBlock_coreReactivity
    (C : N.IndexedChildSelection I) :
    C.selectedSymbolicBlock C.coreReactivity = C.matrix := by
  classical
  ext i j
  unfold selectedSymbolicBlock Network.symbolicJacobian coreReactivity matrix
  rw [Finset.sum_eq_single (C.reaction j)]
  · simp [C.isPaired_selected_iff j j]
  · intro r _ hr
    have hnpair : ¬ C.IsPaired r (C.species j) := by
      intro hp
      obtain ⟨k, hkr, hks⟩ := hp
      have hkj : k = j := C.species_injective hks
      subst k
      exact hr hkr.symm
    simp [hnpair]
  · intro hnotmem
    exact (hnotmem (Finset.mem_univ _)).elim

/-- Equivalent `eps=0` formulation using the filled family. -/
theorem selectedSymbolicBlock_epsilon_zero
    (C : N.IndexedChildSelection I) :
    C.selectedSymbolicBlock (C.epsilonReactivity 0) = C.matrix := by
  rw [C.epsilonReactivity_zero, C.selectedSymbolicBlock_coreReactivity]

/-- Entrywise, the epsilon family is affine in `eps` away from distinguished entries.  This record
is useful for perturbation arguments without committing to a matrix norm. -/
theorem epsilonReactivity_apply (C : N.IndexedChildSelection I)
    (ε : ℝ) (r : N.R) (s : S) :
    C.epsilonReactivity ε r s =
      if (N.reaction r).source s = 0 then 0
      else if C.IsPaired r s then 1 else ε :=
  rfl

/-- Every selected symbolic-block entry depends continuously on the epsilon fill parameter. -/
theorem continuous_selectedSymbolicBlock_apply
    (C : N.IndexedChildSelection I) (i j : I) :
    Continuous (fun ε : ℝ => C.selectedSymbolicBlock (C.epsilonReactivity ε) i j) := by
  classical
  unfold selectedSymbolicBlock Network.symbolicJacobian
  apply continuous_finsetSum
  intro r hr
  by_cases hsrc : (N.reaction r).source (C.species j) = 0
  · simp only [epsilonReactivity, hsrc, if_pos]
    fun_prop
  · by_cases hp : C.IsPaired r (C.species j)
    · simp only [epsilonReactivity, hsrc, hp, if_false, if_true]
      fun_prop
    · simp only [epsilonReactivity, hsrc, hp, if_false]
      fun_prop

/-- Every selected block entry converges to the child-selection matrix entry as `eps -> 0`. -/
theorem tendsto_selectedSymbolicBlock_zero
    (C : N.IndexedChildSelection I) (i j : I) :
    Filter.Tendsto
      (fun ε : ℝ => C.selectedSymbolicBlock (C.epsilonReactivity ε) i j)
      (nhds 0) (nhds (C.matrix i j)) := by
  have hcont : Continuous
      (fun ε : ℝ => C.selectedSymbolicBlock (C.epsilonReactivity ε) i j) :=
    C.continuous_selectedSymbolicBlock_apply i j
  have hzero : C.selectedSymbolicBlock (C.epsilonReactivity 0) i j = C.matrix i j := by
    have hm := C.selectedSymbolicBlock_epsilon_zero
    exact congrArg (fun M : Matrix I I ℝ => M i j) hm
  rw [← hzero]
  exact hcont.continuousAt

/-- Matrix-valued convergence of the selected symbolic block to the child-selection matrix. -/
theorem tendsto_selectedSymbolicBlock_zero_matrix
    (C : N.IndexedChildSelection I) :
    Filter.Tendsto
      (fun ε : ℝ => C.selectedSymbolicBlock (C.epsilonReactivity ε))
      (nhds 0) (nhds C.matrix) := by
  have hcont : Continuous
      (fun ε : ℝ => C.selectedSymbolicBlock (C.epsilonReactivity ε)) := by
    apply continuous_matrix
    intro i j
    exact C.continuous_selectedSymbolicBlock_apply i j
  rw [← C.selectedSymbolicBlock_epsilon_zero]
  exact hcont.continuousAt

end IndexedChildSelection

/-- Finite-matrix openness statement needed by the 2026 construction.  It is intentionally stated
on the exact `epsilonReactivity` family above: if the `eps=0` selected block is D-Hopf, then the
property persists for all sufficiently small positive `eps`. -/
def ChildSelectionDHopfPerturbationTarget : Prop :=
  ∀ {T : Type} [DecidableEq T] [Fintype T]
    (N : Network T) {I : Type} [DecidableEq I] [Fintype I]
    (C : N.IndexedChildSelection I),
    Nonempty (Matrix.StrongDHopfWitness C.matrix) →
      ∃ ε₀ : ℝ, 0 < ε₀ ∧
        ∀ ε : ℝ, 0 < ε → ε < ε₀ →
          Nonempty (Matrix.StrongDHopfWitness
            (C.selectedSymbolicBlock (C.epsilonReactivity ε)))

/-- Once the finite D-Hopf perturbation theorem is available, every indexed D-Hopf child selection
produces an admissible positive reactivity matrix with a D-Hopf selected symbolic block. -/
theorem exists_admissible_reactivity_with_strongDHopfBlock
    {T : Type} [DecidableEq T] [Fintype T]
    (hopen : ChildSelectionDHopfPerturbationTarget)
    (N : Network T) {I : Type} [DecidableEq I] [Fintype I]
    (C : N.IndexedChildSelection I)
    (hcore : Nonempty (Matrix.StrongDHopfWitness C.matrix)) :
    ∃ R : N.ReactivityMatrix,
      N.IsReactivityMatrix R ∧
      Nonempty (Matrix.StrongDHopfWitness (C.selectedSymbolicBlock R)) := by
  obtain ⟨ε₀, hε₀, hopenε⟩ := hopen N C hcore
  let ε := ε₀ / 2
  have hε : 0 < ε := half_pos hε₀
  have hεlt : ε < ε₀ := half_lt_self hε₀
  refine ⟨C.epsilonReactivity ε, C.epsilonReactivity_isReactivityMatrix hε, ?_⟩
  exact hopenε ε hε hεlt

end Network
end CRNT
