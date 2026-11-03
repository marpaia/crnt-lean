import Mathlib.Basic.Real.Basic

/-!
# Counterexamples to two tempting blueprint shortcuts

These finite Lean examples do not refute Craciun's theorem. They refute two insufficient premises
that cannot replace its missing geometric construction: agreement at one distinguished start does
not imply agreement of traces on a shared boundary, and a lexicographic enumeration alone does not
make an unspecified dependency relation acyclic.
-/

namespace CRNT.Examples.GACBlueprintPremiseCounterexamples

/-- Two candidate boundary traces with the same distinguished initial value. -/
def traceA (_ : Fin 2) : ℝ := 0

def traceB (i : Fin 2) : ℝ := i.val

/-- Sharing the initial vertex does not make two face traces compatible elsewhere. -/
theorem same_initial_value_does_not_force_trace_agreement :
    traceA 0 = traceB 0 ∧ traceA 1 ≠ traceB 1 := by
  constructor <;> norm_num [traceA, traceB]

/-- If every dependency points to a strictly smaller natural rank, recursive face processing
has no infinite descent. This proves the order-theoretic part of lexicographic filling; a geometric
construction must still prove that its actual dependencies decrease this rank. -/
theorem wellFounded_of_decreasing_rank {α : Type*} (rank : α → ℕ)
    (depends : α → α → Prop)
    (hdecreasing : ∀ {required face}, depends required face →
      rank required < rank face) : WellFounded depends := by
  have hacc : ∀ n : ℕ, ∀ face, rank face = n → Acc depends face := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro face hface
        apply Acc.intro
        intro required hdep
        exact ih (rank required) (by rw [← hface]; exact hdecreasing hdep)
          required rfl
  exact ⟨fun face => hacc (rank face) face rfl⟩

/-- A local extension rule can be iterated over all faces once its real dependency relation is
proved to decrease the chosen rank. This is only a recursion principle, not the geometric extension
rule required by the zero-separating construction. -/
theorem fill_by_decreasing_rank {α : Type*} (rank : α → ℕ)
    (depends : α → α → Prop)
    (hdecreasing : ∀ {required face}, depends required face →
      rank required < rank face)
    (P : α → Prop)
    (extend : ∀ face, (∀ required, depends required face → P required) → P face) :
    ∀ face, P face := by
  have hfill : ∀ n : ℕ, ∀ face, rank face = n → P face := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro face hface
        apply extend face
        intro required hdep
        exact ih (rank required) (by rw [← hface]; exact hdecreasing hdep)
          required rfl
  exact fun face => hfill (rank face) face rfl

/-- Four individually nonempty affine face constraints in three dimensions. -/
theorem each_affine_face_constraint_nonempty :
    (∃ p : Fin 3 → ℝ, p 0 = 0) ∧
      (∃ p : Fin 3 → ℝ, p 1 = 0) ∧
      (∃ p : Fin 3 → ℝ, p 2 = 0) ∧
      (∃ p : Fin 3 → ℝ, p 0 + p 1 + p 2 = 1) := by
  exact ⟨⟨fun _ => 0, by simp⟩,
    ⟨fun _ => 0, by simp⟩,
    ⟨fun _ => 0, by simp⟩,
    ⟨fun i => if i = 0 then (1 : ℝ) else 0, by norm_num⟩⟩

/-- Local face solvability alone does not guarantee compatible filling at a shared vertex. -/
theorem incompatible_face_offsets_have_no_shared_vertex :
    ¬ ∃ p : Fin 3 → ℝ,
      p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0 ∧ p 0 + p 1 + p 2 = 1 := by
  rintro ⟨p, h0, h1, h2, h3⟩
  rw [h0, h1, h2] at h3
  norm_num at h3

/-- A possible dependency relation on two lexicographically ordered faces. -/
inductive FaceIndex where
  | first
  | second
  deriving DecidableEq

/-- Each face in this toy model requires information from the other face. -/
def cyclicDependency (face required : FaceIndex) : Prop :=
  (face = .first ∧ required = .second) ∨
    (face = .second ∧ required = .first)

def lexRank : FaceIndex → ℕ
  | .first => 0
  | .second => 1

theorem toy_dependencies_form_cycle :
    cyclicDependency .first .second ∧ cyclicDependency .second .first := by
  simp [cyclicDependency]

/-- Any claimed lexicographic construction must prove its geometric dependencies point backward;
that fact cannot be inferred from the enumeration by itself. -/
theorem toy_dependencies_not_lexicographically_decreasing :
    ¬ ∀ face required, cyclicDependency face required → lexRank required < lexRank face := by
  intro h
  have hlt := h .first .second (by simp [cyclicDependency])
  simp [lexRank] at hlt

end CRNT.Examples.GACBlueprintPremiseCounterexamples
