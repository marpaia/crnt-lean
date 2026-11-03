import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Order.Basic

/-!
# Indexed directed paths in a relation

`CRNT.relationGraphOn` forgets the orientation of the causal relation, and `SimpleGraph.Walk`
offers only vertex-indexed cuts (`takeUntil` / `dropUntil`), which are the wrong shape for
arguments that need to cut a walk at a *position*. This file gives a directed walk as an
explicitly indexed structure, where cutting a tail and splicing out a repeat are both plain
reindexings.

The purpose is the orientation-sensitive half of the true-SR endgame: a c-pair of a
species-reaction path agrees with a sign change of `σ` exactly at reaction vertices whose two
incident causal edges point *oppositely*, which for a path means the path is directed. So the
escape argument there needs a directed path, not merely a walk in the underlying graph.

`exists_minimal_relPath` is the payoff: among the directed paths from a distinguished set to a
fixed target, a shortest one is injective and meets the distinguished set only at its start.
-/

namespace CRNT

variable {V : Type*}

/-- A directed walk of length `k` for the relation `E`, staying inside `T`, given by its
sequence of vertices. -/
structure RelPath (E : V → V → Prop) (T : Finset V) (k : ℕ) where
  vertex : Fin (k + 1) → V
  mem : ∀ i, vertex i ∈ T
  step : ∀ i : Fin k, E (vertex (Fin.castSucc i)) (vertex i.succ)

namespace RelPath

variable {E : V → V → Prop} {T : Finset V} {k : ℕ}

/-- The tail of a directed walk from position `m`. -/
def tail (P : RelPath E T k) (m : ℕ) (hm : m ≤ k) : RelPath E T (k - m) where
  vertex := fun i => P.vertex ⟨m + i.1, by have := i.isLt; omega⟩
  mem := fun i => P.mem _
  step := by
    intro i
    have hi := i.isLt
    have h := P.step ⟨m + i.1, by omega⟩
    have h1 : (Fin.castSucc (⟨m + i.1, by omega⟩ : Fin k))
        = (⟨m + (Fin.castSucc i).1, by omega⟩ : Fin (k + 1)) := Fin.ext rfl
    have h2 : ((⟨m + i.1, by omega⟩ : Fin k).succ)
        = (⟨m + (i.succ).1, by omega⟩ : Fin (k + 1)) := Fin.ext rfl
    rw [h1, h2] at h
    exact h

/-- The initial segment of a directed walk, ending at position `m`. -/
def take (P : RelPath E T k) (m : ℕ) (hm : m ≤ k) : RelPath E T m where
  vertex := fun i => P.vertex ⟨i.1, by have := i.isLt; omega⟩
  mem := fun i => P.mem _
  step := by
    intro i
    have hi := i.isLt
    have h := P.step ⟨i.1, by omega⟩
    have h1 : (Fin.castSucc (⟨i.1, by omega⟩ : Fin k)) =
        (⟨(Fin.castSucc i).1, by omega⟩ : Fin (k + 1)) := Fin.ext rfl
    have h2 : ((⟨i.1, by omega⟩ : Fin k).succ) =
        (⟨i.succ.1, by omega⟩ : Fin (k + 1)) := Fin.ext rfl
    rw [h1, h2] at h
    exact h

@[simp] theorem take_vertex (P : RelPath E T k) (m : ℕ) (hm : m ≤ k)
    (i : Fin (m + 1)) : (P.take m hm).vertex i = P.vertex ⟨i.1, by have := i.isLt; omega⟩ := rfl

theorem take_vertex_zero (P : RelPath E T k) (m : ℕ) (hm : m ≤ k) :
    (P.take m hm).vertex ⟨0, by omega⟩ = P.vertex ⟨0, by omega⟩ := rfl

theorem take_vertex_last (P : RelPath E T k) (m : ℕ) (hm : m ≤ k) :
    (P.take m hm).vertex ⟨m, by omega⟩ = P.vertex ⟨m, by omega⟩ := rfl

/-- The initial segment of a directed walk, up to position `m`. -/
def init (P : RelPath E T k) (m : ℕ) (hm : m ≤ k) : RelPath E T m :=
  P.take m hm

@[simp] theorem init_vertex (P : RelPath E T k) (m : ℕ) (hm : m ≤ k)
    (i : Fin (m + 1)) :
    (P.init m hm).vertex i = P.vertex ⟨i.1, by have := i.isLt; omega⟩ := rfl

theorem init_injective (P : RelPath E T k) (m : ℕ) (hm : m ≤ k)
    (hinj : Function.Injective P.vertex) : Function.Injective (P.init m hm).vertex := by
  intro a b hab
  have hidx : (⟨a.1, by have := a.isLt; omega⟩ : Fin (k + 1)) =
      ⟨b.1, by have := b.isLt; omega⟩ := hinj (by simpa [init] using hab)
  have hv : a.1 = b.1 := congrArg (fun z : Fin (k + 1) => z.1) hidx
  exact Fin.ext hv

@[simp] theorem tail_vertex (P : RelPath E T k) (m : ℕ) (hm : m ≤ k) (i : Fin (k - m + 1)) :
    (P.tail m hm).vertex i = P.vertex ⟨m + i.1, by have := i.isLt; omega⟩ := rfl

/-- Splicing out the stretch between two positions carrying the same vertex. -/
def splice (P : RelPath E T k) (a b : ℕ) (hab : a < b) (hbk : b ≤ k)
    (heq : P.vertex ⟨a, by omega⟩ = P.vertex ⟨b, by omega⟩) :
    RelPath E T (k - (b - a)) where
  vertex := fun i =>
    if i.1 ≤ a then P.vertex ⟨i.1, by have := i.isLt; omega⟩
    else P.vertex ⟨i.1 + (b - a), by have := i.isLt; omega⟩
  mem := by
    intro i
    by_cases h : i.1 ≤ a
    · rw [if_pos h]; exact P.mem _
    · rw [if_neg h]; exact P.mem _
  step := by
    intro i
    have hi := i.isLt
    have hcs : (Fin.castSucc i).1 = i.1 := rfl
    have hsu : (i.succ).1 = i.1 + 1 := rfl
    by_cases h : i.1 < a
    · -- strictly below the cut: both endpoints are original
      have h1 : (if (Fin.castSucc i).1 ≤ a then P.vertex ⟨(Fin.castSucc i).1, by omega⟩
          else P.vertex ⟨(Fin.castSucc i).1 + (b - a), by omega⟩)
            = P.vertex ⟨i.1, by omega⟩ := by
        rw [if_pos (show (Fin.castSucc i).1 ≤ a by rw [hcs]; omega)]
        rfl
      have h2 : (if (i.succ).1 ≤ a then P.vertex ⟨(i.succ).1, by omega⟩
          else P.vertex ⟨(i.succ).1 + (b - a), by omega⟩)
            = P.vertex ⟨i.1 + 1, by omega⟩ := by
        rw [if_pos (show (i.succ).1 ≤ a by rw [hsu]; omega)]
        rfl
      show E (if (Fin.castSucc i).1 ≤ a then _ else _) (if (i.succ).1 ≤ a then _ else _)
      rw [h1, h2]
      have hst := P.step ⟨i.1, by omega⟩
      have e1 : (Fin.castSucc (⟨i.1, by omega⟩ : Fin k)) = (⟨i.1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      have e2 : ((⟨i.1, by omega⟩ : Fin k).succ) = (⟨i.1 + 1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      rw [e1, e2] at hst
      exact hst
    · -- at or above the cut: the step is the original one shifted by `b - a`
      have hia : a ≤ i.1 := by omega
      have h1 : (if (Fin.castSucc i).1 ≤ a then P.vertex ⟨(Fin.castSucc i).1, by omega⟩
          else P.vertex ⟨(Fin.castSucc i).1 + (b - a), by omega⟩)
            = P.vertex ⟨i.1 + (b - a), by omega⟩ := by
        by_cases hia' : i.1 = a
        · rw [if_pos (show (Fin.castSucc i).1 ≤ a by rw [hcs]; omega)]
          rw [show (⟨(Fin.castSucc i).1, by omega⟩ : Fin (k + 1)) = ⟨a, by omega⟩ from
            Fin.ext (by rw [hcs]; exact hia')]
          rw [heq]
          exact congrArg P.vertex (Fin.ext (by show b = i.1 + (b - a); omega))
        · rw [if_neg (show ¬ (Fin.castSucc i).1 ≤ a by rw [hcs]; omega)]
          rfl
      have h2 : (if (i.succ).1 ≤ a then P.vertex ⟨(i.succ).1, by omega⟩
          else P.vertex ⟨(i.succ).1 + (b - a), by omega⟩)
            = P.vertex ⟨i.1 + 1 + (b - a), by omega⟩ := by
        rw [if_neg (show ¬ (i.succ).1 ≤ a by rw [hsu]; omega)]
        rfl
      show E (if (Fin.castSucc i).1 ≤ a then _ else _) (if (i.succ).1 ≤ a then _ else _)
      rw [h1, h2]
      have hst := P.step ⟨i.1 + (b - a), by omega⟩
      have e1 : (Fin.castSucc (⟨i.1 + (b - a), by omega⟩ : Fin k))
          = (⟨i.1 + (b - a), by omega⟩ : Fin (k + 1)) := Fin.ext rfl
      have e2 : ((⟨i.1 + (b - a), by omega⟩ : Fin k).succ)
          = (⟨i.1 + 1 + (b - a), by omega⟩ : Fin (k + 1)) :=
        Fin.ext (by show i.1 + (b - a) + 1 = i.1 + 1 + (b - a); omega)
      rw [e1, e2] at hst
      exact hst

@[simp] theorem splice_vertex (P : RelPath E T k) (a b : ℕ) (hab : a < b) (hbk : b ≤ k)
    (heq : P.vertex ⟨a, by omega⟩ = P.vertex ⟨b, by omega⟩) (i : Fin (k - (b - a) + 1)) :
    (P.splice a b hab hbk heq).vertex i =
      if i.1 ≤ a then P.vertex ⟨i.1, by have := i.isLt; omega⟩
      else P.vertex ⟨i.1 + (b - a), by have := i.isLt; omega⟩ := rfl

theorem splice_vertex_zero (P : RelPath E T k) (a b : ℕ) (hab : a < b) (hbk : b ≤ k)
    (heq : P.vertex ⟨a, by omega⟩ = P.vertex ⟨b, by omega⟩) :
    (P.splice a b hab hbk heq).vertex ⟨0, by omega⟩ = P.vertex ⟨0, by omega⟩ := by
  rw [splice_vertex, if_pos (show (0 : ℕ) ≤ a from Nat.zero_le a)]

theorem splice_vertex_last (P : RelPath E T k) (a b : ℕ) (hab : a < b) (hbk : b ≤ k)
    (heq : P.vertex ⟨a, by omega⟩ = P.vertex ⟨b, by omega⟩) :
    (P.splice a b hab hbk heq).vertex ⟨k - (b - a), by omega⟩ = P.vertex ⟨k, by omega⟩ := by
  rw [splice_vertex]
  by_cases hc : k - (b - a) ≤ a
  · rw [if_pos hc]
    have hka : k - (b - a) = a := by omega
    rw [show (⟨k - (b - a), by omega⟩ : Fin (k + 1)) = ⟨a, by omega⟩ from Fin.ext hka, heq]
    exact congrArg P.vertex (Fin.ext (by show b = k; omega))
  · rw [if_neg hc]
    exact congrArg P.vertex (Fin.ext (by show k - (b - a) + (b - a) = k; omega))


/-- Appending one further step at the end of a directed walk. -/
def concat (P : RelPath E T k) (x : V) (hx : x ∈ T)
    (hstep : E (P.vertex ⟨k, by omega⟩) x) : RelPath E T (k + 1) where
  vertex := fun i => if h : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩ else x
  mem := by
    intro i
    by_cases h : i.1 ≤ k
    · rw [dif_pos h]; exact P.mem _
    · rw [dif_neg h]; exact hx
  step := by
    intro i
    have hi := i.isLt
    have hcs : (Fin.castSucc i).1 = i.1 := rfl
    have hsu : (i.succ).1 = i.1 + 1 := rfl
    by_cases h : i.1 < k
    · have h1 : (if hc : (Fin.castSucc i).1 ≤ k
          then P.vertex ⟨(Fin.castSucc i).1, by omega⟩ else x)
            = P.vertex ⟨i.1, by omega⟩ := by
        rw [dif_pos (show (Fin.castSucc i).1 ≤ k by rw [hcs]; omega)]
        rfl
      have h2 : (if hc : (i.succ).1 ≤ k then P.vertex ⟨(i.succ).1, by omega⟩ else x)
            = P.vertex ⟨i.1 + 1, by omega⟩ := by
        rw [dif_pos (show (i.succ).1 ≤ k by rw [hsu]; omega)]
        rfl
      show E (if hc : (Fin.castSucc i).1 ≤ k then _ else _)
        (if hc : (i.succ).1 ≤ k then _ else _)
      rw [h1, h2]
      have hst := P.step ⟨i.1, by omega⟩
      have e1 : (Fin.castSucc (⟨i.1, by omega⟩ : Fin k)) = (⟨i.1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      have e2 : ((⟨i.1, by omega⟩ : Fin k).succ) = (⟨i.1 + 1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      rw [e1, e2] at hst
      exact hst
    · have hik : i.1 = k := by omega
      have h1 : (if hc : (Fin.castSucc i).1 ≤ k
          then P.vertex ⟨(Fin.castSucc i).1, by omega⟩ else x)
            = P.vertex ⟨k, by omega⟩ := by
        rw [dif_pos (show (Fin.castSucc i).1 ≤ k by rw [hcs]; omega)]
        exact congrArg P.vertex (Fin.ext (by rw [hcs]; exact hik))
      have h2 : (if hc : (i.succ).1 ≤ k then P.vertex ⟨(i.succ).1, by omega⟩ else x) = x := by
        rw [dif_neg (show ¬ (i.succ).1 ≤ k by rw [hsu]; omega)]
      show E (if hc : (Fin.castSucc i).1 ≤ k then _ else _)
        (if hc : (i.succ).1 ≤ k then _ else _)
      rw [h1, h2]
      exact hstep

@[simp] theorem concat_vertex (P : RelPath E T k) (x : V) (hx : x ∈ T)
    (hstep : E (P.vertex ⟨k, by omega⟩) x) (i : Fin (k + 1 + 1)) :
    (P.concat x hx hstep).vertex i =
      if h : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩ else x := rfl

theorem concat_vertex_le (P : RelPath E T k) (x : V) (hx : x ∈ T)
    (hstep : E (P.vertex ⟨k, by omega⟩) x) (i : Fin (k + 1 + 1)) (h : i.1 ≤ k) :
    (P.concat x hx hstep).vertex i = P.vertex ⟨i.1, by omega⟩ := dif_pos h

theorem concat_vertex_last (P : RelPath E T k) (x : V) (hx : x ∈ T)
    (hstep : E (P.vertex ⟨k, by omega⟩) x) :
    (P.concat x hx hstep).vertex ⟨k + 1, by omega⟩ = x :=
  dif_neg (show ¬ k + 1 ≤ k by omega)

/-- The extended walk is injective as soon as the new vertex was not already on it. -/
theorem concat_injective (P : RelPath E T k) (x : V) (hx : x ∈ T)
    (hstep : E (P.vertex ⟨k, by omega⟩) x) (hinj : Function.Injective P.vertex)
    (hnew : ∀ i, P.vertex i ≠ x) : Function.Injective (P.concat x hx hstep).vertex := by
  intro a b hab
  have ha := a.isLt
  have hb := b.isLt
  rw [concat_vertex, concat_vertex] at hab
  by_cases hla : a.1 ≤ k <;> by_cases hlb : b.1 ≤ k
  · rw [dif_pos hla, dif_pos hlb] at hab
    have hv := congrArg Fin.val (hinj hab)
    exact Fin.ext hv
  · rw [dif_pos hla, dif_neg hlb] at hab
    exact absurd hab (hnew _)
  · rw [dif_neg hla, dif_pos hlb] at hab
    exact absurd hab.symm (hnew _)
  · exact Fin.ext (by omega)

end RelPath

/-- A directed walk exists along any reflexive-transitive chain, and stays in `T` whenever `T`
is closed under predecessors and contains the chain's endpoint. -/
theorem exists_relPath_of_reflTransGen {E : V → V → Prop} {T : Finset V}
    (hclosed : ∀ x y, E x y → y ∈ T → x ∈ T) {a b : V} (hbT : b ∈ T)
    (h : Relation.ReflTransGen E a b) :
    ∃ (k : ℕ) (P : RelPath E T k),
      P.vertex ⟨0, by omega⟩ = a ∧ P.vertex ⟨k, by omega⟩ = b := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exact ⟨0,
      { vertex := fun _ => b, mem := fun _ => hbT,
        step := fun i => absurd i.isLt (by omega) },
      rfl, rfl⟩
  | @head u c hac _ ih =>
    obtain ⟨k, P, h0, hk⟩ := ih
    have hcT : c ∈ T := h0 ▸ P.mem ⟨0, by omega⟩
    have h0' : P.vertex 0 = c := by
      rw [show (0 : Fin (k + 1)) = ⟨0, by omega⟩ from Fin.ext rfl]; exact h0
    refine ⟨k + 1, ⟨Fin.cases u P.vertex, ?_, ?_⟩, ?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · show u ∈ T
        exact hclosed u c hac hcT
      · intro j
        show P.vertex j ∈ T
        exact P.mem j
    · intro i
      refine Fin.cases ?_ ?_ i
      · show E u (P.vertex 0)
        rw [h0']
        exact hac
      · intro j
        show E (P.vertex (Fin.castSucc j)) (P.vertex j.succ)
        exact P.step j
    · show Fin.cases u P.vertex (0 : Fin (k + 1 + 1)) = u
      exact Fin.cases_zero
    · show Fin.cases u P.vertex ((⟨k, by omega⟩ : Fin (k + 1)).succ) = b
      rw [Fin.cases_succ]
      exact hk

/-- **A shortest directed path out of a distinguished set is injective and leaves the set at
once.**  Splicing out a repeated vertex, or restarting from a later member of the set, both
produce a strictly shorter such path. -/
theorem exists_minimal_relPath {E : V → V → Prop} {T : Finset V} (Good : V → Prop)
    (hclosed : ∀ x y, E x y → y ∈ T → x ∈ T) {a₀ b : V} (hbT : b ∈ T)
    (hga₀ : Good a₀) (h : Relation.ReflTransGen E a₀ b) :
    ∃ (k : ℕ) (P : RelPath E T k),
      Good (P.vertex ⟨0, by omega⟩) ∧ P.vertex ⟨k, by omega⟩ = b ∧
        Function.Injective P.vertex ∧
        ∀ i : Fin (k + 1), i.1 ≠ 0 → ¬ Good (P.vertex i) := by
  classical
  obtain ⟨k₀, P₀, h0, hk⟩ := exists_relPath_of_reflTransGen hclosed hbT h
  -- strong induction on the length of a path witnessing the two endpoint conditions
  suffices H : ∀ k : ℕ, ∀ P : RelPath E T k,
      Good (P.vertex ⟨0, by omega⟩) → P.vertex ⟨k, by omega⟩ = b →
      ∃ (k' : ℕ) (P' : RelPath E T k'),
        Good (P'.vertex ⟨0, by omega⟩) ∧ P'.vertex ⟨k', by omega⟩ = b ∧
          Function.Injective P'.vertex ∧
          ∀ i : Fin (k' + 1), i.1 ≠ 0 → ¬ Good (P'.vertex i) by
    exact H k₀ P₀ (by rw [h0]; exact hga₀) hk
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro P hg hb
    by_cases hinj : Function.Injective P.vertex
    · by_cases hlate : ∀ i : Fin (k + 1), i.1 ≠ 0 → ¬ Good (P.vertex i)
      · exact ⟨k, P, hg, hb, hinj, hlate⟩
      · push_neg at hlate
        obtain ⟨i, hi0, hgi⟩ := hlate
        have hik := i.isLt
        refine ih (k - i.1) (by omega) (P.tail i.1 (by omega)) ?_ ?_
        · rw [RelPath.tail_vertex]
          have : (⟨i.1 + (0 : ℕ), by omega⟩ : Fin (k + 1)) = i :=
            Fin.ext (by show i.1 + 0 = i.1; omega)
          rw [this]
          exact hgi
        · rw [RelPath.tail_vertex]
          exact (congrArg P.vertex
            (Fin.ext (by show i.1 + (k - i.1) = k; omega))).trans hb
    · -- a repeated vertex: splice it out
      have hrep : ∃ x y : Fin (k + 1), x.1 < y.1 ∧ P.vertex x = P.vertex y := by
        by_contra hno
        push_neg at hno
        refine hinj ?_
        intro x y hxy
        rcases lt_trichotomy x.1 y.1 with hlt | heq | hgt
        · exact absurd hxy (hno x y hlt)
        · exact Fin.ext heq
        · exact absurd hxy.symm (hno y x hgt)
      obtain ⟨x, y, hxy, hveq⟩ := hrep
      have hyk := y.isLt
      have hveq' : P.vertex ⟨x.1, by omega⟩ = P.vertex ⟨y.1, by omega⟩ := by
        rw [show (⟨x.1, by omega⟩ : Fin (k + 1)) = x from Fin.ext rfl,
          show (⟨y.1, by omega⟩ : Fin (k + 1)) = y from Fin.ext rfl]
        exact hveq
      refine ih (k - (y.1 - x.1)) (by omega) (P.splice x.1 y.1 hxy (by omega) hveq') ?_ ?_
      · rw [RelPath.splice_vertex_zero]
        exact hg
      · rw [RelPath.splice_vertex_last]
        exact hb

/-- A shortest directed path from a distinguished set to a fixed target is simple, leaves the
set immediately, and has minimum length among all such paths. -/
theorem exists_shortest_relPath {E : V → V → Prop} {T : Finset V} (Good : V → Prop)
    (hclosed : ∀ x y, E x y → y ∈ T → x ∈ T) {a₀ b : V} (hbT : b ∈ T)
    (hga₀ : Good a₀) (h : Relation.ReflTransGen E a₀ b) :
    ∃ (k : ℕ) (P : RelPath E T k),
      Good (P.vertex ⟨0, by omega⟩) ∧ P.vertex ⟨k, by omega⟩ = b ∧
        Function.Injective P.vertex ∧
        (∀ i : Fin (k + 1), i.1 ≠ 0 → ¬ Good (P.vertex i)) ∧
        ∀ (l : ℕ) (Q : RelPath E T l),
          Good (Q.vertex ⟨0, by omega⟩) → Q.vertex ⟨l, by omega⟩ = b → k ≤ l := by
  classical
  obtain ⟨k₀, P₀, h₀, h₀last⟩ := exists_relPath_of_reflTransGen hclosed hbT h
  let HasPath : ℕ → Prop := fun l =>
    ∃ Q : RelPath E T l, Good (Q.vertex ⟨0, by omega⟩) ∧
      Q.vertex ⟨l, by omega⟩ = b
  have hHasPath : ∃ l, HasPath l := ⟨k₀, P₀, by rw [h₀]; exact hga₀, h₀last⟩
  let k := Nat.find hHasPath
  have hk : HasPath k := Nat.find_spec hHasPath
  obtain ⟨P, hPzero, hPlast⟩ := hk
  have hmin : ∀ (l : ℕ) (Q : RelPath E T l),
      Good (Q.vertex ⟨0, by omega⟩) → Q.vertex ⟨l, by omega⟩ = b → k ≤ l := by
    intro l Q hQzero hQlast
    exact Nat.find_min' hHasPath ⟨Q, hQzero, hQlast⟩
  have hinj : Function.Injective P.vertex := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · have hveq : P.vertex ⟨i.1, by omega⟩ = P.vertex ⟨j.1, by omega⟩ := by
        simpa using hij
      let Q := P.splice i.1 j.1 hlt (by omega) hveq
      have hQzero : Good (Q.vertex ⟨0, by omega⟩) := by
        change Good ((P.splice i.1 j.1 hlt (by omega) hveq).vertex ⟨0, by omega⟩)
        rw [RelPath.splice_vertex_zero]
        exact hPzero
      have hQlast : Q.vertex ⟨k - (j.1 - i.1), by omega⟩ = b := by
        change (P.splice i.1 j.1 hlt (by omega) hveq).vertex
          ⟨k - (j.1 - i.1), by omega⟩ = b
        rw [RelPath.splice_vertex_last]
        exact hPlast
      have hshort := hmin (k - (j.1 - i.1)) Q hQzero hQlast
      omega
    · exact Fin.ext heq
    · have hveq : P.vertex ⟨j.1, by omega⟩ = P.vertex ⟨i.1, by omega⟩ := by
        simpa using hij.symm
      let Q := P.splice j.1 i.1 hgt (by omega) hveq
      have hQzero : Good (Q.vertex ⟨0, by omega⟩) := by
        change Good ((P.splice j.1 i.1 hgt (by omega) hveq).vertex ⟨0, by omega⟩)
        rw [RelPath.splice_vertex_zero]
        exact hPzero
      have hQlast : Q.vertex ⟨k - (i.1 - j.1), by omega⟩ = b := by
        change (P.splice j.1 i.1 hgt (by omega) hveq).vertex
          ⟨k - (i.1 - j.1), by omega⟩ = b
        rw [RelPath.splice_vertex_last]
        exact hPlast
      have hshort := hmin (k - (i.1 - j.1)) Q hQzero hQlast
      omega
  have hlate : ∀ i : Fin (k + 1), i.1 ≠ 0 → ¬ Good (P.vertex i) := by
    intro i hi0 hGood
    let Q := P.tail i.1 (by omega)
    have hQzero : Good (Q.vertex ⟨0, by omega⟩) := by
      change Good ((P.tail i.1 (by omega)).vertex ⟨0, by omega⟩)
      rw [RelPath.tail_vertex]
      have heq : (⟨i.1 + 0, by omega⟩ : Fin (k + 1)) = i := Fin.ext (by simp)
      rw [heq]
      exact hGood
    have hQlast : Q.vertex ⟨k - i.1, by omega⟩ = b := by
      change (P.tail i.1 (by omega)).vertex ⟨k - i.1, by omega⟩ = b
      rw [RelPath.tail_vertex]
      have hle : i.1 ≤ k := by omega
      have hv : i.1 + (k - i.1) = k := Nat.add_sub_of_le hle
      have heq : (⟨i.1 + (k - i.1), by omega⟩ : Fin (k + 1)) =
          (⟨k, by omega⟩ : Fin (k + 1)) := Fin.ext hv
      exact (congrArg P.vertex heq).trans hPlast
    have hshort := hmin (k - i.1) Q hQzero hQlast
    omega
  exact ⟨k, P, hPzero, hPlast, hinj, hlate, hmin⟩

/-- In a shortest path to `q`, a vertex with a direct edge into `q` can occur only immediately
before the endpoint. -/
theorem shortestRelPath_incoming_is_last_edge {E : V → V → Prop} {T : Finset V}
    {Good : V → Prop} {m : ℕ} {q u : V} (P : RelPath E T m)
    (hmin : ∀ (l : ℕ) (Q : RelPath E T l),
      Good (Q.vertex ⟨0, by omega⟩) → Q.vertex ⟨l, by omega⟩ = q → m ≤ l)
    (hqT : q ∈ T) (hGood : Good (P.vertex ⟨0, by omega⟩))
    (hEnd : P.vertex ⟨m, by omega⟩ = q) (hstep : E u q)
    (hbefore : ∀ j : Fin (m + 1), P.vertex j = u → j.1 < m)
    (j : Fin (m + 1)) (hju : P.vertex j = u) : j.1 + 1 = m := by
  have hjle : j.1 ≤ m := by omega
  let initialSegment := P.take j.1 hjle
  have hstep' : E (initialSegment.vertex ⟨j.1, by omega⟩) q := by
    rw [RelPath.take_vertex_last, hju]
    exact hstep
  let R := initialSegment.concat q hqT hstep'
  have hRzero : Good (R.vertex ⟨0, by omega⟩) := by
    change Good ((initialSegment.concat q hqT hstep').vertex ⟨0, by omega⟩)
    rw [RelPath.concat_vertex_le initialSegment q hqT hstep'
      (⟨0, by omega⟩ : Fin (j.1 + 1 + 1)) (Nat.zero_le _)]
    change Good ((P.take j.1 hjle).vertex ⟨0, by omega⟩)
    rw [RelPath.take_vertex_zero]
    exact hGood
  have hRlast : R.vertex ⟨j.1 + 1, by omega⟩ = q := by
    change (initialSegment.concat q hqT hstep').vertex ⟨j.1 + 1, by omega⟩ = q
    exact RelPath.concat_vertex_last initialSegment q hqT hstep'
  have hlen := hmin (j.1 + 1) R hRzero hRlast
  have hlt := hbefore j hju
  omega

/-- A shortest directed path from a fixed vertex to a distinguished set is injective and
meets that set only at its endpoint. -/
theorem exists_shortest_relPath_to_good {E : V → V → Prop} {T : Finset V}
    (Good : V → Prop) (hclosed : ∀ x y, E x y → y ∈ T → x ∈ T)
    {a b : V} (hbT : b ∈ T) (h : Relation.ReflTransGen E a b) (hbGood : Good b) :
    ∃ (k : ℕ) (P : RelPath E T k),
      P.vertex ⟨0, by omega⟩ = a ∧ Good (P.vertex ⟨k, by omega⟩) ∧
        Function.Injective P.vertex ∧
        (∀ i : Fin (k + 1), i.1 ≠ k → ¬ Good (P.vertex i)) ∧
        ∀ (l : ℕ) (Q : RelPath E T l),
          Q.vertex ⟨0, by omega⟩ = a → Good (Q.vertex ⟨l, by omega⟩) → k ≤ l := by
  classical
  obtain ⟨k₀, P₀, hP₀start, hP₀last⟩ := exists_relPath_of_reflTransGen hclosed hbT h
  let HasPath : ℕ → Prop := fun l =>
    ∃ Q : RelPath E T l, Q.vertex ⟨0, by omega⟩ = a ∧ Good (Q.vertex ⟨l, by omega⟩)
  have hHasPath : ∃ l, HasPath l :=
    ⟨k₀, P₀, hP₀start, hP₀last ▸ hbGood⟩
  let k := Nat.find hHasPath
  have hk : HasPath k := Nat.find_spec hHasPath
  obtain ⟨P, hPstart, hPgood⟩ := hk
  have hmin : ∀ (l : ℕ) (Q : RelPath E T l),
      Q.vertex ⟨0, by omega⟩ = a → Good (Q.vertex ⟨l, by omega⟩) → k ≤ l := by
    intro l Q hQstart hQgood
    exact Nat.find_min' hHasPath ⟨Q, hQstart, hQgood⟩
  have hinj : Function.Injective P.vertex := by
    intro i j hij
    have hi := i.isLt
    have hj := j.isLt
    rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · have hveq : P.vertex ⟨i.1, by omega⟩ = P.vertex ⟨j.1, by omega⟩ := by
        simpa using hij
      let Q := P.splice i.1 j.1 hlt (by omega) hveq
      have hQstart : Q.vertex ⟨0, by omega⟩ = a := by
        change (P.splice i.1 j.1 hlt (by omega) hveq).vertex ⟨0, by omega⟩ = a
        rw [RelPath.splice_vertex_zero]
        exact hPstart
      have hQgood : Good (Q.vertex ⟨k - (j.1 - i.1), by omega⟩) := by
        change Good ((P.splice i.1 j.1 hlt (by omega) hveq).vertex
          ⟨k - (j.1 - i.1), by omega⟩)
        rw [RelPath.splice_vertex_last]
        exact hPgood
      have hshort := hmin (k - (j.1 - i.1)) Q hQstart hQgood
      omega
    · exact Fin.ext heq
    · have hveq : P.vertex ⟨j.1, by omega⟩ = P.vertex ⟨i.1, by omega⟩ := by
        simpa using hij.symm
      let Q := P.splice j.1 i.1 hgt (by omega) hveq
      have hQstart : Q.vertex ⟨0, by omega⟩ = a := by
        change (P.splice j.1 i.1 hgt (by omega) hveq).vertex ⟨0, by omega⟩ = a
        rw [RelPath.splice_vertex_zero]
        exact hPstart
      have hQgood : Good (Q.vertex ⟨k - (i.1 - j.1), by omega⟩) := by
        change Good ((P.splice j.1 i.1 hgt (by omega) hveq).vertex
          ⟨k - (i.1 - j.1), by omega⟩)
        rw [RelPath.splice_vertex_last]
        exact hPgood
      have hshort := hmin (k - (i.1 - j.1)) Q hQstart hQgood
      omega
  have hlate : ∀ i : Fin (k + 1), i.1 ≠ k → ¬ Good (P.vertex i) := by
    intro i hik hGood
    have hilt := i.isLt
    have hiLt : i.1 < k := by omega
    let Q := P.take i.1 (by omega)
    have hQstart : Q.vertex ⟨0, by omega⟩ = a := by
      change (P.take i.1 (by omega)).vertex ⟨0, by omega⟩ = a
      rw [RelPath.take_vertex_zero]
      exact hPstart
    have hQgood : Good (Q.vertex ⟨i.1, by omega⟩) := by
      change Good ((P.take i.1 (by omega)).vertex ⟨i.1, by omega⟩)
      rw [RelPath.take_vertex_last]
      have hidx : (⟨i.1, by omega⟩ : Fin (k + 1)) = i := Fin.ext rfl
      rw [hidx]
      exact hGood
    have hshort := hmin i.1 Q hQstart hQgood
    omega
  exact ⟨k, P, hPstart, hPgood, hinj, hlate, hmin⟩

/-- Forget the vertex-set bookkeeping and read a `RelPath` as a reflexive-transitive chain. -/
theorem relPath_reflTransGen {E : V → V → Prop} {T : Finset V} {k : ℕ}
    (P : RelPath E T k) :
    Relation.ReflTransGen E (P.vertex ⟨0, by omega⟩) (P.vertex ⟨k, by omega⟩) := by
  induction k with
  | zero =>
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      let pshort := P.take k (by omega)
      have hprefix :
          Relation.ReflTransGen E (P.vertex ⟨0, by omega⟩) (P.vertex ⟨k, by omega⟩) := by
        simpa [pshort, RelPath.take_vertex_zero, RelPath.take_vertex_last] using ih pshort
      have hlast : E (P.vertex ⟨k, by omega⟩) (P.vertex ⟨k + 1, by omega⟩) := by
        have h := P.step (⟨k, by omega⟩ : Fin (k + 1))
        have hfirst : Fin.castSucc (⟨k, by omega⟩ : Fin (k + 1)) =
            (⟨k, by omega⟩ : Fin (k + 1 + 1)) := Fin.ext rfl
        have hsecond : (⟨k, by omega⟩ : Fin (k + 1)).succ =
            (⟨k + 1, by omega⟩ : Fin (k + 1 + 1)) := Fin.ext rfl
        rw [hfirst, hsecond] at h
        exact h
      have hend : (⟨k + 1, by omega⟩ : Fin (k + 1 + 1)) =
          (⟨Nat.succ k, by omega⟩ : Fin (Nat.succ k + 1)) := Fin.ext rfl
      rw [hend]
      exact Relation.ReflTransGen.tail hprefix hlast

end CRNT
