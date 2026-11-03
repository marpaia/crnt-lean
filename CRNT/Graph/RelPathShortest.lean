import CRNT.Graph.RelPath

/-!
# Shortest directed paths between two fixed vertices

`CRNT.RelPath` supplies indexed directed walks together with the cut operations `take`,
`tail`, `splice` and one-step `concat`, and `exists_shortest_relPath` already produces a
minimal walk *out of a predicate `Good`* (or, symmetrically, *into* one).  The true-SR
endgame needs the remaining shape: a minimum-length walk between **two fixed vertices**.

Everything here is generic graph theory — no `Network`, no stoichiometry — so it is the layer
that the SR modules consume rather than re-derive.

The payoffs:

* `RelPath.edge` is the one-step walk along a single edge.
* `ShortestPath` bundles a walk with its endpoints and its `Nat`-minimality;
  `ShortestPath.of_reflTransGen` builds one out of a bare `Relation.ReflTransGen` by
  `Nat.find`, and `exists_shortestPath` says reachability is the *only* hypothesis needed.
* `ShortestPath.injective`: a shortest path is simple.
* `le_one_of_edge` / `length_eq_one_of_edge`: **the no-shortcut lemma.**  If a shortest path's
  start already has a direct edge to its target, the path has length exactly one.  This is the
  "the residue needs a path of length 1" statement, in the shape the residue needs it.

## Not in this file

A general `RelPath.append` (concatenation at an arbitrary shared vertex) and the
prefix/suffix minimality built on it are deliberately **not** here.  Proving `append`'s `step`
field needs index arithmetic across the join, and three attempts failed to elaborate; the
existing `RelPath.concat` (one step) plus `take`/`tail`/`splice` already cover every consumer
in the tree.  See `research/routes/sr-shortest-path.md` for the failure detail.
-/

namespace CRNT

variable {V : Type*}

namespace RelPath

variable {E : V → V → Prop} {T : Finset V} {k : ℕ}

/-- **The one-step directed walk along the edge `h : E x y`.**  This is the object the
no-shortcut lemmas are stated against: a shortest path whose endpoints are already joined by
`h` has length one. -/
def edge (x y : V) (hx : x ∈ T) (hy : y ∈ T) (h : E x y) : RelPath E T 1 where
  vertex := Fin.cases x (fun _ => y)
  mem := by
    intro i
    refine Fin.cases hx ?_ i
    intro j
    exact hy
  step := by
    intro i
    have hi : i = (⟨0, by omega⟩ : Fin 1) := Fin.ext (by have := i.isLt; omega)
    subst hi
    show E (Fin.cases x (fun _ => y) (Fin.castSucc (⟨0, by omega⟩ : Fin 1)))
      (Fin.cases x (fun _ => y) ((⟨0, by omega⟩ : Fin 1).succ))
    simp only [Fin.cases_succ]
    exact h

@[simp] theorem edge_vertex_zero (x y : V) (hx : x ∈ T) (hy : y ∈ T) (h : E x y) :
    (edge x y hx hy h).vertex ⟨0, by omega⟩ = x := rfl

@[simp] theorem edge_vertex_one (x y : V) (hx : x ∈ T) (hy : y ∈ T) (h : E x y) :
    (edge x y hx hy h).vertex ⟨1, by omega⟩ = y := by
  show Fin.cases x (fun _ => y) ((⟨0, by omega⟩ : Fin 1).succ) = y
  rw [Fin.cases_succ]

/-- **A shortest directed walk between two fixed vertices.**  `path` stays inside `T`, runs from
`a` to `b`, and `min_length` says its length is at most the length of *every* directed walk in
`T` from `a` to `b`. -/
structure ShortestPath (E : V → V → Prop) (T : Finset V) (a b : V) where
  length : ℕ
  path : RelPath E T length
  start_eq : path.vertex ⟨0, by omega⟩ = a
  end_eq : path.vertex ⟨length, by omega⟩ = b
  min_length : ∀ (l : ℕ) (Q : RelPath E T l),
    Q.vertex ⟨0, by omega⟩ = a → Q.vertex ⟨l, by omega⟩ = b → length ≤ l

/-- **Reachability produces a shortest path.**  Existence of *some* walk comes from
`exists_relPath_of_reflTransGen`; `Nat.find` then picks the least admissible length, and
`Nat.find_min'` supplies the minimality clause. -/
noncomputable def ShortestPath.of_reflTransGen (hclosed : ∀ x y, E x y → y ∈ T → x ∈ T)
    {a b : V} (hbT : b ∈ T) (h : Relation.ReflTransGen E a b) : ShortestPath E T a b := by
  classical
  refine Classical.choice (α := ShortestPath E T a b) ?_
  show Nonempty (ShortestPath E T a b)
  obtain ⟨k₀, P₀, h₀, h₀last⟩ := exists_relPath_of_reflTransGen hclosed hbT h
  let HasPath : ℕ → Prop := fun l =>
    ∃ Q : RelPath E T l, Q.vertex ⟨0, by omega⟩ = a ∧ Q.vertex ⟨l, by omega⟩ = b
  have hExists : ∃ l, HasPath l := ⟨k₀, P₀, h₀, h₀last⟩
  have hk : HasPath (Nat.find hExists) := Nat.find_spec hExists
  obtain ⟨P, hPstart, hPend⟩ := hk
  refine ⟨{ length := Nat.find hExists, path := P, start_eq := hPstart, end_eq := hPend,
            min_length := ?_ }⟩
  intro l Q hQstart hQlast
  exact Nat.find_min' hExists ⟨Q, hQstart, hQlast⟩

/-- **Reachability is the only hypothesis**: a shortest path from `a` to `b` exists exactly
when `b` is reachable from `a` along `E`. -/
theorem exists_shortestPath {a b : V} (hclosed : ∀ x y, E x y → y ∈ T → x ∈ T)
    (hbT : b ∈ T) :
    (∃ _P : ShortestPath E T a b, True) ↔ Relation.ReflTransGen E a b :=
  ⟨fun h => by
    have hh := relPath_reflTransGen h.choose.path
    rw [h.choose.start_eq, h.choose.end_eq] at hh
    exact hh,
    fun h => ⟨ShortestPath.of_reflTransGen hclosed hbT h, trivial⟩⟩

/-- A shortest path is a simple path: no vertex repeats. -/
theorem ShortestPath.injective (P : ShortestPath E T a b) : Function.Injective P.path.vertex := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
  · have hveq : P.path.vertex ⟨i.1, by omega⟩ = P.path.vertex ⟨j.1, by omega⟩ := by
      simpa using hij
    let Q := P.path.splice i.1 j.1 hlt (by omega) hveq
    have hQstart : Q.vertex ⟨0, by omega⟩ = a := by
      change (P.path.splice i.1 j.1 hlt (by omega) hveq).vertex ⟨0, by omega⟩ = a
      rw [RelPath.splice_vertex_zero]
      exact P.start_eq
    have hQend : Q.vertex ⟨P.length - (j.1 - i.1), by omega⟩ = b := by
      change (P.path.splice i.1 j.1 hlt (by omega) hveq).vertex
        ⟨P.length - (j.1 - i.1), by omega⟩ = b
      rw [RelPath.splice_vertex_last]
      exact P.end_eq
    have h := P.min_length (P.length - (j.1 - i.1)) Q hQstart hQend
    omega
  · exact Fin.ext heq
  · have hveq : P.path.vertex ⟨j.1, by omega⟩ = P.path.vertex ⟨i.1, by omega⟩ := by
      simpa using hij.symm
    let Q := P.path.splice j.1 i.1 hgt (by omega) hveq
    have hQstart : Q.vertex ⟨0, by omega⟩ = a := by
      change (P.path.splice j.1 i.1 hgt (by omega) hveq).vertex ⟨0, by omega⟩ = a
      rw [RelPath.splice_vertex_zero]
      exact P.start_eq
    have hQend : Q.vertex ⟨P.length - (i.1 - j.1), by omega⟩ = b := by
      change (P.path.splice j.1 i.1 hgt (by omega) hveq).vertex
        ⟨P.length - (i.1 - j.1), by omega⟩ = b
      rw [RelPath.splice_vertex_last]
      exact P.end_eq
    have h := P.min_length (P.length - (i.1 - j.1)) Q hQstart hQend
    omega

/-- On a shortest path, equal vertices occur at equal positions. -/
theorem ShortestPath.eq_of_vertex_eq (P : ShortestPath E T a b) {i j : Fin (P.length + 1)}
    (h : P.path.vertex i = P.path.vertex j) : i = j :=
  P.injective h

/-- **The no-shortcut lemma.**  If a shortest path's start vertex already has a direct edge to
its end vertex, the path has length at most one. -/
theorem ShortestPath.le_one_of_edge (P : ShortestPath E T a b) (hedge : E a b) :
    P.length ≤ 1 := by
  have haT : a ∈ T := by rw [← P.start_eq]; exact P.path.mem ⟨0, by omega⟩
  have hbT : b ∈ T := by rw [← P.end_eq]; exact P.path.mem ⟨P.length, by omega⟩
  have h := P.min_length 1 (RelPath.edge a b haT hbT hedge)
    (RelPath.edge_vertex_zero a b haT hbT hedge).symm
    (RelPath.edge_vertex_one a b haT hbT hedge).symm
  omega

/-- **No-shortcut, endpoint form.**  When `a` and `b` are genuinely different, a shortest path
from `a` to `b` together with a direct edge `E a b` has length *exactly* one — this is the
"the residue needs a path of length 1" statement. -/
theorem ShortestPath.length_eq_one_of_edge (P : ShortestPath E T a b) (hedge : E a b)
    (hab : a ≠ b) : P.length = 1 := by
  have hle := P.le_one_of_edge hedge
  have hne : P.length ≠ 0 := by
    intro hz
    have hidx : (⟨0, by omega⟩ : Fin (P.length + 1)) = ⟨P.length, by omega⟩ :=
      Fin.ext (by omega)
    exact hab (P.start_eq.symm.trans (hidx ▸ P.end_eq))
  omega

/-- **No-shortcut, negated form.**  A shortest path of length at least two between distinct
vertices witnesses that its start has no direct edge to its end. -/
theorem ShortestPath.not_edge_of_length_ge_two (P : ShortestPath E T a b)
    (h2 : 2 ≤ P.length) : ¬ E a b := by
  intro hedge
  have hle := P.le_one_of_edge hedge
  omega

end RelPath

end CRNT