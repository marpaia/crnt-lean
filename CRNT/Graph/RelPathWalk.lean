import CRNT.Graph.RelPath
import CRNT.Graph.FiniteSource

/-!
# Lifting unoriented walks to directed `RelPath`s

`CRNT.relationGraphOn E T` forgets the orientation of the causal relation, so a walk
found inside a strongly connected source is a walk in a *symmetric* graph. The
orientation-sensitive endgame needs a `CRNT.RelPath`, i.e. a walk with one chosen
direction on every step.

This file supplies that lift. It lives in its own module because `CRNT.Graph.RelPath`
must not import `CRNT.Graph.FiniteSource` (which would invert the module layering:
the `Multistationarity` layer depends on `RelPath`, not the other way round), while
`FiniteSource.lean` in turn does not import `RelPath`.

Two facts have to be handled explicitly:

* `relationGraphOn` is a `SimpleGraph` on the subtypes `{v // v ∈ T}`, so the
  `RelPath` is built over `V` by projecting with `.1`; membership in `T` then comes
  from the subtype proof rather than from `Finset` search;
* `Adj u v := u.1 ≠ v.1 ∧ (E u.1 v.1 ∨ E v.1 u.1)` admits **either** orientation, so
  the direction cannot be recovered from the walk. It is supplied as an explicit
  hypothesis `hdir`, which discards the `Or.inr` branch.

`RelPath.append` is also placed here: `RelPath.concat` in `CRNT/Graph/RelPath.lean`
only appends a *single* further step, so gluing a whole second `RelPath` onto the end
of a first one has to be built somewhere, and this is the module that already owns the
`RelPath` ↔ `Walk` correspondence.
-/

namespace CRNT

variable {V : Type*} {E : V → V → Prop} {T : Finset V} {a b : {v // v ∈ T}}

/-- A walk in the unoriented induced graph, together with a choice of orientation on
every step, is a `RelPath` over `V`. -/
def relPathOfWalk (W : (relationGraphOn E T).Walk a b)
    (hdir : ∀ i : Fin W.length, E (W.getVert i.1).1 (W.getVert i.1.succ).1) :
    RelPath E T W.length where
  vertex := fun i => (W.getVert i.1).1
  mem := fun i => (W.getVert i.1).property
  step := fun i => hdir i

@[simp] theorem relPathOfWalk_vertex (W : (relationGraphOn E T).Walk a b)
    (hdir : ∀ i : Fin W.length, E (W.getVert i.1).1 (W.getVert i.1.succ).1)
    (i : Fin (W.length + 1)) :
    (relPathOfWalk W hdir).vertex i = (W.getVert i.1).1 := rfl

@[simp] theorem relPathOfWalk_vertex_zero (W : (relationGraphOn E T).Walk a b)
    (hdir : ∀ i : Fin W.length, E (W.getVert i.1).1 (W.getVert i.1.succ).1) :
    (relPathOfWalk W hdir).vertex ⟨0, by omega⟩ = a.1 := by
  rw [relPathOfWalk_vertex]
  exact congrArg Subtype.val (W.getVert_zero)

@[simp] theorem relPathOfWalk_vertex_length (W : (relationGraphOn E T).Walk a b)
    (hdir : ∀ i : Fin W.length, E (W.getVert i.1).1 (W.getVert i.1.succ).1) :
    (relPathOfWalk W hdir).vertex ⟨W.length, by omega⟩ = b.1 := by
  rw [relPathOfWalk_vertex]
  exact congrArg Subtype.val (W.getVert_length)

/-- A walk that is a path in the underlying graph lifts to an injective `RelPath`.
`Walk.IsPath` is `p.support.Nodup`, and `getVert` reads off `p.support.get`, so
nodupness of the support gives injectivity of `getVert` on `Fin (p.length + 1)`. -/
theorem relPathOfWalk_injective_of_isPath (W : (relationGraphOn E T).Walk a b)
    (hdir : ∀ i : Fin W.length, E (W.getVert i.1).1 (W.getVert i.1.succ).1)
    (hW : W.IsPath) : Function.Injective (relPathOfWalk W hdir).vertex := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  rw [relPathOfWalk_vertex, relPathOfWalk_vertex] at hij
  have hinj : Function.Injective W.support.get :=
    List.nodup_iff_injective_get.mp hW.support_nodup
  have hcomp : W.getVert ∘ Fin.val = W.support.get :=
    SimpleGraph.Walk.getVert_comp_val_eq_get_support W
  have hc : W.length + 1 = W.support.length := W.length_support.symm
  have happ (t : Fin (W.length + 1)) :
      W.getVert t.1 = W.support.get (Fin.cast hc t) := by
    show (W.getVert ∘ Fin.val) (Fin.cast hc t) = W.support.get (Fin.cast hc t)
    rw [hcomp]
  have hij' : W.getVert i.1 = W.getVert j.1 := Subtype.ext hij
  have hz : W.support.get (Fin.cast hc i) = W.support.get (Fin.cast hc j) :=
    (happ i).symm.trans (hij'.trans (happ j))
  exact Fin.ext (congrArg (fun z : Fin W.support.length => z.1) (hinj hz))

/-- The endpoints of the lifted path, stated for the ambient vertex type. -/
theorem relPathOfWalk_mem (W : (relationGraphOn E T).Walk a b)
    (hdir : ∀ i : Fin W.length, E (W.getVert i.1).1 (W.getVert i.1.succ).1)
    (i : Fin (W.length + 1)) : (relPathOfWalk W hdir).vertex i ∈ T :=
  (relPathOfWalk W hdir).mem i

namespace RelPath

variable {E : V → V → Prop} {T : Finset V} {k l : ℕ}

/-- Concatenating two `RelPath`s that meet at the shared endpoint. -/
def append (P : RelPath E T k) (Q : RelPath E T l) (hl : 0 < l)
    (hjoin : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩) :
    RelPath E T (k + l) where
  vertex := fun i =>
    if h : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩ else Q.vertex ⟨i.1 - k, by omega⟩
  mem := by
    intro i
    by_cases h : i.1 ≤ k
    · rw [dif_pos h]; exact P.mem _
    · rw [dif_neg h]; exact Q.mem _
  step := by
    intro i
    have hi : i.1 < k + l := i.isLt
    by_cases hlt : i.1 < k
    · have hik : i.1 ≤ k := by omega
      have hik' : i.1 + 1 ≤ k := by omega
      show E (if hc : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩ else
          Q.vertex ⟨i.1 - k, by omega⟩)
        (if hc : i.1 + 1 ≤ k then P.vertex ⟨i.1 + 1, by omega⟩ else
          Q.vertex ⟨i.1 + 1 - k, by omega⟩)
      rw [dif_pos hik, dif_pos hik']
      have hst := P.step ⟨i.1, by omega⟩
      have e1 : (Fin.castSucc (⟨i.1, by omega⟩ : Fin k)) = (⟨i.1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      have e2 : ((⟨i.1, by omega⟩ : Fin k).succ) = (⟨i.1 + 1, by omega⟩ : Fin (k + 1)) :=
        Fin.ext rfl
      rw [e1, e2] at hst
      exact hst
    · by_cases heq : i.1 = k
      · have hik : i.1 ≤ k := by omega
        have hik' : ¬ i.1 + 1 ≤ k := by omega
        show E (if hc : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩ else
            Q.vertex ⟨i.1 - k, by omega⟩)
          (if hc : i.1 + 1 ≤ k then P.vertex ⟨i.1 + 1, by omega⟩ else
            Q.vertex ⟨i.1 + 1 - k, by omega⟩)
        rw [dif_pos hik, dif_neg hik']
        show E (P.vertex (⟨i.1, by omega⟩ : Fin (k + 1)))
          (Q.vertex (⟨i.1 + 1 - k, by omega⟩ : Fin (l + 1)))
        have hidx1 : (⟨i.1, by omega⟩ : Fin (k + 1)) = ⟨k, by omega⟩ := Fin.ext heq
        have hidx2 : (⟨i.1 + 1 - k, by omega⟩ : Fin (l + 1)) = ⟨1, by omega⟩ :=
          Fin.ext (show i.1 + 1 - k = 1 by rw [heq]; omega)
        rw [hidx1, hidx2]
        exact hjoin ▸ Q.step ⟨0, by omega⟩
      · have hik : ¬ i.1 ≤ k := by omega
        have hik' : ¬ i.1 + 1 ≤ k := by omega
        show E (if hc : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩ else
            Q.vertex ⟨i.1 - k, by omega⟩)
          (if hc : i.1 + 1 ≤ k then P.vertex ⟨i.1 + 1, by omega⟩ else
            Q.vertex ⟨i.1 + 1 - k, by omega⟩)
        rw [dif_neg hik, dif_neg hik']
        have hst := Q.step ⟨i.1 - k, by omega⟩
        have e1 : (Fin.castSucc (⟨i.1 - k, by omega⟩ : Fin l)) =
            (⟨i.1 - k, by omega⟩ : Fin (l + 1)) := Fin.ext rfl
        have hval : i.1 - k + 1 = i.1 + 1 - k := by omega
        have e2 : ((⟨i.1 - k, by omega⟩ : Fin l).succ) =
            (⟨i.1 + 1 - k, by omega⟩ : Fin (l + 1)) := Fin.ext hval
        rw [e1, e2] at hst
        exact hst

@[simp] theorem append_vertex (P : RelPath E T k) (Q : RelPath E T l) (hl : 0 < l)
    (hjoin : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩)
    (i : Fin (k + l + 1)) :
    (P.append Q hl hjoin).vertex i =
      if h : i.1 ≤ k then P.vertex ⟨i.1, by omega⟩ else Q.vertex ⟨i.1 - k, by omega⟩ := rfl

@[simp] theorem append_vertex_le (P : RelPath E T k) (Q : RelPath E T l) (hl : 0 < l)
    (hjoin : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩)
    (i : Fin (k + l + 1)) (h : i.1 ≤ k) :
    (P.append Q hl hjoin).vertex i = P.vertex ⟨i.1, by omega⟩ := dif_pos h

@[simp] theorem append_vertex_last (P : RelPath E T k) (Q : RelPath E T l) (hl : 0 < l)
    (hjoin : P.vertex ⟨k, by omega⟩ = Q.vertex ⟨0, by omega⟩) :
    (P.append Q hl hjoin).vertex ⟨k + l, by omega⟩ = Q.vertex ⟨l, by omega⟩ := by
  rw [append_vertex, dif_neg (show ¬ k + l ≤ k by omega)]
  exact congrArg (fun t : Fin (l + 1) => Q.vertex t)
    (Fin.ext (Nat.add_sub_cancel_left k l))


end RelPath

end CRNT