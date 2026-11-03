import CRNT.Analysis.SpernerNBoundaryCell
import CRNT.Analysis.SpernerNIncidence
import CRNT.Analysis.SpernerNParity

/-!
# Boundary-facet ↔ (n-1)-cell correspondence for the Kuhn triangulation

Two layers. First, the last-coordinate geometry of a Kuhn cell's vertices: only the final simple root
`d_(last)` touches coordinate `n+1`, so the last coordinate steps down by one exactly when the
`d_(last)` direction has been taken; consequently a cell touches the boundary face `x_last = 0` only
when its base last-coordinate is `1` and the `d_(last)` step has been passed.

Second, for a cell `c` whose first Kuhn step is `d_(last)` (`c.perm 0 = Fin.last n`) and which touches
the face (`c.base (Fin.last (n+1)) = 1`), the facet dropping vertex `0` lies on the face. Projecting it
(dropping the last coordinate) yields a genuine `n`-cell `bcell c`, with permutation `bperm` and a
vertex correspondence `(bcell c).vertex k = (c.vertex k.succ)` projected. The `door_iff_rainbow`
correspondence then equates such a facet being a *door* with the projected cell being *rainbow* under
the restricted coloring — the geometric heart of the dimension recursion.

Depends on: `CRNT.Analysis.SpernerNBoundaryCell`,
`CRNT.Analysis.SpernerNIncidence`, `CRNT.Analysis.SpernerNParity`.
-/

namespace CRNT.Analysis.SpernerN

open Finset

variable {n N : ℕ}

/-- Only the last simple root touches the last coordinate: `root j (last) = -1` iff `j = last`. -/
theorem root_last (j : Fin (n + 1)) :
    root j (Fin.last (n + 1)) = if j = Fin.last n then -1 else 0 := by
  have h1 : (Fin.last (n + 1) : Fin (n + 2)) ≠ j.castSucc :=
    fun h => absurd h.symm (ne_of_lt (Fin.castSucc_lt_last j))
  have h2 : (Fin.last (n + 1) = j.succ) ↔ j = Fin.last n := by
    rw [eq_comm, ← Fin.succ_last, Fin.succ_inj]
  unfold root
  rw [if_neg h1]
  by_cases hj : j = Fin.last n
  · rw [if_pos (h2.mpr hj), if_pos hj]; ring
  · rw [if_neg (fun h => hj (h2.mp h)), if_neg hj]; ring

/-- The last-coordinate offset of the `k`-th vertex: it drops by one exactly once the `d_(last)`
direction (at permutation-position `σ⁻¹ (last n)`) has been taken. -/
theorem voff_last (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 2)) :
    voff σ k (Fin.last (n + 1))
      = if ((σ⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ) then -1 else 0 := by
  unfold voff
  rw [Finset.sum_congr rfl (fun l _ => root_last (σ l))]
  have key : ∀ l : Fin (n + 1), (σ l = Fin.last n) ↔ (l = σ⁻¹ (Fin.last n)) :=
    fun l => σ.apply_eq_iff_eq_symm_apply
  simp_rw [key]
  rw [Finset.sum_ite_eq' (Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ)))
    (σ⁻¹ (Fin.last n)) (fun _ => (-1 : ℤ))]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- The last coordinate of a cell vertex: `base_(last) + (−1 if the d_(last) step has been taken)`. -/
theorem vertex_last (c : Cell (n + 1) N) (k : Fin (n + 2)) :
    ((c.vertex k).1 (Fin.last (n + 1)) : ℤ)
      = (c.base (Fin.last (n + 1)) : ℤ)
        + if ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ) then -1 else 0 := by
  rw [c.vertex_val k (Fin.last (n + 1)), voff_last]

/-- **Every valid Kuhn cell has last base-coordinate `≥ 1`.** The `d_(last)` step (taken by the final
vertex) decrements the last coordinate, so a base coordinate of `0` would make that vertex negative.
Consequently no cell has its *base* on the face `x_last = 0`; cells only *touch* the face. -/
theorem base_last_pos (c : Cell (n + 1) N) : 1 ≤ c.base (Fin.last (n + 1)) := by
  have hv := c.valid (Fin.last (n + 1)) (Fin.last (n + 1))
  rw [voff_last] at hv
  have hp : ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < ((Fin.last (n + 1) : Fin (n + 2)) : ℕ) := by
    rw [Fin.val_last]; exact (c.perm⁻¹ (Fin.last n)).isLt
  rw [if_pos hp] at hv
  omega

/-- **A cell vertex lies on the boundary face `x_last = 0`** exactly when the cell touches the face
(`base_last = 1`) and the vertex comes after the `d_(last)` step. -/
theorem vertex_last_zero_iff (c : Cell (n + 1) N) (k : Fin (n + 2)) :
    (c.vertex k).1 (Fin.last (n + 1)) = 0
      ↔ (c.base (Fin.last (n + 1)) = 1
          ∧ ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ)) := by
  have hbpos := base_last_pos c
  have hval := vertex_last c k
  constructor
  · intro h0
    have hz : ((c.vertex k).1 (Fin.last (n + 1)) : ℤ) = 0 := by exact_mod_cast h0
    rw [hval] at hz
    by_cases hp : ((c.perm⁻¹ (Fin.last n) : Fin (n + 1)) : ℕ) < (k : ℕ)
    · rw [if_pos hp] at hz; exact ⟨by omega, hp⟩
    · rw [if_neg hp] at hz; omega
  · rintro ⟨hb, hp⟩
    have hz : ((c.vertex k).1 (Fin.last (n + 1)) : ℤ) = 0 := by rw [hval, if_pos hp, hb]; norm_num
    exact_mod_cast hz

/-! ### The boundary cell `bcell` and the door ↔ rainbow correspondence

For a cell `c : Cell (n+1) N` whose first Kuhn step is `d_(last)` (`hp0 : c.perm 0 = Fin.last n`) and
which touches the face (`hb : c.base (Fin.last (n+1)) = 1`), the facet dropping vertex `0` lies on the
boundary face `x_last = 0`. Projecting that facet (dropping the last coordinate via `boundaryEquiv`)
gives a genuine `n`-cell `bcell c`, whose permutation is `c.perm` with the position-`0` entry removed.
-/

/-- The non-position-0 permutation entries never equal `Fin.last n`. -/
theorem perm_succ_ne_last (c : Cell (n + 1) N) (hp0 : c.perm 0 = Fin.last n) (j : Fin n) :
    c.perm j.succ ≠ Fin.last n := fun h =>
  Fin.succ_ne_zero j (c.perm.injective (h.trans hp0.symm))

/-- The permutation of the boundary `n`-cell: `c.perm` with its position-`0` entry (which is
`Fin.last n`) removed, the remaining values cast down to `Fin n`. -/
noncomputable def bperm (c : Cell (n + 1) N) (hp0 : c.perm 0 = Fin.last n) : Equiv.Perm (Fin n) :=
  Equiv.ofBijective (fun j => (c.perm j.succ).castPred (perm_succ_ne_last c hp0 j))
    (Finite.injective_iff_bijective.mp (by
      intro a b h
      have h2 : c.perm a.succ = c.perm b.succ := by
        have := congrArg Fin.castSucc h
        rwa [Fin.castSucc_castPred, Fin.castSucc_castPred] at this
      exact Fin.succ_injective n (c.perm.injective h2)))

@[simp] theorem bperm_castSucc (c : Cell (n + 1) N) (hp0 : c.perm 0 = Fin.last n) (j : Fin n) :
    (bperm c hp0 j).castSucc = c.perm j.succ := by
  simp only [bperm, Equiv.ofBijective_apply]
  exact Fin.castSucc_castPred _ _

/-- **Root projection.** The `(n+1)`-dimensional simple root at a cast-down index, evaluated at a
cast-down coordinate, equals the `n`-dimensional simple root. -/
theorem root_castSucc (a : Fin n) (i : Fin (n + 1)) :
    root a.castSucc i.castSucc = root a i := by
  have hsc : (a.castSucc).succ = (a.succ).castSucc := by
    ext; simp [Fin.val_succ, Fin.val_castSucc]
  unfold root
  rw [hsc]
  simp only [Fin.castSucc_inj]

/-- The base of the boundary `n`-cell: the projected coordinates (dropping the last) of the cell's
vertex `1`, the first vertex on the boundary face. -/
def bcellBase (c : Cell (n + 1) N) : Fin (n + 1) → ℕ := fun i => (c.vertex 1).1 i.castSucc

/-- **Prefix-sum split.** The offset of vertex `k.succ` of `c` (at a projected coordinate) splits as
the first `d_(last)` step (which lands at vertex `1`) plus the offset of vertex `k` of the projected
cell `bcell`. -/
theorem voff_succ_split (c : Cell (n + 1) N) (hp0 : c.perm 0 = Fin.last n) (k i : Fin (n + 1)) :
    voff c.perm k.succ i.castSucc
      = voff c.perm (1 : Fin (n + 2)) i.castSucc + voff (bperm c hp0) k i := by
  have h1 : voff c.perm (1 : Fin (n + 2)) i.castSucc = root (c.perm 0) i.castSucc := by
    unfold voff
    have hfilter : Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < ((1 : Fin (n + 2)) : ℕ))
        = {(0 : Fin (n + 1))} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.val_one, Fin.ext_iff, Fin.val_zero]
      simp [Nat.lt_one_iff]
    rw [hfilter, Finset.sum_singleton]
  rw [h1]
  have hset : (Finset.univ.filter (fun l' : Fin (n + 1) => (l' : ℕ) < (k : ℕ) + 1)).erase 0
      = (Finset.univ.filter (fun m : Fin n => (m : ℕ) < (k : ℕ))).image Fin.succ := by
    ext l'
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · rintro ⟨hne, hlt⟩
      have hsp : (l'.pred hne).succ = l' := Fin.succ_pred l' hne
      have hv : (l'.pred hne).val + 1 = l'.val := by
        conv_rhs => rw [← hsp]
        rw [Fin.val_succ]
      exact ⟨l'.pred hne, by omega, hsp⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨Fin.succ_ne_zero m, by simp only [Fin.val_succ]; omega⟩
  unfold voff
  simp only [Fin.val_succ]
  have h0mem : (0 : Fin (n + 1)) ∈
      Finset.univ.filter (fun l' : Fin (n + 1) => (l' : ℕ) < (k : ℕ) + 1) := by simp
  rw [← Finset.add_sum_erase _ _ h0mem]
  congr 1
  rw [hset, Finset.sum_image (fun a _ b _ h => Fin.succ_injective n h)]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [← bperm_castSucc c hp0 m, root_castSucc]

/-- **The boundary-cell offset identity.** A vertex of the projected cell `bcell` (at any coordinate)
agrees with the corresponding vertex `k.succ` of `c` (at the cast-up coordinate). -/
theorem bcell_voff_eq (c : Cell (n + 1) N) (hp0 : c.perm 0 = Fin.last n) (k i : Fin (n + 1)) :
    (bcellBase c i : ℤ) + voff (bperm c hp0) k i = ((c.vertex k.succ).1 i.castSucc : ℤ) := by
  simp only [bcellBase]
  rw [Cell.vertex_val, Cell.vertex_val, voff_succ_split c hp0 k i]
  ring

/-- **The boundary `n`-cell.** For a cell `c` whose first Kuhn step is `d_(last)` and which touches
the face `x_last = 0`, dropping vertex `0` and projecting away the last coordinate yields a genuine
Kuhn `n`-cell. -/
noncomputable def bcell (c : Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) : Cell n N where
  base := bcellBase c
  perm := bperm c hp0
  sum_base := by
    have hsum : ∑ i : Fin (n + 2), (c.vertex (1 : Fin (n + 2))).1 i = N := (c.vertex 1).2
    rw [Fin.sum_univ_castSucc] at hsum
    have hzero : (c.vertex (1 : Fin (n + 2))).1 (Fin.last (n + 1)) = 0 := by
      rw [vertex_last_zero_iff]
      refine ⟨hb, ?_⟩
      have hinv : c.perm⁻¹ (Fin.last n) = 0 := by rw [← hp0]; simp
      rw [hinv]
      simp only [Fin.val_zero, Fin.val_one]
      omega
    rw [hzero, add_zero] at hsum
    simpa [bcellBase] using hsum
  valid := fun k i => by rw [bcell_voff_eq c hp0 k i]; exact Nat.cast_nonneg _

@[simp] theorem bcell_base (c : Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) : (bcell c hb hp0).base = bcellBase c := rfl

@[simp] theorem bcell_perm (c : Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) : (bcell c hb hp0).perm = bperm c hp0 := rfl

/-- **Vertex correspondence.** Vertex `k` of `bcell` is vertex `k.succ` of `c`, projected by dropping
the last coordinate. -/
theorem bcell_vertex (c : Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) (k i : Fin (n + 1)) :
    ((bcell c hb hp0).vertex k).1 i = (c.vertex k.succ).1 i.castSucc := by
  have h := (bcell c hb hp0).vertex_val k i
  rw [bcell_base, bcell_perm, bcell_voff_eq c hp0 k i] at h
  exact_mod_cast h

/-- **Color bridge for the boundary cell.** The restricted color of vertex `k` of `bcell`, recast up
by `castSucc`, is the original color of vertex `k.succ` of `c`. -/
theorem bcell_vertex_color (c : Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) (col : SpernerColoring (n + 1) N) (k : Fin (n + 1)) :
    ((restrictColoring col).color ((bcell c hb hp0).vertex k)).castSucc
      = col.color (c.vertex k.succ) := by
  have hface : (c.vertex k.succ).1 (Fin.last (n + 1)) = 0 := by
    rw [vertex_last_zero_iff]
    refine ⟨hb, ?_⟩
    have hinv : c.perm⁻¹ (Fin.last n) = 0 := by rw [← hp0]; simp
    rw [hinv]
    simp only [Fin.val_zero, Fin.val_succ]
    omega
  have hpt : (bcell c hb hp0).vertex k = boundaryEquiv n N ⟨c.vertex k.succ, hface⟩ := by
    ext i
    rw [bcell_vertex]
    rfl
  rw [hpt]
  exact restrictColoring_color_of_boundary col (c.vertex k.succ) hface

/-- **Door ↔ rainbow correspondence.** The facet of `c` dropping vertex `0` is a *door* (its colors
realize exactly the low colors `{0, …, n}`) precisely when the projected boundary cell `bcell` is
*rainbow* under the restricted coloring (its vertices receive every color bijectively). This is the
geometric heart of the dimension recursion: boundary doors of `(n+1)`-cells correspond to rainbow
`n`-cells on the face. -/
theorem door_iff_rainbow (c : Cell (n + 1) N) (hb : c.base (Fin.last (n + 1)) = 1)
    (hp0 : c.perm 0 = Fin.last n) (col : SpernerColoring (n + 1) N) :
    (facetVerts c 0).image col.color = lowColors (n + 1)
      ↔ Function.Bijective
          (fun k => (restrictColoring col).color ((bcell c hb hp0).vertex k)) := by
  set g : Fin (n + 1) → Fin (n + 1) :=
    fun k => (restrictColoring col).color ((bcell c hb hp0).vertex k) with hg
  have hbridge : ∀ k, (g k).castSucc = col.color (c.vertex k.succ) :=
    fun k => bcell_vertex_color c hb hp0 col k
  have herase : univ.erase (0 : Fin (n + 2)) = univ.image (Fin.succ : Fin (n + 1) → Fin (n + 2)) := by
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
    exact Fin.exists_succ_eq.symm
  have hfacet : (facetVerts c 0).image col.color = (univ.image g).image Fin.castSucc := by
    rw [facetVerts, Finset.image_image, herase, Finset.image_image, Finset.image_image]
    apply Finset.image_congr
    intro k _
    simp only [Function.comp_apply]
    exact (hbridge k).symm
  have hlow : lowColors (n + 1) = univ.image (Fin.castSucc : Fin (n + 1) → Fin (n + 2)) := by
    rw [lowColors_eq_erase]
    ext x
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_image, true_and]
    constructor
    · intro hx; exact ⟨x.castPred hx, Fin.castSucc_castPred x hx⟩
    · rintro ⟨y, rfl⟩; exact (Fin.castSucc_lt_last y).ne
  rw [hfacet, hlow, (Finset.image_injective (Fin.castSucc_injective _)).eq_iff]
  constructor
  · intro h
    refine Finite.surjective_iff_bijective.mp (fun y => ?_)
    have hy : y ∈ univ.image g := by rw [h]; exact Finset.mem_univ y
    obtain ⟨x, _, hx⟩ := Finset.mem_image.mp hy
    exact ⟨x, hx⟩
  · intro h
    rw [Finset.eq_univ_iff_forall]
    intro y
    obtain ⟨x, hx⟩ := h.surjective y
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩

end CRNT.Analysis.SpernerN
