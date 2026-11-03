import CRNT.Analysis.SpernerNInterior
import Mathlib.Data.ZMod.Basic

/-!
# Closing the n-dimensional Sperner lemma

The base-change *predecessor* (the inverse of `shiftCell`) and the door-incidence involution that
discharges `SpernerHandshake`, making `sperner_exists_rainbow` unconditional.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators
open Finset

variable {n N : ℕ}

/-! ### The predecessor permutation (the inverse rotation) -/

/-- The **predecessor permutation**: the right-rotation `σ' = σ ∘ (finRotate (n+1))⁻¹`, i.e.
`σ'(l) = σ(l-1)` (wrapping `σ(0) ↦ σ(last)`). -/
def predPerm (σ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 1)) :=
  σ * (finRotate (n + 1))⁻¹

theorem finRotate_inv_apply (l : Fin (n + 1)) : (finRotate (n + 1))⁻¹ l = l - 1 := by
  have : (finRotate (n + 1)) (l - 1) = l := by rw [finRotate_apply, sub_add_cancel]
  exact (Equiv.Perm.inv_eq_iff_eq).mpr this.symm

theorem predPerm_apply (σ : Equiv.Perm (Fin (n + 1))) (l : Fin (n + 1)) :
    predPerm σ l = σ (l - 1) := by
  simp only [predPerm, Equiv.Perm.mul_apply, finRotate_inv_apply]

/-- `0 - 1 = Fin.last n` in `Fin (n+1)`. -/
theorem zero_sub_one_eq_last : (0 : Fin (n + 1)) - 1 = Fin.last n := by
  apply Fin.ext
  rw [Fin.coe_sub_one, if_pos rfl, Fin.val_last]

/-- **Predecessor offset.** For `k ≠ 0` the predecessor offset is the original offset of the previous
vertex, plus the last root (the wrapped `σ(0) ↦ σ(last)` step). -/
theorem voff_predPerm_ne_zero (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 2))
    (hk : k ≠ 0) (i : Fin (n + 2)) :
    voff (predPerm σ) k i = root (σ (Fin.last n)) i + voff σ (k - 1) i := by
  have hkpos : 0 < (k : ℕ) := by
    rcases Nat.eq_zero_or_pos (k : ℕ) with h | h
    · exact absurd (Fin.ext h) hk
    · exact h
  have hkval : ((k - 1 : Fin (n + 2)) : ℕ) = (k : ℕ) - 1 := by
    rw [Fin.coe_sub_one, if_neg hk]
  have hL : voff (predPerm σ) k i
      = ∑ l ∈ univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ)), root (σ (l - 1)) i := by
    simp only [voff]
    exact Finset.sum_congr rfl (fun l _ => by rw [predPerm_apply])
  have hsplit : (univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ)))
      = insert (0 : Fin (n + 1))
          ((univ.filter (fun l' : Fin (n + 1) => (l' : ℕ) < ((k - 1 : Fin (n + 2)) : ℕ))).image (· + 1)) := by
    rw [hkval]
    ext l
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
    constructor
    · intro hl
      rcases Nat.eq_zero_or_pos (l : ℕ) with h0 | hpos
      · exact Or.inl (Fin.ext (by rw [h0, Fin.val_zero]))
      · refine Or.inr ⟨⟨(l : ℕ) - 1, by omega⟩, by simp only; omega, ?_⟩
        apply Fin.ext
        have hlne : (⟨(l : ℕ) - 1, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
          intro hc
          have hv : ((⟨(l : ℕ) - 1, by omega⟩ : Fin (n + 1)) : ℕ) = n := by rw [hc, Fin.val_last]
          simp only at hv; omega
        rw [Fin.val_add_one, if_neg hlne]
        simp only; omega
    · rintro (rfl | ⟨l', hl', rfl⟩)
      · simp only [Fin.val_zero]; omega
      · have hlne : l' ≠ Fin.last n := by
          intro hc; rw [hc, Fin.val_last] at hl'; omega
        rw [Fin.val_add_one, if_neg hlne]; omega
  have h0notin : (0 : Fin (n + 1))
      ∉ (univ.filter (fun l' : Fin (n + 1) => (l' : ℕ) < ((k - 1 : Fin (n + 2)) : ℕ))).image (· + 1) := by
    simp only [mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
    intro l' hl' hc
    rw [hkval] at hl'
    have hlne : l' ≠ Fin.last n := by
      intro h; rw [h, Fin.val_last] at hl'; omega
    have h1 : ((l' + 1 : Fin (n + 1)) : ℕ) = (l' : ℕ) + 1 := by rw [Fin.val_add_one, if_neg hlne]
    have h2 : ((l' + 1 : Fin (n + 1)) : ℕ) = 0 := by rw [hc, Fin.val_zero]
    omega
  rw [hL, hsplit, Finset.sum_insert h0notin, zero_sub_one_eq_last]
  congr 1
  rw [Finset.sum_image (fun a _ b _ h => add_one_injective h)]
  simp only [voff]
  refine Finset.sum_congr rfl (fun l' hl' => ?_)
  rw [mem_filter] at hl'
  have hlne : l' ≠ Fin.last n := by
    intro hc; rw [hc, Fin.val_last] at hl'; omega
  rw [add_sub_cancel_right]

/-! ### The predecessor cell -/

/-- **Down-validity (the predecessor interior condition).** The base-change predecessor across the
*last* facet exists when the coordinate decremented by the down-step (`(σ last).castSucc`) is positive
in the base. -/
def DownValid (c : Cell (n + 1) N) : Prop :=
  1 ≤ c.base ((c.perm (Fin.last n)).castSucc)

instance (c : Cell (n + 1) N) : Decidable (DownValid c) := by unfold DownValid; infer_instance

/-- The base of the predecessor: `c.base − root (σ last)`, i.e. decrement coordinate
`(σ last).castSucc` and increment `(σ last).succ`. -/
def predBase (c : Cell (n + 1) N) (i : Fin (n + 2)) : ℕ :=
  c.base i + (if i = (c.perm (Fin.last n)).succ then 1 else 0)
    - (if i = (c.perm (Fin.last n)).castSucc then 1 else 0)

/-- Under down-validity the predecessor base casts to `c.base − root (σ last)` without truncation. -/
theorem predBase_cast (c : Cell (n + 1) N) (h : DownValid c) (i : Fin (n + 2)) :
    ((predBase c i : ℕ) : ℤ) = (c.base i : ℤ) - root (c.perm (Fin.last n)) i := by
  have hcs_ne_succ : (c.perm (Fin.last n)).castSucc ≠ (c.perm (Fin.last n)).succ := by
    intro hh
    have hv : ((c.perm (Fin.last n)).castSucc : ℕ) = ((c.perm (Fin.last n)).succ : ℕ) :=
      congrArg Fin.val hh
    simp only [Fin.val_succ, Fin.val_castSucc] at hv; omega
  rcases eq_or_ne i (c.perm (Fin.last n)).castSucc with hcs | hcs
  · have hsucc : i ≠ (c.perm (Fin.last n)).succ := by
      intro h2; exact hcs_ne_succ (by rw [← hcs]; exact h2)
    have hge : 1 ≤ c.base i := by rw [hcs]; exact h
    simp only [predBase, root, if_pos hcs, if_neg hsucc]; omega
  · rcases eq_or_ne i (c.perm (Fin.last n)).succ with hsucc | hsucc
    · simp only [predBase, root, if_pos hsucc, if_neg hcs]; omega
    · simp only [predBase, root, if_neg hsucc, if_neg hcs]; omega

/-- **The base-change predecessor** of `c` across the *last* facet: the cell whose `shiftCell` is `c`.
Permutation `σ ∘ (finRotate)⁻¹` (right-rotation) and base `c.base − root (σ last)`. -/
def predCell (c : Cell (n + 1) N) (h : DownValid c) : Cell (n + 1) N where
  base := predBase c
  perm := predPerm c.perm
  sum_base := by
    have key : ((∑ i, predBase c i : ℕ) : ℤ) = (N : ℤ) := by
      rw [Nat.cast_sum, Finset.sum_congr rfl (fun i _ => predBase_cast c h i),
        Finset.sum_sub_distrib]
      have hb : ∑ i : Fin (n + 2), (c.base i : ℤ) = (N : ℤ) := by rw [← Nat.cast_sum, c.sum_base]
      have hr : ∑ i : Fin (n + 2), root (c.perm (Fin.last n)) i = 0 := root_sum _
      rw [hb, hr]; ring
    exact_mod_cast key
  valid := by
    intro k i
    by_cases hk : k = 0
    · subst hk
      have hz : voff (predPerm c.perm) 0 i = 0 := by
        simp only [voff]
        apply Finset.sum_eq_zero
        intro l hl
        simp only [mem_filter, mem_univ, true_and, Fin.val_zero] at hl
        exfalso
        have hl' : (l : ℕ) < 0 := by simpa using hl
        exact Nat.not_lt_zero (l : ℕ) hl'
      rw [hz, add_zero]
      exact_mod_cast Nat.zero_le (predBase c i)
    · rw [voff_predPerm_ne_zero c.perm k hk i, predBase_cast c h i]
      have hval : (0 : ℤ) ≤ (c.base i : ℤ) + voff c.perm (k - 1) i := c.valid (k - 1) i
      have heq : (c.base i : ℤ) - root (c.perm (Fin.last n)) i
            + (root (c.perm (Fin.last n)) i + voff c.perm (k - 1) i)
          = (c.base i : ℤ) + voff c.perm (k - 1) i := by ring
      rw [heq]; exact hval

@[simp] theorem predCell_base (c : Cell (n + 1) N) (h : DownValid c) :
    (predCell c h).base = predBase c := rfl
@[simp] theorem predCell_perm (c : Cell (n + 1) N) (h : DownValid c) :
    (predCell c h).perm = predPerm c.perm := rfl

/-- `voff` at vertex `0` is zero. -/
theorem voff_zero (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2)) : voff σ 0 i = 0 := by
  simp only [voff]
  apply Finset.sum_eq_zero
  intro l hl
  simp only [mem_filter, mem_univ, true_and, Fin.val_zero] at hl
  exfalso
  have hl' : (l : ℕ) < 0 := by simpa using hl
  exact Nat.not_lt_zero (l : ℕ) hl'

/-- **Vertex `1` of the predecessor recovers `c.base`.** -/
theorem predCell_vertex_one (c : Cell (n + 1) N) (h : DownValid c) (i : Fin (n + 2)) :
    ((predCell c h).vertex 1).1 i = c.base i := by
  have hcast : (((predCell c h).vertex 1).1 i : ℤ) = (c.base i : ℤ) := by
    rw [Cell.vertex_val, predCell_base, predCell_perm,
      voff_predPerm_ne_zero c.perm 1 one_ne_zero i, predBase_cast c h i]
    have hz : voff c.perm (1 - 1 : Fin (n + 2)) i = 0 := by rw [sub_self]; exact voff_zero c.perm i
    rw [hz]; ring
  exact_mod_cast hcast

/-- **The predecessor is shift-valid** (its `shiftCell` reconstructs `c`, whose last vertex is in the
orthant). -/
theorem shiftValid_predCell (c : Cell (n + 1) N) (h : DownValid c) : ShiftValid (predCell c h) := by
  intro i
  rw [show (((predCell c h).vertex 1).1 i : ℤ) = (c.base i : ℤ) from by
    rw [predCell_vertex_one c h i]]
  have hsr : ((if i = 0 then (1 : ℤ) else 0) - (if i = Fin.last (n + 1) then 1 else 0))
      = voff c.perm (Fin.last (n + 1)) i := by rw [voff_last_eq_sum_root, sum_root]
  rw [hsr]
  exact c.valid (Fin.last (n + 1)) i

/-- The shift permutation undoes the predecessor permutation. -/
theorem shiftPerm_predPerm (σ : Equiv.Perm (Fin (n + 1))) : shiftPerm (predPerm σ) = σ := by
  rw [shiftPerm, predPerm, mul_assoc, inv_mul_cancel, mul_one]

/-- **The shift cell undoes the predecessor: `shiftCell (predCell c) = c`.** -/
theorem shiftCell_predCell (c : Cell (n + 1) N) (h : DownValid c) :
    shiftCell (predCell c h) (shiftValid_predCell c h) = c := by
  apply Cell.eq_of_base_perm
  · funext i
    show ((predCell c h).vertex 1).1 i = c.base i
    exact predCell_vertex_one c h i
  · show shiftPerm (predPerm c.perm) = c.perm
    exact shiftPerm_predPerm c.perm

/-- `shiftPerm σ` sends the last position to `σ 0` (the wrapped step). -/
theorem shiftPerm_last (σ : Equiv.Perm (Fin (n + 1))) : shiftPerm σ (Fin.last n) = σ 0 := by
  rw [shiftPerm_apply]
  congr 1
  apply Fin.ext
  rw [Fin.val_add_one, if_pos rfl, Fin.val_zero]

/-- The shift of a cell is down valid (its predecessor is `c` itself). -/
theorem downValid_shiftCell (c : Cell (n + 1) N) (hsv : ShiftValid c) :
    DownValid (shiftCell c hsv) := by
  show 1 ≤ (shiftCell c hsv).base (((shiftCell c hsv).perm (Fin.last n)).castSucc)
  have hperm : (shiftCell c hsv).perm (Fin.last n) = c.perm 0 := shiftPerm_last c.perm
  rw [hperm]
  show 1 ≤ (c.vertex 1).1 ((c.perm 0).castSucc)
  have hne : ((c.perm 0).castSucc) ≠ ((c.perm 0).succ) := by
    intro hh
    have hv2 : ((c.perm 0).castSucc : ℕ) = ((c.perm 0).succ : ℕ) := congrArg Fin.val hh
    simp only [Fin.val_succ, Fin.val_castSucc] at hv2; omega
  have hroot : root (c.perm 0) ((c.perm 0).castSucc) = 1 := by
    rw [root, if_pos rfl, if_neg hne]; ring
  have hc : ((c.vertex 1).1 ((c.perm 0).castSucc) : ℤ) = (c.base ((c.perm 0).castSucc) : ℤ) + 1 := by
    rw [Cell.vertex_val, voff_one, hroot]
  have h2 : (1 : ℤ) ≤ ((c.vertex 1).1 ((c.perm 0).castSucc) : ℤ) := by
    rw [hc]; have := Int.natCast_nonneg (c.base ((c.perm 0).castSucc)); omega
  exact_mod_cast h2

/-- **The predecessor undoes the shift: `predCell (shiftCell c) = c`.** -/
theorem predCell_shiftCell (c : Cell (n + 1) N) (hsv : ShiftValid c) :
    predCell (shiftCell c hsv) (downValid_shiftCell c hsv) = c := by
  apply Cell.eq_of_base_perm
  · funext i
    show predBase (shiftCell c hsv) i = c.base i
    have hcast : ((predBase (shiftCell c hsv) i : ℕ) : ℤ) = (c.base i : ℤ) := by
      rw [predBase_cast (shiftCell c hsv) (downValid_shiftCell c hsv) i]
      show ((c.vertex 1).1 i : ℤ) - root (shiftPerm c.perm (Fin.last n)) i = c.base i
      rw [shiftPerm_last, Cell.vertex_val, voff_one]; ring
    exact_mod_cast hcast
  · show predPerm (shiftPerm c.perm) = c.perm
    rw [predPerm, shiftPerm, mul_assoc, mul_inv_cancel, mul_one]

/-- `shiftCell` is injective. -/
theorem shiftCell_injective {c c' : Cell (n + 1) N} (h : ShiftValid c) (h' : ShiftValid c')
    (heq : shiftCell c h = shiftCell c' h') : c = c' := by
  have hp : shiftPerm c.perm = shiftPerm c'.perm := congrArg Cell.perm heq
  rw [shiftPerm, shiftPerm] at hp
  have hperm : c.perm = c'.perm := mul_right_cancel hp
  have hb : (c.vertex 1).1 = (c'.vertex 1).1 := congrArg Cell.base heq
  apply Cell.eq_of_base_perm _ hperm
  funext i
  have h1 := congrFun hb i
  have e1 : ((c.vertex 1).1 i : ℤ) = (c.base i : ℤ) + root (c.perm 0) i := by
    rw [Cell.vertex_val, voff_one]
  have e2 : ((c'.vertex 1).1 i : ℤ) = (c'.base i : ℤ) + root (c'.perm 0) i := by
    rw [Cell.vertex_val, voff_one]
  rw [hperm] at e1
  have hc : (c.base i : ℤ) = (c'.base i : ℤ) := by
    have : ((c.vertex 1).1 i : ℤ) = ((c'.vertex 1).1 i : ℤ) := by rw [h1]
    rw [e1, e2] at this; linarith
  exact_mod_cast hc

/-! ### G2 — the last door facet has a predecessor -/

/-- **G2 — last door facets are down valid.** A door incidence `(c, last)` always satisfies
`DownValid`: were the decremented base coordinate `a := (σ last).castSucc` zero, coordinate `a` would
vanish on the entire door facet (its `voff` contributions are all `≤ 0` away from the top vertex),
placing the facet on `{x_a = 0}` with `a ≠ last`, contradicting `door_face_eq_last`. -/
theorem downValid_of_doorFacet (col : SpernerColoring (n + 1) N) (c : Cell (n + 1) N)
    (hdoor : IsDoorFacet col c (Fin.last (n + 1))) :
    DownValid c := by
  classical
  set σ := c.perm with hσ
  set a : Fin (n + 2) := (σ (Fin.last n)).castSucc with hadef
  have ha_val : (a : ℕ) = (σ (Fin.last n) : ℕ) := by rw [hadef, Fin.val_castSucc]
  have ha_le : (a : ℕ) ≤ n := by rw [ha_val]; exact Nat.lt_succ_iff.mp (σ (Fin.last n)).isLt
  have ha_ne_last : a ≠ Fin.last (n + 1) := by
    intro h
    have hv : (a : ℕ) = n + 1 := by rw [h, Fin.val_last]
    omega
  by_contra hnv
  have hnv' : ¬ 1 ≤ c.base a := hnv
  have hba0 : c.base a = 0 := by omega
  -- coordinate `a` vanishes on every facet vertex
  have hface : ∀ p ∈ facetVerts c (Fin.last (n + 1)), p.1 a = 0 := by
    intro p hp
    rw [facetVerts, Finset.mem_image] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    rw [Finset.mem_erase] at hk
    have hkne : k ≠ Fin.last (n + 1) := hk.1
    have hkle : (k : ℕ) ≤ n := by
      have := k.isLt
      have hkv : (k : ℕ) ≠ n + 1 := fun hc => hkne (Fin.ext (by rw [Fin.val_last]; exact hc))
      omega
    -- each prefix root contribution to coordinate `a` is `≤ 0`
    have hterm : ∀ l ∈ univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ)),
        root (σ l) a ≤ 0 := by
      intro l hl
      rw [mem_filter] at hl
      have hlv : (l : ℕ) < n := by omega
      have hcs : ¬ a = (σ l).castSucc := by
        intro hc
        have hvv : (σ l : ℕ) = (a : ℕ) := by rw [hc, Fin.val_castSucc]
        rw [ha_val] at hvv
        have : l = Fin.last n := σ.injective (Fin.ext hvv)
        rw [this, Fin.val_last] at hlv; omega
      rw [root, if_neg hcs]
      split_ifs <;> omega
    have hvoff_le : voff σ k a ≤ 0 := by
      rw [voff]; exact Finset.sum_nonpos hterm
    have hcast : ((c.vertex k).1 a : ℤ) = voff σ k a := by
      rw [Cell.vertex_val, hba0]; push_cast; ring
    have hnn : (0 : ℤ) ≤ ((c.vertex k).1 a : ℤ) := Int.natCast_nonneg _
    have hz : ((c.vertex k).1 a : ℤ) = 0 := le_antisymm (hcast ▸ hvoff_le) hnn
    exact_mod_cast hz
  exact ha_ne_last (door_face_eq_last c (Fin.last (n + 1)) col a hdoor hface)

/-! ### Door preservation under the neighbour maps -/

variable {col : SpernerColoring (n + 1) N}

theorem isDoorFacet_flipCell {c : Cell (n + 1) N} {m : Fin (n + 2)} {h0 hn}
    {hv : ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m h0 hn) m i}
    (hd : IsDoorFacet col c m) : IsDoorFacet col (flipCell c m h0 hn hv) m := by
  unfold IsDoorFacet at *; rw [flipCell_facet]; exact hd

theorem isDoorFacet_shiftCell {c : Cell (n + 1) N} (h : ShiftValid c)
    (hd : IsDoorFacet col c 0) : IsDoorFacet col (shiftCell c h) (Fin.last (n + 1)) := by
  unfold IsDoorFacet at *; rw [shiftCell_facet]; exact hd

theorem isDoorFacet_predCell {c : Cell (n + 1) N} (h : DownValid c)
    (hd : IsDoorFacet col c (Fin.last (n + 1))) : IsDoorFacet col (predCell c h) 0 := by
  unfold IsDoorFacet at *
  rw [show facetVerts (predCell c h) 0 = facetVerts c (Fin.last (n + 1)) from by
    rw [← shiftCell_facet (predCell c h) (shiftValid_predCell c h), shiftCell_predCell]]
  exact hd

/-- The flip at a fixed index is an involution. -/
theorem flipCell_flipCell (c : Cell (n + 1) N) (m : Fin (n + 2)) (h0 : 0 < (m : ℕ))
    (hn : (m : ℕ) < n + 1)
    (hv : ∀ i, 0 ≤ (c.base i : ℤ) + voff (flipPerm c.perm m h0 hn) m i)
    (hv2 : ∀ i, 0 ≤ ((flipCell c m h0 hn hv).base i : ℤ)
      + voff (flipPerm (flipCell c m h0 hn hv).perm m h0 hn) m i) :
    flipCell (flipCell c m h0 hn hv) m h0 hn hv2 = c := by
  refine Cell.eq_of_base_perm ?_ ?_
  · rfl
  · show flipPerm (flipPerm c.perm m h0 hn) m h0 hn = c.perm
    rw [flipPerm, flipPerm, mul_assoc, Equiv.swap_mul_self, mul_one]

/-! ### The door-incidence count modulo two -/

open scoped Classical in
/-- The door incidences dropping a *middle* vertex (`0 < m < n+1`). -/
noncomputable def midIncidences (col : SpernerColoring (n + 1) N) :
    Finset (Cell (n + 1) N × Fin (n + 2)) :=
  (doorIncidences col).filter (fun p => 0 < (p.2 : ℕ) ∧ (p.2 : ℕ) < n + 1)

open scoped Classical in
/-- The door incidences dropping vertex `0` with a valid shift. -/
noncomputable def shiftZeroIncidences (col : SpernerColoring (n + 1) N) :
    Finset (Cell (n + 1) N × Fin (n + 2)) :=
  (doorIncidences col).filter (fun p => p.2 = 0 ∧ ShiftValid p.1)

open scoped Classical in
/-- The door incidences dropping the *last* vertex. -/
noncomputable def lastIncidences (col : SpernerColoring (n + 1) N) :
    Finset (Cell (n + 1) N × Fin (n + 2)) :=
  (doorIncidences col).filter (fun p => p.2 = Fin.last (n + 1))

theorem mem_doorIncidences {col : SpernerColoring (n + 1) N}
    {p : Cell (n + 1) N × Fin (n + 2)} :
    p ∈ doorIncidences col ↔ IsDoorFacet col p.1 p.2 := by
  rw [doorIncidences, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem mem_midIncidences {col : SpernerColoring (n + 1) N}
    {p : Cell (n + 1) N × Fin (n + 2)} :
    p ∈ midIncidences col ↔ IsDoorFacet col p.1 p.2 ∧ 0 < (p.2 : ℕ) ∧ (p.2 : ℕ) < n + 1 := by
  rw [midIncidences, Finset.mem_filter, mem_doorIncidences]

/-- **Middle door incidences are even in number** (paired by the flip). -/
theorem even_midIncidences_card (col : SpernerColoring (n + 1) N) :
    Even (midIncidences col).card := by
  classical
  have hsum : ∑ _p ∈ midIncidences col, (1 : ZMod 2) = 0 := by
    refine Finset.sum_involution
      (fun a ha => (flipCell a.1 a.2 (mem_midIncidences.mp ha).2.1 (mem_midIncidences.mp ha).2.2
        (flipValid_of_doorFacet col a.1 a.2 (mem_midIncidences.mp ha).2.1
          (mem_midIncidences.mp ha).2.2 (mem_midIncidences.mp ha).1), a.2))
      (fun a ha => by decide)
      (fun a ha _ => by
        intro hc
        exact flipCell_ne a.1 a.2 (mem_midIncidences.mp ha).2.1 (mem_midIncidences.mp ha).2.2
          (flipValid_of_doorFacet col a.1 a.2 (mem_midIncidences.mp ha).2.1
            (mem_midIncidences.mp ha).2.2 (mem_midIncidences.mp ha).1) (congrArg Prod.fst hc))
      (fun a ha => by
        have H0 := (mem_midIncidences.mp ha).2.1
        have HN := (mem_midIncidences.mp ha).2.2
        have HV := flipValid_of_doorFacet col a.1 a.2 H0 HN (mem_midIncidences.mp ha).1
        rw [mem_midIncidences]
        exact ⟨@isDoorFacet_flipCell n N col a.1 a.2 H0 HN HV (mem_midIncidences.mp ha).1,
          H0, HN⟩)
      (fun a ha => by
        have H0 := (mem_midIncidences.mp ha).2.1
        have HN := (mem_midIncidences.mp ha).2.2
        have HV := flipValid_of_doorFacet col a.1 a.2 H0 HN (mem_midIncidences.mp ha).1
        have HV2 := flipValid_of_doorFacet col (flipCell a.1 a.2 H0 HN HV) a.2 H0 HN
          (isDoorFacet_flipCell (mem_midIncidences.mp ha).1)
        refine Prod.ext ?_ ?_
        · exact flipCell_flipCell a.1 a.2 H0 HN HV HV2
        · rfl)
  have hcard : ((midIncidences col).card : ZMod 2) = 0 := by
    rw [← hsum, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact ZMod.natCast_eq_zero_iff_even.mp hcard

theorem mem_shiftZeroIncidences {col : SpernerColoring (n + 1) N}
    {p : Cell (n + 1) N × Fin (n + 2)} :
    p ∈ shiftZeroIncidences col ↔ IsDoorFacet col p.1 p.2 ∧ p.2 = 0 ∧ ShiftValid p.1 := by
  classical
  rw [shiftZeroIncidences, Finset.mem_filter, mem_doorIncidences]

theorem mem_lastIncidences {col : SpernerColoring (n + 1) N}
    {p : Cell (n + 1) N × Fin (n + 2)} :
    p ∈ lastIncidences col ↔ IsDoorFacet col p.1 p.2 ∧ p.2 = Fin.last (n + 1) := by
  rw [lastIncidences, Finset.mem_filter, mem_doorIncidences]

/-- **The last door incidences biject with the shift-valid zero door incidences** (via the
predecessor/shift inverse pair). -/
theorem card_lastIncidences_eq_shiftZero (col : SpernerColoring (n + 1) N) :
    (lastIncidences col).card = (shiftZeroIncidences col).card := by
  classical
  refine Finset.card_bij'
    (fun a ha => (predCell a.1 (downValid_of_doorFacet col a.1
      ((mem_lastIncidences.mp ha).2 ▸ (mem_lastIncidences.mp ha).1)), (0 : Fin (n + 2))))
    (fun b hb => (shiftCell b.1 (mem_shiftZeroIncidences.mp hb).2.2, Fin.last (n + 1)))
    ?_ ?_ ?_ ?_
  · intro a ha
    have hdl : IsDoorFacet col a.1 (Fin.last (n + 1)) :=
      (mem_lastIncidences.mp ha).2 ▸ (mem_lastIncidences.mp ha).1
    have dv : DownValid a.1 := downValid_of_doorFacet col a.1 hdl
    rw [mem_shiftZeroIncidences]
    exact ⟨isDoorFacet_predCell dv hdl, rfl, shiftValid_predCell a.1 dv⟩
  · intro b hb
    have hd0 : IsDoorFacet col b.1 0 := (mem_shiftZeroIncidences.mp hb).2.1 ▸
      (mem_shiftZeroIncidences.mp hb).1
    have sv : ShiftValid b.1 := (mem_shiftZeroIncidences.mp hb).2.2
    rw [mem_lastIncidences]
    exact ⟨isDoorFacet_shiftCell sv hd0, rfl⟩
  · intro a ha
    have hdl : IsDoorFacet col a.1 (Fin.last (n + 1)) :=
      (mem_lastIncidences.mp ha).2 ▸ (mem_lastIncidences.mp ha).1
    have dv : DownValid a.1 := downValid_of_doorFacet col a.1 hdl
    refine Prod.ext ?_ ?_
    · exact shiftCell_predCell a.1 dv
    · exact ((mem_lastIncidences.mp ha).2).symm
  · intro b hb
    have sv : ShiftValid b.1 := (mem_shiftZeroIncidences.mp hb).2.2
    refine Prod.ext ?_ ?_
    · exact predCell_shiftCell b.1 sv
    · exact ((mem_shiftZeroIncidences.mp hb).2.1).symm

open scoped Classical in
/-- **The boundary-door zero incidences biject with the boundary door cells.** -/
theorem card_zeroBoundary_eq_boundary (col : SpernerColoring (n + 1) N) :
    ((doorIncidences col).filter (fun p => p.2 = 0 ∧ ¬ ShiftValid p.1)).card
      = (univ.filter (isBoundaryDoorCell col)).card := by
  classical
  refine Finset.card_bij' (fun p _ => p.1) (fun c _ => (c, (0 : Fin (n + 2)))) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_filter] at hp
    obtain ⟨hdi, hz, hnsv⟩ := hp
    have hdoor : IsDoorFacet col p.1 p.2 := mem_doorIncidences.mp hdi
    have hbp := (not_shiftValid_iff p.1).mp hnsv
    rw [Finset.mem_filter, isBoundaryDoorCell]
    exact ⟨mem_univ _, hbp.1, hbp.2, hz ▸ hdoor⟩
  · intro c hc
    rw [Finset.mem_filter] at hc
    have hb : isBoundaryDoorCell col c := hc.2
    rw [isBoundaryDoorCell] at hb
    rw [Finset.mem_filter]
    refine ⟨?_, rfl, ?_⟩
    · rw [mem_doorIncidences]; exact hb.2.2
    · rw [not_shiftValid_iff]; exact ⟨hb.1, hb.2.1⟩
  · intro p hp
    rw [Finset.mem_filter] at hp
    exact Prod.ext rfl hp.2.1.symm
  · intro c _
    rfl

/-- **The three facet regions (by dropped index) partition the door incidences.** -/
theorem card_partition3 (col : SpernerColoring (n + 1) N) :
    (lastIncidences col).card + (midIncidences col).card
        + ((doorIncidences col).filter (fun p => p.2 = 0)).card
      = (doorIncidences col).card := by
  classical
  rw [lastIncidences, midIncidences, Finset.card_filter, Finset.card_filter, Finset.card_filter,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, Finset.card_eq_sum_ones]
  apply Finset.sum_congr rfl
  intro p _
  have hlt := p.2.isLt
  simp only [Fin.ext_iff, Fin.val_last, Fin.val_zero]
  split_ifs <;> omega

open scoped Classical in
/-- **The zero door incidences split by shift-validity into the shift-valid ones and the boundary
ones.** -/
theorem card_zero_split (col : SpernerColoring (n + 1) N) :
    ((doorIncidences col).filter (fun p => p.2 = 0)).card
      = (shiftZeroIncidences col).card
        + ((doorIncidences col).filter (fun p => p.2 = 0 ∧ ¬ ShiftValid p.1)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not
    (s := (doorIncidences col).filter (fun p => p.2 = 0)) (p := fun p => ShiftValid p.1)
  rw [show ((doorIncidences col).filter (fun p => p.2 = 0)).filter (fun p => ShiftValid p.1)
        = shiftZeroIncidences col from by rw [shiftZeroIncidences, Finset.filter_filter],
    show ((doorIncidences col).filter (fun p => p.2 = 0)).filter (fun p => ¬ ShiftValid p.1)
        = (doorIncidences col).filter (fun p => p.2 = 0 ∧ ¬ ShiftValid p.1) from by
      rw [Finset.filter_filter]] at h
  omega

open scoped Classical in
/-- **The door-incidence count has boundary parity.** -/
theorem doorIncidences_card_mod_two_eq_boundary (col : SpernerColoring (n + 1) N) :
    (doorIncidences col).card % 2 = (univ.filter (isBoundaryDoorCell col)).card % 2 := by
  classical
  have hpart := card_partition3 col
  have hzero := card_zero_split col
  have hlast := card_lastIncidences_eq_shiftZero col
  have hbdry := card_zeroBoundary_eq_boundary col
  obtain ⟨k, hk⟩ := even_midIncidences_card col
  omega

open scoped Classical in
/-- **The Sperner handshake.** The rainbow cells and the boundary door cells have equal parity. -/
theorem sperner_handshake (col : SpernerColoring (n + 1) N) (_hN : 0 < N) :
    Odd #{c : Cell (n + 1) N | IsRainbowCell col c}
      ↔ Odd #{c : Cell (n + 1) N | isBoundaryDoorCell col c} := by
  rw [Nat.odd_iff, Nat.odd_iff, ← card_doorIncidences_mod_two col,
    doorIncidences_card_mod_two_eq_boundary col]

/-- **The handshake holds in every dimension.** -/
theorem sperner_handshake_holds {N : ℕ} : SpernerHandshake (N := N) :=
  fun {_m} col hN => sperner_handshake col hN

/-- **The n-dimensional Sperner lemma (counted form).** Every Sperner coloring of the `n`-simplex has
an odd number of rainbow cells. -/
theorem sperner_odd_rainbow {m N : ℕ} (col : SpernerColoring m N) (hN : 0 < N) :
    Odd #{c : Cell m N | IsRainbowCell col c} :=
  sperner_odd_rainbow_of_handshake (fun {_N} => sperner_handshake_holds) col hN

/-- **The n-dimensional Sperner lemma.** Every Sperner coloring of the `n`-simplex has a rainbow
cell — one whose `n+1` vertices realize all `n+1` colors. -/
theorem sperner_exists_rainbow {m N : ℕ} (col : SpernerColoring m N) (hN : 0 < N) :
    ∃ c : Cell m N, IsRainbowCell col c :=
  sperner_exists_rainbow_of_handshake (fun {_N} => sperner_handshake_holds) col hN

end CRNT.Analysis.SpernerN
