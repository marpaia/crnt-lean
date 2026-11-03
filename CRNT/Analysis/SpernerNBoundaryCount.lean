import CRNT.Analysis.SpernerNBoundaryCorr
import CRNT.Analysis.SpernerNSperner

/-!
# Boundary doors count = rainbow `n`-cells count

The final combinatorial ingredient of the dimension recursion. The map `bcell`, which sends an
`(n+1)`-cell `c` touching the face `x_last = 0` with first Kuhn step `d_(last)` to its projected
`n`-cell on the face, is a **bijection** between the boundary `(n+1)`-cells (those satisfying
`c.base (Fin.last (n+1)) = 1 ∧ c.perm 0 = Fin.last n`) and *all* `n`-cells. Its inverse is the
explicit lift `lift d`, which prepends the `d_(last)` step (permutation `0 ↦ Fin.last n`,
`j.succ ↦ (d.perm j).castSucc`) and reconstructs the base.

Composing the bijection with `door_iff_rainbow` — which equates the projected facet being a *door*
with the lifted cell being *rainbow* — yields the count identity

`#{boundary door cells of col} = #{rainbow n-cells of (restrictColoring col)}`,

the bridge that feeds the inductive hypothesis into the handshaking step.

Depends on: `CRNT.Analysis.SpernerNBoundaryCorr`, `CRNT.Analysis.SpernerNSperner`.
-/

namespace CRNT.Analysis.SpernerN

open Finset Function

variable {n N : ℕ}

/-! ### The lifted permutation -/

/-- The permutation of `Fin (n+1)` that prepends the `d_(last)` Kuhn step: it sends position `0` to
`Fin.last n` and `j.succ` to `(σ j).castSucc`. This is the permutation of the unique `(n+1)`-cell
whose projected face cell has permutation `σ`. -/
noncomputable def liftPerm (σ : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.ofBijective (Fin.cons (Fin.last n) (fun j => (σ j).castSucc))
    (Finite.injective_iff_bijective.mp (by
      intro a b h
      induction a using Fin.cases with
      | zero =>
        induction b using Fin.cases with
        | zero => rfl
        | succ b' =>
          rw [Fin.cons_zero, Fin.cons_succ] at h
          exact absurd h.symm (Fin.castSucc_lt_last (σ b')).ne
      | succ a' =>
        induction b using Fin.cases with
        | zero =>
          rw [Fin.cons_zero, Fin.cons_succ] at h
          exact absurd h (Fin.castSucc_lt_last (σ a')).ne
        | succ b' =>
          rw [Fin.cons_succ, Fin.cons_succ] at h
          rw [σ.injective (Fin.castSucc_injective n h)]))

@[simp] theorem liftPerm_zero (σ : Equiv.Perm (Fin n)) : liftPerm σ 0 = Fin.last n := by
  simp only [liftPerm, Equiv.ofBijective_apply, Fin.cons_zero]

@[simp] theorem liftPerm_succ (σ : Equiv.Perm (Fin n)) (j : Fin n) :
    liftPerm σ j.succ = (σ j).castSucc := by
  simp only [liftPerm, Equiv.ofBijective_apply, Fin.cons_succ]

/-! ### Root projections -/

/-- The `(n+1)`-dim simple root at `Fin.last n`, evaluated at a cast-up coordinate, is `1` exactly
at the top projected coordinate. -/
theorem root_last_castSucc (j : Fin (n + 1)) :
    root (Fin.last n) j.castSucc = if j = Fin.last n then 1 else 0 := by
  unfold root
  have e1 : (j.castSucc = (Fin.last n).castSucc) ↔ (j = Fin.last n) := Fin.castSucc_inj
  have e2 : ¬ (j.castSucc = (Fin.last n).succ) := by
    rw [Fin.succ_last]; exact (Fin.castSucc_lt_last j).ne
  by_cases hj : j = Fin.last n
  · rw [if_pos (e1.mpr hj), if_neg e2, if_pos hj]; ring
  · rw [if_neg (fun h => hj (e1.mp h)), if_neg e2, if_neg hj]; ring

/-- The `(n+1)`-dim simple root at a cast-up index never touches the top coordinate. -/
theorem root_castSucc_last (b : Fin n) : root b.castSucc (Fin.last (n + 1)) = 0 := by
  rw [root_last, if_neg]
  exact (Fin.castSucc_lt_last b).ne

/-! ### Offset of the lifted permutation -/

/-- **Lift offset split.** The offset of vertex `m.succ` of the lifted permutation splits as the
first `d_(last)` step plus the cast-up offsets of `σ`. -/
theorem lift_voff_split (σ : Equiv.Perm (Fin n)) (m : Fin (n + 1)) (i : Fin (n + 2)) :
    voff (liftPerm σ) m.succ i
      = root (Fin.last n) i
        + ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < (m : ℕ)), root ((σ a).castSucc) i := by
  unfold voff
  have hset : (univ.filter (fun l : Fin (n + 1) => (l : ℕ) < ((m.succ : Fin (n + 2)) : ℕ))).erase 0
      = (univ.filter (fun a : Fin n => (a : ℕ) < (m : ℕ))).image Fin.succ := by
    ext l
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Fin.val_succ]
    constructor
    · rintro ⟨hne, hlt⟩
      refine ⟨l.pred hne, ?_, Fin.succ_pred l hne⟩
      have hv : (l.pred hne).val + 1 = l.val := by
        conv_rhs => rw [← Fin.succ_pred l hne, Fin.val_succ]
      omega
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Fin.succ_ne_zero a, by simp only [Fin.val_succ]; omega⟩
  have h0mem : (0 : Fin (n + 1)) ∈
      univ.filter (fun l : Fin (n + 1) => (l : ℕ) < ((m.succ : Fin (n + 2)) : ℕ)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_succ, Fin.val_zero]; omega
  rw [← Finset.add_sum_erase _ _ h0mem, liftPerm_zero]
  congr 1
  rw [hset, Finset.sum_image (fun a _ b _ h => Fin.succ_injective n h)]
  exact Finset.sum_congr rfl (fun a _ => by rw [liftPerm_succ])

/-- The lift offset at a cast-up coordinate equals the boundary correction plus the `σ` offset. -/
theorem lift_voff_castSucc (σ : Equiv.Perm (Fin n)) (m j : Fin (n + 1)) :
    voff (liftPerm σ) m.succ j.castSucc
      = (if j = Fin.last n then (1 : ℤ) else 0) + voff σ m j := by
  rw [lift_voff_split, root_last_castSucc]
  congr 1
  exact Finset.sum_congr rfl (fun a _ => by rw [root_castSucc])

/-- The lift offset at the top coordinate is always `-1` (the prepended `d_(last)` step). -/
theorem lift_voff_last (σ : Equiv.Perm (Fin n)) (m : Fin (n + 1)) :
    voff (liftPerm σ) m.succ (Fin.last (n + 1)) = -1 := by
  rw [lift_voff_split, root_last, if_pos rfl]
  have : ∑ a ∈ univ.filter (fun a : Fin n => (a : ℕ) < (m : ℕ)),
      root ((σ a).castSucc) (Fin.last (n + 1)) = 0 :=
    Finset.sum_eq_zero (fun a _ => root_castSucc_last (σ a))
  rw [this]; ring

/-! ### The lifted base and cell -/

/-- The last coordinate of any cell's base is positive: the `d_(last)` step decreases it by one, so
nonnegativity at the top vertex forces `1 ≤ base (Fin.last n)`. -/
theorem dbase_last_pos (d : Cell n N) (hN : 0 < N) : 1 ≤ d.base (Fin.last n) := by
  cases n with
  | zero =>
    have hs : d.base 0 = N := by simpa using d.sum_base
    have h0 : d.base (Fin.last 0) = N := by rw [show (Fin.last 0 : Fin 1) = 0 from rfl]; exact hs
    omega
  | succ m => exact base_last_pos d

/-- The base of the lifted cell: `1` at the top coordinate, and `d.base` (with the `d_(last)`
correction) on the projected coordinates. -/
def liftBase (d : Cell n N) : Fin (n + 2) → ℕ :=
  Fin.lastCases 1 (fun j : Fin (n + 1) => d.base j - (if j = Fin.last n then 1 else 0))

@[simp] theorem liftBase_last (d : Cell n N) : liftBase d (Fin.last (n + 1)) = 1 := by
  simp [liftBase]

@[simp] theorem liftBase_castSucc (d : Cell n N) (j : Fin (n + 1)) :
    liftBase d j.castSucc = d.base j - (if j = Fin.last n then 1 else 0) := by
  simp [liftBase]

theorem liftBase_castSucc_cast (d : Cell n N) (hN : 0 < N) (j : Fin (n + 1)) :
    ((liftBase d j.castSucc : ℤ)) = (d.base j : ℤ) - (if j = Fin.last n then 1 else 0) := by
  rw [liftBase_castSucc]
  by_cases hj : j = Fin.last n
  · subst hj
    rw [if_pos rfl, if_pos rfl, Nat.cast_sub (dbase_last_pos d hN), Nat.cast_one]
  · rw [if_neg hj, if_neg hj]; simp

/-- **The lifted cell.** Given an `n`-cell `d`, the unique boundary `(n+1)`-cell whose projected
face cell is `d`: prepend the `d_(last)` Kuhn step. -/
noncomputable def lift (d : Cell n N) (hN : 0 < N) : Cell (n + 1) N where
  base := liftBase d
  perm := liftPerm d.perm
  sum_base := by
    have key : ((∑ i, liftBase d i : ℕ) : ℤ) = (N : ℤ) := by
      rw [Nat.cast_sum, Fin.sum_univ_castSucc]
      simp only [liftBase_last]
      rw [Finset.sum_congr rfl (fun j _ => liftBase_castSucc_cast d hN j), Finset.sum_sub_distrib]
      have hb : ∑ j : Fin (n + 1), (d.base j : ℤ) = (N : ℤ) := by rw [← Nat.cast_sum, d.sum_base]
      have hi : ∑ j : Fin (n + 1), (if j = Fin.last n then (1 : ℤ) else 0) = 1 := by
        rw [Finset.sum_ite_eq' univ (Fin.last n) (fun _ => (1 : ℤ))]; simp
      push_cast
      rw [hb, hi]; ring
    exact_mod_cast key
  valid := fun k i => by
    refine Fin.cases ?_ (fun m => ?_) k
    · have hz : voff (liftPerm d.perm) 0 i = 0 := by
        unfold voff
        apply Finset.sum_eq_zero
        intro l hl
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero] at hl
        exfalso
        have hl' : (l : ℕ) < 0 := by simpa using hl
        exact Nat.not_lt_zero (l : ℕ) hl'
      rw [hz, add_zero]
      exact_mod_cast Nat.zero_le (liftBase d i)
    · refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [liftBase_last, lift_voff_last]; norm_num
      · rw [liftBase_castSucc_cast d hN j, lift_voff_castSucc]
        have hv := d.valid m j
        have heq : ((d.base j : ℤ) - (if j = Fin.last n then (1 : ℤ) else 0))
              + ((if j = Fin.last n then (1 : ℤ) else 0) + voff d.perm m j)
            = (d.base j : ℤ) + voff d.perm m j := by ring
        rw [heq]; exact hv

@[simp] theorem lift_base (d : Cell n N) (hN : 0 < N) : (lift d hN).base = liftBase d := by
  simp [lift]
@[simp] theorem lift_perm (d : Cell n N) (hN : 0 < N) : (lift d hN).perm = liftPerm d.perm := by
  simp [lift]

@[simp] theorem lift_base_last (d : Cell n N) (hN : 0 < N) :
    (lift d hN).base (Fin.last (n + 1)) = 1 := liftBase_last d
@[simp] theorem lift_perm_zero (d : Cell n N) (hN : 0 < N) :
    (lift d hN).perm 0 = Fin.last n := liftPerm_zero d.perm

/-! ### The two inverse identities -/

/-- Vertex `1` of the lifted cell, projected, recovers `d.base`. -/
theorem lift_vertex_one_coord (d : Cell n N) (hN : 0 < N) (i : Fin (n + 1)) :
    ((lift d hN).vertex 1).1 i.castSucc = d.base i := by
  rw [show (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ from rfl]
  have hval := (lift d hN).vertex_val (0 : Fin (n + 1)).succ i.castSucc
  rw [lift_perm, lift_base, lift_voff_castSucc, liftBase_castSucc_cast d hN i] at hval
  have hz : voff d.perm (0 : Fin (n + 1)) i = 0 := by
    unfold voff
    apply Finset.sum_eq_zero
    intro l hl
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_zero] at hl
    exfalso
    have hl' : (l : ℕ) < 0 := by simpa using hl
    exact Nat.not_lt_zero (l : ℕ) hl'
  rw [hz] at hval
  have h2 : (((lift d hN).vertex (0 : Fin (n + 1)).succ).1 i.castSucc : ℤ) = (d.base i : ℤ) := by
    rw [hval]; ring
  exact_mod_cast h2

/-- **Right inverse.** `bcell` undoes `lift`. -/
theorem bcell_lift (d : Cell n N) (hN : 0 < N) :
    bcell (lift d hN) (lift_base_last d hN) (lift_perm_zero d hN) = d := by
  refine Cell.eq_of_base_perm (funext fun i => ?_) ?_
  · rw [bcell_base]
    exact lift_vertex_one_coord d hN i
  · rw [bcell_perm]
    refine Equiv.ext fun j => Fin.castSucc_injective n ?_
    rw [bperm_castSucc, lift_perm, liftPerm_succ]

/-- The projected base of a boundary cell, expressed through the original base. -/
theorem bcellBase_eq (c : Cell (n + 1) N) (hp0 : c.perm 0 = Fin.last n) (j : Fin (n + 1)) :
    bcellBase c j = c.base j.castSucc + (if j = Fin.last n then 1 else 0) := by
  have hfilter : Finset.univ.filter (fun l : Fin (n + 1) => (l : ℕ) < ((1 : Fin (n + 2)) : ℕ))
      = {(0 : Fin (n + 1))} := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Fin.val_one, Fin.ext_iff, Fin.val_zero]
    simp [Nat.lt_one_iff]
  have hv1 : voff c.perm 1 j.castSucc = root (Fin.last n) j.castSucc := by
    unfold voff; rw [hfilter, Finset.sum_singleton, hp0]
  have hval := c.vertex_val 1 j.castSucc
  rw [hv1, root_last_castSucc] at hval
  have hcast : ((bcellBase c j : ℕ) : ℤ)
      = ((c.base j.castSucc + (if j = Fin.last n then 1 else 0) : ℕ) : ℤ) := by
    show (((c.vertex 1).1 j.castSucc : ℕ) : ℤ) = _
    rw [hval]; push_cast; by_cases hj : j = Fin.last n <;> simp [hj]
  exact_mod_cast hcast

/-- **Left inverse.** `lift` undoes `bcell` on boundary cells. -/
theorem lift_bcell (c : Cell (n + 1) N) (hN : 0 < N)
    (hb : c.base (Fin.last (n + 1)) = 1) (hp0 : c.perm 0 = Fin.last n) :
    lift (bcell c hb hp0) hN = c := by
  refine Cell.eq_of_base_perm (funext fun i => ?_) ?_
  · rw [lift_base]
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [liftBase_last, hb]
    · rw [liftBase_castSucc, bcell_base, bcellBase_eq c hp0 j, Nat.add_sub_cancel]
  · rw [lift_perm]
    refine Equiv.ext fun x => ?_
    refine Fin.cases ?_ (fun j => ?_) x
    · rw [liftPerm_zero, hp0]
    · rw [liftPerm_succ, bcell_perm, bperm_castSucc]

/-! ### The count identity -/

/-- A **boundary door cell** of `col`: an `(n+1)`-cell touching the face `x_last = 0` with first Kuhn
step `d_(last)`, whose on-face facet (dropping vertex `0`) is a *door* under `col`. -/
def isBoundaryDoorCell (col : SpernerColoring (n + 1) N) (c : Cell (n + 1) N) : Prop :=
  c.base (Fin.last (n + 1)) = 1 ∧ c.perm 0 = Fin.last n ∧
    (facetVerts c 0).image col.color = lowColors (n + 1)

instance decidableIsBoundaryDoorCell (col : SpernerColoring (n + 1) N) :
    DecidablePred (isBoundaryDoorCell col) := fun c => by unfold isBoundaryDoorCell; infer_instance

/-- **Boundary doors = rainbow `n`-cells.** Via the `bcell`/`lift` bijection together with the
door ↔ rainbow correspondence, the boundary door cells of `col` are in bijection with the rainbow
`n`-cells of the restricted coloring; in particular their counts agree. This is the inductive bridge:
the right-hand count is odd by the inductive hypothesis. -/
theorem boundary_doors_eq_rainbow (col : SpernerColoring (n + 1) N) (hN : 0 < N) :
    (univ.filter (isBoundaryDoorCell col)).card
      = (univ.filter (IsRainbowCell (restrictColoring col))).card := by
  refine Finset.card_bij'
    (fun c hc => bcell c (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc).2.2.1)
    (fun d _ => lift d hN) ?_ ?_ ?_ ?_
  · intro c hc
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _,
      (door_iff_rainbow c (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc).2.2.1 col).mp
        (Finset.mem_filter.mp hc).2.2.2⟩
  · intro d hd
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, lift_base_last d hN, lift_perm_zero d hN, ?_⟩
    rw [door_iff_rainbow (lift d hN) (lift_base_last d hN) (lift_perm_zero d hN) col, bcell_lift d hN]
    exact (Finset.mem_filter.mp hd).2
  · intro c hc
    exact lift_bcell c hN (Finset.mem_filter.mp hc).2.1 (Finset.mem_filter.mp hc).2.2.1
  · intro d _
    exact bcell_lift d hN

end CRNT.Analysis.SpernerN
