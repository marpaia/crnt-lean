import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Nested lower envelopes

A *blueprint tree* of depth `m` is a nested family of columns: at each level a finite ordered list
of nodes with a basepoint value `β`, a lower edge `lo` and an upper breakpoint `hi`, each node
carrying a subtree of the next depth.  A full path `P` determines the affine function

`val ε P y = ∑_level (D + β * y_level)`,  `D i = -∑_{i' < i} (β (i'+1) - β i') ε ^ hi i'`.

The constants `D` are chosen so that consecutive nodes of a column tie exactly at
`u = ε ^ hi`, where `u` is the tail sum of `y` from that level on.

`realized_of_isMin`: if `P` minimizes `val ε · y` over all full paths, then at every level the
tail sum `u` lies between `ε ^ hi(i-1) / 2` and `2 ε ^ hi i`.  The proof only compares `P` with the
two neighbouring nodes followed by their *wall paths* (first child at every deeper level), and
bounds the deeper constants by the first breakpoint of each column, which the well-formedness
condition `WF` places above `β + 2ρ`.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset

/-- Depth-indexed blueprint trees. -/
inductive BTree : ℕ → Type
  | leaf : BTree 0
  | node {m : ℕ} (n : ℕ) (β lo hi : ℕ → ℝ) (sub : ℕ → BTree m) : BTree (m + 1)

namespace BTree

/-- The constant of node `i` of a column. -/
noncomputable def colD (ε : ℝ) (β hi : ℕ → ℝ) (i : ℕ) : ℝ :=
  -∑ i' ∈ range i, (β (i' + 1) - β i') * ε ^ (hi i')

theorem colD_zero (ε : ℝ) (β hi : ℕ → ℝ) : colD ε β hi 0 = 0 := by simp [colD]

theorem colD_succ (ε : ℝ) (β hi : ℕ → ℝ) (i : ℕ) :
    colD ε β hi (i + 1) = colD ε β hi i - (β (i + 1) - β i) * ε ^ (hi i) := by
  simp [colD, Finset.sum_range_succ]; ring

/-- Full paths. -/
def IsPath : {m : ℕ} → BTree m → List ℕ → Prop
  | _, .leaf, l => l = []
  | _, .node n _ _ _ sub, l => ∃ i rest, l = i :: rest ∧ i < n ∧ IsPath (sub i) rest

/-- Value of a path at `y`. -/
noncomputable def val (ε : ℝ) : {m : ℕ} → BTree m → List ℕ → (ℕ → ℝ) → ℝ
  | _, .leaf, _, _ => 0
  | _, .node _ _ _ _ _, [], _ => 0
  | _, .node _ β _ hi sub, i :: rest, y =>
      colD ε β hi i + β i * y 0 + val ε (sub i) rest (fun j => y (j + 1))

/-- Sum of absolute constants along a path. -/
noncomputable def absD (ε : ℝ) : {m : ℕ} → BTree m → List ℕ → ℝ
  | _, .leaf, _ => 0
  | _, .node _ _ _ _ _, [] => 0
  | _, .node _ β _ hi sub, i :: rest => |colD ε β hi i| + absD ε (sub i) rest

/-- The wall path: first child at every level. -/
def wallPath : {m : ℕ} → BTree m → List ℕ
  | _, .leaf => []
  | _, .node _ _ _ _ sub => 0 :: wallPath (sub 0)

/-- Radius of node `i` given the parent radius. -/
noncomputable def nodeRad (ρp : ℝ) (n : ℕ) (β hi : ℕ → ℝ) (i : ℕ) : ℝ :=
  max ρp (max (if i + 1 < n then hi i - β i else 0) (if 0 < i then β i - hi (i - 1) else 0))

theorem le_nodeRad (ρp : ℝ) (n : ℕ) (β hi : ℕ → ℝ) (i : ℕ) : ρp ≤ nodeRad ρp n β hi i :=
  le_max_left _ _

theorem nodeRad_ge_hi {ρp : ℝ} {n : ℕ} {β hi : ℕ → ℝ} {i : ℕ} (h : i + 1 < n) :
    hi i - β i ≤ nodeRad ρp n β hi i := by
  unfold nodeRad; rw [if_pos h]; exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem nodeRad_ge_lo {ρp : ℝ} {n : ℕ} {β hi : ℕ → ℝ} {i : ℕ} (h : 0 < i) :
    β i - hi (i - 1) ≤ nodeRad ρp n β hi i := by
  unfold nodeRad; rw [if_pos h]; exact le_trans (le_max_right _ _) (le_max_right _ _)

/-- Well-formedness for the envelope argument. -/
def WF : {m : ℕ} → BTree m → ℝ → ℝ → Prop
  | _, .leaf, _, _ => True
  | _, .node n β _ hi sub, βp, ρp =>
      1 ≤ n ∧ β 0 = βp ∧
      (∀ i, i + 1 < n → β i ≤ hi i ∧ hi i ≤ β (i + 1)) ∧
      (2 ≤ n → βp + 2 * ρp ≤ hi 0) ∧
      ∀ i, i < n → WF (sub i) (β i) (nodeRad ρp n β hi i)

/-- Global bounds: basepoint values in `[0, Bβ]`, sibling gaps at least `Δ`. -/
def Bounded (Bβ Δ : ℝ) : {m : ℕ} → BTree m → Prop
  | _, .leaf => True
  | _, .node n β _ _ sub =>
      (∀ i, i < n → 0 ≤ β i ∧ β i ≤ Bβ) ∧ (∀ i, i + 1 < n → Δ ≤ β (i + 1) - β i) ∧
      ∀ i, i < n → Bounded Bβ Δ (sub i)

/-- Tail sums. -/
noncomputable def ysum (m : ℕ) (y : ℕ → ℝ) : ℝ := ∑ j ∈ range m, y j

theorem ysum_succ (m : ℕ) (y : ℕ → ℝ) :
    ysum (m + 1) y = y 0 + ysum m (fun j => y (j + 1)) := by
  simp [ysum, Finset.sum_range_succ']; ring

theorem ysum_nonneg {m : ℕ} {y : ℕ → ℝ} (hy : ∀ j, 0 ≤ y j) : 0 ≤ ysum m y :=
  Finset.sum_nonneg fun j _ => hy j

/-! ### Elementary facts -/

theorem isPath_wallPath : ∀ {m : ℕ} (t : BTree m) (βp ρp : ℝ), WF t βp ρp →
    IsPath t (wallPath t)
  | _, .leaf, _, _, _ => rfl
  | _, .node n β lo hi sub, βp, ρp, h =>
      ⟨0, wallPath (sub 0), rfl, h.1, isPath_wallPath (sub 0) _ _ (h.2.2.2.2 0 h.1)⟩

theorem val_wallPath (ε : ℝ) : ∀ {m : ℕ} (t : BTree m) (βp ρp : ℝ), WF t βp ρp →
    ∀ y : ℕ → ℝ, val ε t (wallPath t) y = βp * ysum m y
  | _, .leaf, _, _, _, y => by simp [val, wallPath, ysum]
  | _, .node n β lo hi sub, βp, ρp, h, y => by
      have hsub := val_wallPath ε (sub 0) _ _ (h.2.2.2.2 0 h.1) (fun j => y (j + 1))
      simp only [wallPath, val, colD_zero, hsub, ysum_succ, h.2.1]
      ring

/-- Column constants are bounded by the first breakpoint. -/
theorem abs_colD_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {n : ℕ} {β hi : ℕ → ℝ}
    (hmono : ∀ i, i + 1 < n → β i ≤ hi i ∧ hi i ≤ β (i + 1)) {i : ℕ} (hi' : i < n) :
    |colD ε β hi i| ≤ (β i - β 0) * ε ^ (hi 0) := by
  have hβmono : ∀ i', i' + 1 < n → β i' ≤ β (i' + 1) := fun i' h' =>
    le_trans (hmono i' h').1 (hmono i' h').2
  have hhi : ∀ i', i' + 1 < n → hi 0 ≤ hi i' := by
    intro i' h'
    induction i' with
    | zero => exact le_rfl
    | succ k ih =>
        have hk : k + 1 < n := by omega
        exact le_trans (ih hk) (le_trans (hmono k hk).2 (hmono (k + 1) h').1)
  have hterm : ∀ i' ∈ range i, 0 ≤ (β (i' + 1) - β i') * ε ^ (hi i') := by
    intro i' hi''
    have := hβmono i' (by simp at hi''; omega)
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hε0.le _)
  have hsum_nn : 0 ≤ ∑ i' ∈ range i, (β (i' + 1) - β i') * ε ^ (hi i') := sum_nonneg hterm
  rw [colD, abs_neg, abs_of_nonneg hsum_nn]
  calc ∑ i' ∈ range i, (β (i' + 1) - β i') * ε ^ (hi i')
      ≤ ∑ i' ∈ range i, (β (i' + 1) - β i') * ε ^ (hi 0) := by
        refine sum_le_sum fun i' hi'' => ?_
        have hlt : i' + 1 < n := by simp at hi''; omega
        exact mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (hhi i' hlt))
          (by linarith [hβmono i' hlt])
    _ = (β i - β 0) * ε ^ (hi 0) := by
        rw [← sum_mul, Finset.sum_range_sub (f := β)]

/-- Every basepoint value in a well-formed subtree is at least the parent value. -/
theorem val_ge (ε : ℝ) : ∀ {m : ℕ} (t : BTree m) (βp ρp : ℝ), WF t βp ρp →
    ∀ P, IsPath t P → ∀ y : ℕ → ℝ, (∀ j, 0 ≤ y j) →
    βp * ysum m y - absD ε t P ≤ val ε t P y
  | _, .leaf, _, _, _, P, hP, y, hy => by
      simp [val, absD, ysum]
  | m + 1, .node n β lo hi sub, βp, ρp, h, P, hP, y, hy => by
      obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
      have ih := val_ge ε (sub i) _ _ (h.2.2.2.2 i hin) rest hrest (fun j => y (j + 1))
        (fun j => hy _)
      have hβi : βp ≤ β i := by
        have : ∀ k, k < n → βp ≤ β k := by
          intro k hk
          induction k with
          | zero => exact h.2.1.symm.le
          | succ k ihk =>
              have := h.2.2.1 k (by omega)
              exact le_trans (ihk (by omega)) (le_trans this.1 this.2)
        exact this i hin
      have hys := ysum_nonneg (m := m) (fun j => hy (j + 1))
      simp only [val, absD, ysum_succ]
      have hc : -|colD ε β hi i| ≤ colD ε β hi i := neg_abs_le _
      have h1 : βp * y 0 ≤ β i * y 0 := mul_le_mul_of_nonneg_right hβi (hy 0)
      have h2 : βp * ysum m (fun j => y (j + 1)) ≤ β i * ysum m (fun j => y (j + 1)) :=
        mul_le_mul_of_nonneg_right hβi hys
      nlinarith

/-- The constants along any path of a well-formed bounded subtree are exponentially small in the
parent's `β + 2ρ`. -/
theorem absD_le {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {Bβ Δ : ℝ} :
    ∀ {m : ℕ} (t : BTree m) (βp ρp : ℝ), WF t βp ρp → Bounded Bβ Δ t → 0 ≤ ρp →
    ∀ P, IsPath t P → absD ε t P ≤ m * Bβ * ε ^ (βp + 2 * ρp)
  | _, .leaf, _, _, _, _, _, P, _ => by simp [absD]
  | m + 1, .node n β lo hi sub, βp, ρp, h, hb, hρ, P, hP => by
      obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
      have hβmono : ∀ k, k < n → βp ≤ β k := by
        intro k hk
        induction k with
        | zero => exact h.2.1.symm.le
        | succ k ihk =>
            have := h.2.2.1 k (by omega)
            exact le_trans (ihk (by omega)) (le_trans this.1 this.2)
      have hρi : ρp ≤ nodeRad ρp n β hi i := le_nodeRad _ _ _ _ _
      have ih := absD_le hε0 hε1 (sub i) _ _ (h.2.2.2.2 i hin) (hb.2.2 i hin)
        (le_trans hρ hρi) rest hrest
      have hexp : ε ^ (β i + 2 * nodeRad ρp n β hi i) ≤ ε ^ (βp + 2 * ρp) :=
        Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith [hβmono i hin])
      have hBβ : 0 ≤ Bβ := le_trans (hb.1 i hin).1 (hb.1 i hin).2
      have hcol : |colD ε β hi i| ≤ Bβ * ε ^ (βp + 2 * ρp) := by
        rcases Nat.lt_or_ge n 2 with hn | hn
        · have : i = 0 := by omega
          subst this; simp [colD_zero]; positivity
        · refine le_trans (abs_colD_le hε0 hε1 h.2.2.1 hin) ?_
          have hhi0 := h.2.2.2.1 hn
          have h0 : 0 ≤ β 0 := (hb.1 0 (by omega)).1
          refine mul_le_mul (by linarith [(hb.1 i hin).2]) ?_ (Real.rpow_nonneg hε0.le _) hBβ
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le hhi0
      simp only [absD]
      have hm : (m : ℝ) * Bβ * ε ^ (β i + 2 * nodeRad ρp n β hi i) ≤
          (m : ℝ) * Bβ * ε ^ (βp + 2 * ρp) :=
        mul_le_mul_of_nonneg_left hexp (by positivity)
      push_cast
      nlinarith

/-! ### The envelope localization -/

/-- What the minimizing path tells us at every level. -/
def Realized (ε : ℝ) : {m : ℕ} → BTree m → List ℕ → (ℕ → ℝ) → Prop
  | _, .leaf, _, _ => True
  | _, .node _ _ _ _ _, [], _ => True
  | m + 1, .node n _ _ hi sub, i :: rest, y =>
      (i + 1 < n → ε ^ (hi i) ≤ 2 * ysum (m + 1) y) ∧
      (0 < i → ysum (m + 1) y ≤ 2 * ε ^ (hi (i - 1))) ∧
      Realized ε (sub i) rest (fun j => y (j + 1))

theorem realized_of_isMin {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {Bβ Δ γ : ℝ} (M0 : ℕ)
    (hγ : 0 < γ) (hΔ : 0 < Δ) (hsmall : (M0 : ℝ) * Bβ * ε ^ γ ≤ Δ / 2) :
    ∀ {m : ℕ} (t : BTree m) (βp ρp : ℝ), m ≤ M0 + 1 → WF t βp ρp → Bounded Bβ Δ t →
    γ ≤ ρp → ∀ y : ℕ → ℝ, (∀ j, 0 ≤ y j) →
    ∀ P, IsPath t P → (∀ Q, IsPath t Q → val ε t P y ≤ val ε t Q y) →
    Realized ε t P y
  | _, .leaf, _, _, _, _, _, _, y, hy, P, hP, hmin => trivial
  | m + 1, .node n β lo hi sub, βp, ρp, hm, h, hb, hγρ, y, hy, P, hP, hmin => by
      obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
      set ρi := nodeRad ρp n β hi i with hρi
      have hρi_ge : γ ≤ ρi := le_trans hγρ (le_nodeRad _ _ _ _ _)
      have hWFi := h.2.2.2.2 i hin
      have hBi := hb.2.2 i hin
      set y' : ℕ → ℝ := fun j => y (j + 1) with hy'
      have hy'nn : ∀ j, 0 ≤ y' j := fun j => hy _
      have hu : ysum (m + 1) y = y 0 + ysum m y' := ysum_succ m y
      -- lower bound for the actual path
      have hlow := val_ge ε (sub i) _ _ hWFi rest hrest y' hy'nn
      have hE := absD_le hε0 hε1 (sub i) _ _ hWFi hBi (le_trans hγ.le hρi_ge) rest hrest
      have hBβ : 0 ≤ Bβ := le_trans (hb.1 i hin).1 (hb.1 i hin).2
      have hmM : (m : ℝ) ≤ M0 := by exact_mod_cast (by omega : m ≤ M0)
      have hvalP : val ε (BTree.node n β lo hi sub) (i :: rest) y =
          colD ε β hi i + β i * y 0 + val ε (sub i) rest y' := rfl
      have hcomp : ∀ i', i' < n → val ε (BTree.node n β lo hi sub) (i :: rest) y ≤
          colD ε β hi i' + β i' * ysum (m + 1) y := by
        intro i' hi'
        have hpath : IsPath (BTree.node n β lo hi sub) (i' :: wallPath (sub i')) :=
          ⟨i', _, rfl, hi', isPath_wallPath _ _ _ (h.2.2.2.2 i' hi')⟩
        have := hmin _ hpath
        have hw := val_wallPath ε (sub i') _ _ (h.2.2.2.2 i' hi') y'
        have : val ε (BTree.node n β lo hi sub) (i' :: wallPath (sub i')) y =
            colD ε β hi i' + β i' * ysum (m + 1) y := by
          show colD ε β hi i' + β i' * y 0 + val ε (sub i') (wallPath (sub i')) y' = _
          rw [hw, hu]; ring
        linarith
      refine ⟨?_, ?_, ?_⟩
      · -- upper neighbour
        intro hnext
        have hc := hcomp (i + 1) hnext
        rw [colD_succ] at hc
        have hgap := hb.2.1 i hnext
        have hrad : hi i - β i ≤ ρi := nodeRad_ge_hi hnext
        have hexp : ε ^ (β i + 2 * ρi) ≤ ε ^ (hi i) * ε ^ γ := by
          rw [← Real.rpow_add hε0]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
        have hpow : 0 < ε ^ (hi i) := Real.rpow_pos_of_pos hε0 _
        have hEle : absD ε (sub i) rest ≤ Δ / 2 * ε ^ (hi i) := by
          calc absD ε (sub i) rest ≤ m * Bβ * ε ^ (β i + 2 * ρi) := hE
            _ ≤ M0 * Bβ * (ε ^ (hi i) * ε ^ γ) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hmM hBβ) hexp
                  (Real.rpow_nonneg hε0.le _) (by positivity)
            _ = (M0 * Bβ * ε ^ γ) * ε ^ (hi i) := by ring
            _ ≤ Δ / 2 * ε ^ (hi i) := mul_le_mul_of_nonneg_right hsmall hpow.le
        rw [hvalP] at hc
        set u := ysum (m + 1) y with hudef
        set e := ε ^ (hi i) with hedef
        have key : (β (i + 1) - β i) * (e - u) ≤ Δ / 2 * e := by
          have h3 : (β (i + 1) - β i) * (e - u) =
              (β (i + 1) - β i) * e - β (i + 1) * u + β i * y 0 + β i * ysum m y' := by
            rw [hu]; ring
          rw [h3]; linarith
        by_contra hcon
        push_neg at hcon
        have hpos : 0 < e - u := by linarith
        have : Δ * (e - u) ≤ (β (i + 1) - β i) * (e - u) :=
          mul_le_mul_of_nonneg_right hgap hpos.le
        nlinarith
      · -- lower neighbour
        intro hpos
        have hprev : i - 1 + 1 = i := Nat.sub_add_cancel hpos
        have hc := hcomp (i - 1) (by omega)
        have hD : colD ε β hi i = colD ε β hi (i - 1) - (β i - β (i - 1)) * ε ^ (hi (i - 1)) := by
          conv_lhs => rw [← hprev]
          rw [colD_succ, hprev]
        have hgap := hb.2.1 (i - 1) (by omega)
        rw [hprev] at hgap
        have hrad : β i - hi (i - 1) ≤ ρi := nodeRad_ge_lo hpos
        have hord := (h.2.2.1 (i - 1) (by omega)).2
        rw [hprev] at hord
        have hexp : ε ^ (β i + 2 * ρi) ≤ ε ^ (hi (i - 1)) * ε ^ γ := by
          rw [← Real.rpow_add hε0]
          exact Real.rpow_le_rpow_of_exponent_ge hε0 hε1.le (by linarith)
        have hpow : 0 < ε ^ (hi (i - 1)) := Real.rpow_pos_of_pos hε0 _
        have hEle : absD ε (sub i) rest ≤ Δ / 2 * ε ^ (hi (i - 1)) := by
          calc absD ε (sub i) rest ≤ m * Bβ * ε ^ (β i + 2 * ρi) := hE
            _ ≤ M0 * Bβ * (ε ^ (hi (i - 1)) * ε ^ γ) := by
                apply mul_le_mul (mul_le_mul_of_nonneg_right hmM hBβ) hexp
                  (Real.rpow_nonneg hε0.le _) (by positivity)
            _ = (M0 * Bβ * ε ^ γ) * ε ^ (hi (i - 1)) := by ring
            _ ≤ Δ / 2 * ε ^ (hi (i - 1)) := mul_le_mul_of_nonneg_right hsmall hpow.le
        rw [hvalP, hD] at hc
        set u := ysum (m + 1) y with hudef
        set e := ε ^ (hi (i - 1)) with hedef
        have key : (β i - β (i - 1)) * (u - e) ≤ Δ / 2 * e := by
          have h3 : (β i - β (i - 1)) * (u - e) =
              β i * y 0 + β i * ysum m y' - β (i - 1) * u - (β i - β (i - 1)) * e := by
            rw [hu]; ring
          rw [h3]; linarith
        by_contra hcon
        push_neg at hcon
        have hpos : 0 < u - e := by linarith
        have : Δ * (u - e) ≤ (β i - β (i - 1)) * (u - e) :=
          mul_le_mul_of_nonneg_right hgap hpos.le
        nlinarith
      · -- recurse
        refine realized_of_isMin hε0 hε1 M0 hγ hΔ hsmall (sub i) _ _ (by omega) hWFi hBi hρi_ge y'
          hy'nn rest hrest ?_
        intro Q hQ
        have := hmin (i :: Q) ⟨i, Q, rfl, hin, hQ⟩
        simp only [val] at this
        linarith

end BTree
end Persistence
end CRNT
