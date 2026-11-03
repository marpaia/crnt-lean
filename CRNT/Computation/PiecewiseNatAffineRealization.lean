import CRNT.Computation.PiecewiseNatAffine
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases

/-!
# Chemical realizations of affine minima

Explicit networks and stable-computation proofs for minima of natural-affine
functions. These are sufficient constructions for a restricted family, not a
realization theorem for every classical semilinear function or every function
satisfying `PiecewiseNatAffine`.
-/

namespace CRNT

namespace Computation

open scoped BigOperators

namespace MinAffine

variable {d k : ℕ}

/-! ## Small helpers -/

/-- In `Fin (n+1)`, an element is `≤ 0` exactly when it is `0`. -/
theorem fin_le_zero_iff {n : ℕ} (l : Fin (n+1)) : l ≤ 0 ↔ l = 0 := by
  constructor
  · intro h
    have h' : l.val ≤ 0 := by
      rw [Fin.le_iff_val_le_val] at h
      simpa using h
    rw [Fin.ext_iff]
    simp only [Fin.val_zero]
    omega
  · intro h
    subst h
    exact le_rfl

/-- If `x` is a lower bound of all the values `A j` and is equal to one of them, then `x`
is the minimum of the values `A j`. -/
theorem eq_finsetMin_of_le_and_mem {α : Type} [Fintype α] [DecidableEq α] [Nonempty α]
    (A : α → ℕ) (x : ℕ) (h1 : ∀ j, x ≤ A j) (h2 : ∃ j, x = A j) :
    x = ((Finset.univ : Finset α).image A).min' (Finset.Nonempty.image Finset.univ_nonempty A) := by
  have hmem : x ∈ (Finset.univ : Finset α).image A := by
    obtain ⟨j, hj⟩ := h2
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, hj.symm⟩
  have hne : ((Finset.univ : Finset α).image A).Nonempty :=
    Finset.Nonempty.image Finset.univ_nonempty A
  have hle : ((Finset.univ : Finset α).image A).min' hne ≤ x := Finset.min'_le _ x hmem
  have hmem2 := Finset.min'_mem _ hne
  obtain ⟨j, hj, hval⟩ := Finset.mem_image.mp hmem2
  have : x ≤ ((Finset.univ : Finset α).image A).min' hne := by
    rw [← hval]
    exact h1 j
  exact le_antisymm this hle

/-! ## The network -/

/-- The species type of the network computing the minimum of finitely many affine
functions: `Sum.inl i` is the input species `X_i`, `Sum.inr (Sum.inl l)` is the
accumulator `Z_l`, and `Sum.inr (Sum.inr r)` is the piece stream `P_r`. -/
abbrev Species (d k : ℕ) := Fin d ⊕ Fin (k+1) ⊕ Fin k

/-- The input species `X_i`. -/
abbrev xSpec (i : Fin d) : Species d k := Sum.inl i

/-- The accumulator species `Z_l`; `Z_k` is the output species. -/
abbrev zSpec (l : Fin (k+1)) : Species d k := Sum.inr (Sum.inl l)

/-- The piece stream species `P_r`, which carries the molecules of the piece `r + 1`. -/
abbrev pSpec (r : Fin k) : Species d k := Sum.inr (Sum.inr r)

/-- The source complex of the conversion reaction for the input `i`: one molecule of
`X_i`. -/
def convSource (i : Fin d) : Species d k → ℕ := fun s => if s = xSpec i then 1 else 0

/-- The target complex of the conversion reaction for the input `i`: the molecules of
every piece, `(ps l).coeff i` molecules of the stream of the piece `l`. -/
def convTarget (ps : Fin (k+1) → Affine d) (i : Fin d) : Species d k → ℕ := fun s =>
  match s with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl l) => if l = 0 then (ps 0).coeff i else 0
  | Sum.inr (Sum.inr r) => (ps (r.succ)).coeff i

/-- The source complex of the chain reaction `j`: one molecule of the accumulator `Z_j`
and one molecule of the piece stream `P_j`. -/
def chainSource (j : Fin k) : Species d k → ℕ := fun s =>
  match s with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl l) => if l = Fin.castSucc j then 1 else 0
  | Sum.inr (Sum.inr r) => if r = j then 1 else 0

/-- The target complex of the chain reaction `j`: one molecule of the accumulator
`Z_{j+1}`. -/
def chainTarget (j : Fin k) : Species d k → ℕ := fun s =>
  match s with
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl l) => if l = j.succ then 1 else 0
  | Sum.inr (Sum.inr _) => 0

/-- **The network computing the minimum of the affine pieces `ps`.**

The reactions are indexed by `Fin d ⊕ Fin k`:
* `Sum.inl i` is the conversion reaction `X_i → (ps 0).coeff i · Z_0 + ∑ r,
  (ps (r+1)).coeff i · P_r`, and
* `Sum.inr j` is the chain reaction `Z_j + P_j → Z_{j+1}`. -/
abbrev minAffineCRN (ps : Fin (k+1) → Affine d) : Network (Species d k) :=
  ⟨Fin d ⊕ Fin k, inferInstance, inferInstance, fun r => match r with
    | Sum.inl i => ⟨convSource i, convTarget ps i⟩
    | Sum.inr j => ⟨chainSource j, chainTarget j⟩⟩

/-- The initial configuration of `minAffineCRN`: `x i` molecules of the input species
`X_i`, the constant `a l = (ps l).const` in the stream of the piece `l`
(`a 0` molecules of `Z_0`, `a l` molecules of `P_{l-1}` for `l ≥ 1`). -/
def minAffineInit (ps : Fin (k+1) → Affine d) (x : Fin d → ℕ) : Config (Species d k) :=
  fun s => match s with
    | Sum.inl i => x i
    | Sum.inr (Sum.inl l) => if l = 0 then (ps 0).const else 0
    | Sum.inr (Sum.inr r) => (ps (r.succ)).const

/-- The output species of `minAffineCRN`: the last accumulator `Z_k`. -/
def minAffineOut (k : ℕ) : Species d k := zSpec ⟨k, by omega⟩

/-- The value computed by the network at the input `x`: the minimum of the values of the
pieces. -/
def minAffineVal (ps : Fin (k+1) → Affine d) (x : Fin d → ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin (k+1))).image (fun l => (ps l).eval x)).min'
    (Finset.Nonempty.image (Finset.univ_nonempty) (fun l => (ps l).eval x))

/-! ## The complexes of the reactions -/

@[simp] theorem convSource_x (i j : Fin d) :
    (convSource (d := d) (k := k) i (xSpec (d := d) (k := k) j) : ℕ) = if j = i then 1 else 0 := by
  simp [convSource, xSpec]

@[simp] theorem convSource_z (i : Fin d) (l : Fin (k+1)) :
    (convSource (d := d) (k := k) i (zSpec (d := d) (k := k) l) : ℕ) = 0 := by
  simp [convSource, xSpec, zSpec]

@[simp] theorem convSource_p (i : Fin d) (r : Fin k) :
    (convSource (d := d) (k := k) i (pSpec (d := d) (k := k) r) : ℕ) = 0 := by
  simp [convSource, xSpec, pSpec]

@[simp] theorem convTarget_x (ps : Fin (k+1) → Affine d) (i j : Fin d) :
    (convTarget ps i (xSpec (d := d) (k := k) j) : ℕ) = 0 := by
  simp [convTarget]

@[simp] theorem convTarget_z (ps : Fin (k+1) → Affine d) (i : Fin d) (l : Fin (k+1)) :
    (convTarget ps i (zSpec (d := d) (k := k) l) : ℕ) = if l = 0 then (ps 0).coeff i else 0 := by
  simp [convTarget]

@[simp] theorem convTarget_p (ps : Fin (k+1) → Affine d) (i : Fin d) (r : Fin k) :
    (convTarget ps i (pSpec (d := d) (k := k) r) : ℕ) = (ps (r.succ)).coeff i := by
  simp [convTarget]

@[simp] theorem chainSource_x (j : Fin k) (i : Fin d) :
    (chainSource (d := d) (k := k) j (xSpec (d := d) (k := k) i) : ℕ) = 0 := by
  simp [chainSource]

@[simp] theorem chainSource_z (j : Fin k) (l : Fin (k+1)) :
    (chainSource (d := d) (k := k) j (zSpec (d := d) (k := k) l) : ℕ) = if l = Fin.castSucc j then 1 else 0 := by
  simp [chainSource]

@[simp] theorem chainSource_p (j : Fin k) (r : Fin k) :
    (chainSource (d := d) (k := k) j (pSpec (d := d) (k := k) r) : ℕ) = if r = j then 1 else 0 := by
  simp [chainSource]

@[simp] theorem chainTarget_x (j : Fin k) (i : Fin d) :
    (chainTarget (d := d) (k := k) j (xSpec (d := d) (k := k) i) : ℕ) = 0 := by
  simp [chainTarget]

@[simp] theorem chainTarget_z (j : Fin k) (l : Fin (k+1)) :
    (chainTarget (d := d) (k := k) j (zSpec (d := d) (k := k) l) : ℕ) = if l = j.succ then 1 else 0 := by
  simp [chainTarget]

@[simp] theorem chainTarget_p (j : Fin k) (r : Fin k) :
    (chainTarget (d := d) (k := k) j (pSpec (d := d) (k := k) r) : ℕ) = 0 := by
  simp [chainTarget]

/-- The stoichiometric change of the conversion reaction at the input species. -/
@[simp] theorem delta_conv_x (ps : Fin (k+1) → Affine d) (i j : Fin d) :
    delta (minAffineCRN ps) (Sum.inl i) (xSpec (d := d) (k := k) j)
      = (if j = i then (-1 : ℤ) else 0) := by
  simp [delta]
  by_cases h : j = i <;> simp [h]

/-- The stoichiometric change of the conversion reaction at an accumulator. -/
@[simp] theorem delta_conv_z (ps : Fin (k+1) → Affine d) (i : Fin d) (l : Fin (k+1)) :
    delta (minAffineCRN ps) (Sum.inl i) (zSpec (d := d) (k := k) l)
      = (if l = 0 then ((ps 0).coeff i : ℤ) else 0) := by
  simp [delta]

/-- The stoichiometric change of the conversion reaction at a piece stream. -/
@[simp] theorem delta_conv_p (ps : Fin (k+1) → Affine d) (i : Fin d) (r : Fin k) :
    delta (minAffineCRN ps) (Sum.inl i) (pSpec (d := d) (k := k) r) = ((ps (r.succ)).coeff i : ℤ) := by
  simp [delta]

/-- The stoichiometric change of the chain reaction at an accumulator. -/
@[simp] theorem delta_chain_z (ps : Fin (k+1) → Affine d) (j : Fin k) (l : Fin (k+1)) :
    delta (minAffineCRN ps) (Sum.inr j) (zSpec (d := d) (k := k) l)
      = (if l = j.succ then (1 : ℤ) else 0) - (if l = Fin.castSucc j then (1 : ℤ) else 0) := by
  simp [delta]

/-- The stoichiometric change of the chain reaction at a piece stream. -/
@[simp] theorem delta_chain_p (ps : Fin (k+1) → Affine d) (j : Fin k) (r : Fin k) :
    delta (minAffineCRN ps) (Sum.inr j) (pSpec (d := d) (k := k) r) = (if r = j then (-1 : ℤ) else 0) := by
  simp [delta]
  by_cases h : r = j <;> simp [h]

/-- The stoichiometric change of the chain reaction at an input species. -/
@[simp] theorem delta_chain_x (ps : Fin (k+1) → Affine d) (j : Fin k) (i : Fin d) :
    delta (minAffineCRN ps) (Sum.inr j) (xSpec (d := d) (k := k) i) = 0 := by
  simp [delta]

/-- If `g x = 0` for `x ≠ a`, then `∑ x, g x * (if x = a then c else 0) = g a * c`. -/
theorem sum_mul_ite_single {ι : Type} [Fintype ι] [DecidableEq ι] (g : ι → ℤ) (a : ι) (c : ℤ) :
    (∑ x, g x * (if x = a then c else 0)) = g a * c := by
  have key : ∀ x, g x * (if x = a then c else 0) = (if x = a then g x * c else 0) := by
    intro x
    by_cases h : x = a <;> simp [h]
  rw [Finset.sum_congr rfl (fun x _ => key x),
    Finset.sum_ite_eq' Finset.univ a (fun x => g x * c)]
  simp

/-- A successor is never `0`. -/
theorem fin_succ_ne_zero' {n : ℕ} (j : Fin n) : (0 : Fin (n+1)) ≠ j.succ := by
  intro h
  have hv : ((0 : Fin (n+1)) : ℕ) = (j.succ : ℕ) := Fin.ext_iff.mp h
  simp at hv

/-- Two successors are equal only if their predecessors are equal. -/
theorem fin_succ_inj {n : ℕ} {a b : Fin n} (h : a.succ = b.succ) : a = b := by
  apply Fin.ext
  have hv : (a.succ : ℕ) = (b.succ : ℕ) := Fin.ext_iff.mp h
  simp only [Fin.val_succ] at hv
  omega

/-- The successor of `j` and `Fin.castSucc j` are different elements. -/
theorem fin_succ_ne_castSucc {n : ℕ} (j : Fin n) : j.succ ≠ Fin.castSucc j := by
  intro h
  have hv : (j.succ : ℕ) = (Fin.castSucc j : ℕ) := Fin.ext_iff.mp h
  simp only [Fin.val_succ, Fin.val_castSucc] at hv
  omega

/-! ## The linear invariants of the pieces -/

/-- The weight of a species for the invariant of the piece `l`: the input species `X_i`
weighs the coefficient of the piece, the accumulators `Z_r` with `r ≥ l` weigh one, and
the piece stream `P_r` weighs one when it carries the piece `l`. -/
def pieceWeight (ps : Fin (k+1) → Affine d) (l : Fin (k+1)) : Species d k → ℤ := fun s =>
  match s with
  | Sum.inl i => (ps l).coeff i
  | Sum.inr (Sum.inl r) => if l ≤ r then 1 else 0
  | Sum.inr (Sum.inr r) => if l = r.succ then 1 else 0

@[simp] theorem pieceWeight_x (ps : Fin (k+1) → Affine d) (l : Fin (k+1)) (i : Fin d) :
    pieceWeight ps l (xSpec (d := d) (k := k) i) = (ps l).coeff i := by
  simp [pieceWeight]

@[simp] theorem pieceWeight_z (ps : Fin (k+1) → Affine d) (l : Fin (k+1)) (r : Fin (k+1)) :
    pieceWeight ps l (zSpec (d := d) (k := k) r) = if l ≤ r then 1 else 0 := by
  simp [pieceWeight]

@[simp] theorem pieceWeight_p (ps : Fin (k+1) → Affine d) (l : Fin (k+1)) (r : Fin k) :
    pieceWeight ps l (pSpec (d := d) (k := k) r) = if l = r.succ then 1 else 0 := by
  simp [pieceWeight]

/-- **The invariant weight of a piece is annihilated by the conversion reaction.** -/
theorem pieceWeight_delta_conv (ps : Fin (k+1) → Affine d) (l : Fin (k+1)) (i : Fin d) :
    wsum (pieceWeight ps l) (delta (minAffineCRN ps) (Sum.inl i)) = 0 := by
  have hX : (∑ j : Fin d, pieceWeight ps l (xSpec (d := d) (k := k) j)
      * delta (minAffineCRN ps) (Sum.inl i) (xSpec (d := d) (k := k) j)) = -((ps l).coeff i : ℤ) := by
    have key : ∀ j : Fin d, pieceWeight ps l (xSpec (d := d) (k := k) j)
        * delta (minAffineCRN ps) (Sum.inl i) (xSpec (d := d) (k := k) j)
        = (if j = i then -((ps l).coeff i : ℤ) else 0) := by
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    rw [Finset.sum_ite_eq' Finset.univ i (fun _ => -((ps l).coeff i : ℤ))]
    simp
  have hZ : (∑ l' : Fin (k+1), pieceWeight ps l (zSpec (d := d) (k := k) l')
      * delta (minAffineCRN ps) (Sum.inl i) (zSpec (d := d) (k := k) l'))
      = (if l = 0 then ((ps 0).coeff i : ℤ) else 0) := by
    have key : ∀ l' : Fin (k+1), pieceWeight ps l (zSpec (d := d) (k := k) l')
        * delta (minAffineCRN ps) (Sum.inl i) (zSpec (d := d) (k := k) l')
        = pieceWeight ps l (zSpec (d := d) (k := k) l')
          * ((if l' = 0 then ((ps 0).coeff i : ℤ) else 0)) := by
      intro l'
      by_cases h : l' = 0 <;> simp [h]
    rw [Finset.sum_congr rfl (fun l' _ => key l')]
    rw [sum_mul_ite_single]
    by_cases hc : l = 0
    · simp [hc]
    · have hn : ¬ (l ≤ 0) := (fin_le_zero_iff l).not.mpr hc
      simp [hc, hn]
  have hP : (∑ r : Fin k, pieceWeight ps l (pSpec (d := d) (k := k) r)
      * delta (minAffineCRN ps) (Sum.inl i) (pSpec (d := d) (k := k) r))
      = (if l = 0 then (0 : ℤ) else ((ps l).coeff i : ℤ)) := by
    by_cases hl : l = 0
    · subst hl
      refine Finset.sum_eq_zero fun r _ => ?_
      have hne : (0 : Fin (k+1)) ≠ r.succ := fin_succ_ne_zero' r
      simp [hne]
    · obtain ⟨r₀, hr₀⟩ := Fin.eq_succ_of_ne_zero hl
      have key : ∀ r : Fin k, pieceWeight ps l (pSpec (d := d) (k := k) r)
          * delta (minAffineCRN ps) (Sum.inl i) (pSpec (d := d) (k := k) r)
          = ((ps (r.succ)).coeff i : ℤ) * ((if r = r₀ then 1 else 0)) := by
        intro r
        by_cases h : r = r₀
        · subst h
          rw [pieceWeight_p, delta_conv_p, hr₀]
          simp
        · have hne : r.succ ≠ r₀.succ := fun h' => h (fin_succ_inj h')
          have hnl : l ≠ r.succ := by rw [hr₀]; exact hne.symm
          rw [pieceWeight_p, delta_conv_p, ite_eq_right hnl, ite_eq_right h]
          simp
      rw [Finset.sum_congr rfl (fun r _ => key r)]
      rw [sum_mul_ite_single]
      simp [hr₀]
  have hsum : (∑ s : Species d k, pieceWeight ps l s
      * delta (minAffineCRN ps) (Sum.inl i) s) = 0 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_sum_type]
    rw [hX, hZ, hP]
    by_cases hl : l = 0
    · subst hl
      simp
    · simp [hl]
  exact hsum

/-- **The invariant weight of a piece is annihilated by the chain reaction.** -/
theorem pieceWeight_delta_chain (ps : Fin (k+1) → Affine d) (l : Fin (k+1)) (j : Fin k) :
    wsum (pieceWeight ps l) (delta (minAffineCRN ps) (Sum.inr j)) = 0 := by
  have hX : (∑ i : Fin d, pieceWeight ps l (xSpec (d := d) (k := k) i)
      * delta (minAffineCRN ps) (Sum.inr j) (xSpec (d := d) (k := k) i)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp
  have hZ : (∑ l' : Fin (k+1), pieceWeight ps l (zSpec (d := d) (k := k) l')
      * delta (minAffineCRN ps) (Sum.inr j) (zSpec (d := d) (k := k) l'))
      = (if l ≤ j.succ then (1 : ℤ) else 0) - (if l ≤ Fin.castSucc j then (1 : ℤ) else 0) := by
    have key : ∀ l' : Fin (k+1), pieceWeight ps l (zSpec (d := d) (k := k) l')
        * delta (minAffineCRN ps) (Sum.inr j) (zSpec (d := d) (k := k) l')
        = pieceWeight ps l (zSpec (d := d) (k := k) l')
          * ((if l' = j.succ then (1 : ℤ) else 0)
            + (if l' = Fin.castSucc j then (-1 : ℤ) else 0)) := by
      intro l'
      by_cases h1 : l' = j.succ
      · subst h1
        have hne : j.succ ≠ Fin.castSucc j := fin_succ_ne_castSucc j
        simp [hne]
      · by_cases h2 : l' = Fin.castSucc j
        · subst h2
          have hne : Fin.castSucc j ≠ j.succ := (fin_succ_ne_castSucc j).symm
          simp [hne]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun l' _ => key l')]
    have key2 : ∀ l' : Fin (k+1),
        pieceWeight ps l (zSpec (d := d) (k := k) l')
          * ((if l' = j.succ then (1 : ℤ) else 0)
            + (if l' = Fin.castSucc j then (-1 : ℤ) else 0))
        = pieceWeight ps l (zSpec (d := d) (k := k) l')
          * ((if l' = j.succ then (1 : ℤ) else 0))
          + pieceWeight ps l (zSpec (d := d) (k := k) l')
          * ((if l' = Fin.castSucc j then (-1 : ℤ) else 0)) := by
      intro l'
      ring
    rw [Finset.sum_congr rfl (fun l' _ => key2 l')]
    rw [Finset.sum_add_distrib]
    rw [sum_mul_ite_single, sum_mul_ite_single]
    simp only [pieceWeight_z]
    ring
  have hP : (∑ r : Fin k, pieceWeight ps l (pSpec (d := d) (k := k) r)
      * delta (minAffineCRN ps) (Sum.inr j) (pSpec (d := d) (k := k) r))
      = (if l = j.succ then (-1 : ℤ) else 0) := by
    have key : ∀ r : Fin k, pieceWeight ps l (pSpec (d := d) (k := k) r)
        * delta (minAffineCRN ps) (Sum.inr j) (pSpec (d := d) (k := k) r)
        = (if l = r.succ then (1 : ℤ) else 0) * ((if r = j then (-1 : ℤ) else 0)) := by
      intro r
      by_cases h : r = j
      · subst h
        simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [sum_mul_ite_single]
    by_cases h : l = j.succ <;> simp [h]
  have hzero : (if l ≤ j.succ then (1 : ℤ) else 0)
      - (if l ≤ Fin.castSucc j then (1 : ℤ) else 0)
      + (if l = j.succ then (-1 : ℤ) else 0) = 0 := by
    by_cases h1 : l ≤ Fin.castSucc j
    · have h2 : l ≤ j.succ := by
        rw [Fin.le_iff_val_le_val]
        simp only [Fin.val_succ]
        have h1' : (l : ℕ) ≤ (j : ℕ) := by
          rw [Fin.le_iff_val_le_val] at h1
          simpa using h1
        omega
      have h3 : l ≠ j.succ := by
        intro hc
        have hv : (l : ℕ) = (j.succ : ℕ) := Fin.ext_iff.mp hc
        simp only [Fin.val_succ] at hv
        have h1' : (l : ℕ) ≤ (j : ℕ) := by
          rw [Fin.le_iff_val_le_val] at h1
          simpa using h1
        omega
      simp [h1, h2, h3]
    · by_cases h2 : l ≤ j.succ
      · have h3 : l = j.succ := by
          apply Fin.ext_iff.mpr
          simp only [Fin.val_succ]
          have h1' : ¬ ((l : ℕ) ≤ (j : ℕ)) := by
            intro hc
            apply h1
            rw [Fin.le_iff_val_le_val]
            simpa using hc
          have h2' : (l : ℕ) ≤ (j : ℕ) + 1 := by
            rw [Fin.le_iff_val_le_val] at h2
            simpa using h2
          omega
        subst h3
        simp
      · have h3 : l ≠ j.succ := by
          intro hc
          have hv : (l : ℕ) = (j.succ : ℕ) := Fin.ext_iff.mp hc
          simp only [Fin.val_succ] at hv
          have h2' : ¬ ((l : ℕ) ≤ (j.succ : ℕ)) := by
            intro hc2
            apply h2
            rw [Fin.le_iff_val_le_val]
            exact hc2
          omega
        simp [h1, h2, h3]
  have hsum : (∑ s : Species d k, pieceWeight ps l s
      * delta (minAffineCRN ps) (Sum.inr j) s) = 0 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_sum_type]
    rw [hX, hZ, hP]
    convert hzero using 1 ; ring
  exact hsum

/-! ### The tail sums of the accumulators -/

/-- The number of molecules in the accumulators `Z_r` with `r ≥ l`. -/
def zTail (n : ℕ) (cz : Fin n → ℕ) (l : ℕ) : ℕ :=
  ∑ r : Fin n, if l ≤ r.val then cz r else 0

@[simp] theorem zTail_zero (n : ℕ) (cz : Fin n → ℕ) : zTail n cz n = 0 := by
  refine Finset.sum_eq_zero fun r _ => ?_
  simp

/-- The tail sum splits off its first term. -/
theorem zTail_succ (n : ℕ) (cz : Fin n → ℕ) {l : ℕ} (hl : l < n) :
    zTail n cz l = cz ⟨l, hl⟩ + zTail n cz (l + 1) := by
  have key : ∀ r : Fin n, (if l ≤ r.val then cz r else 0)
      = (if r = ⟨l, hl⟩ then cz ⟨l, hl⟩ else 0)
        + (if l + 1 ≤ r.val then cz r else 0) := by
    intro r
    by_cases h1 : r = ⟨l, hl⟩
    · subst h1
      simp
    · have hne : r.val ≠ l := by
        intro hc
        apply h1
        exact Fin.ext hc
      by_cases h2 : l ≤ r.val
      · have h3 : l + 1 ≤ r.val := by omega
        rw [ite_eq_left h2, ite_eq_right h1, ite_eq_left h3]
        ring
      · have h3 : ¬ (l + 1 ≤ r.val) := by omega
        rw [ite_eq_right h2, ite_eq_right h1, ite_eq_right h3]
  simp only [zTail]
  rw [Finset.sum_congr rfl (fun r _ => key r)]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin n)) ⟨l, hl⟩ (fun _ => cz ⟨l, hl⟩)]
  simp

/-- The tail sums are decreasing in the index. -/
theorem zTail_le (n : ℕ) (cz : Fin n → ℕ) {l : ℕ} (hl : 0 < l) (hl' : l ≤ n) :
    zTail n cz l ≤ zTail n cz (l - 1) := by
  have h1 : zTail n cz (l - 1) = cz ⟨l - 1, by omega⟩ + zTail n cz l := by
    have hz := zTail_succ (l := l - 1) n cz (by omega)
    rwa [Nat.sub_add_cancel hl] at hz
  omega

/-! ### The invariants in explicit form -/

/-- **The value of the invariant at the initial configuration.**  The weighted sum of the
initial configuration for the weight of the piece `l` is the value of the piece. -/
theorem configSum_pieceInit (ps : Fin (k+1) → Affine d) (l : Fin (k+1)) (x : Fin d → ℕ) :
    configSum (pieceWeight ps l) (minAffineInit ps x) = ((ps l).eval x : ℤ) := by
  have hX : (∑ i : Fin d, pieceWeight ps l (xSpec (d := d) (k := k) i)
      * ((minAffineInit ps x (xSpec (d := d) (k := k) i) : ℤ)))
      = (∑ i, ((ps l).coeff i : ℤ) * (x i : ℤ)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [minAffineInit]
  have hZ : (∑ r : Fin (k+1), pieceWeight ps l (zSpec (d := d) (k := k) r)
      * ((minAffineInit ps x (zSpec (d := d) (k := k) r) : ℤ)))
      = (if l = 0 then ((ps 0).const : ℤ) else 0) := by
    have key : ∀ r : Fin (k+1), pieceWeight ps l (zSpec (d := d) (k := k) r)
        * ((minAffineInit ps x (zSpec (d := d) (k := k) r) : ℤ))
        = pieceWeight ps l (zSpec (d := d) (k := k) r)
          * ((if r = 0 then ((ps 0).const : ℤ) else 0)) := by
      intro r
      simp [minAffineInit]
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [sum_mul_ite_single]
    by_cases hc : l = 0
    · simp [hc]
    · have hn : ¬ (l ≤ 0) := (fin_le_zero_iff l).not.mpr hc
      simp [hc, hn]
  have hP : (∑ r : Fin k, pieceWeight ps l (pSpec (d := d) (k := k) r)
      * ((minAffineInit ps x (pSpec (d := d) (k := k) r) : ℤ)))
      = (if l = 0 then (0 : ℤ) else ((ps l).const : ℤ)) := by
    by_cases hl : l = 0
    · subst hl
      refine Finset.sum_eq_zero fun r _ => ?_
      have hne : (0 : Fin (k+1)) ≠ r.succ := fin_succ_ne_zero' r
      simp [minAffineInit, hne]
    · obtain ⟨r₀, hr₀⟩ := Fin.eq_succ_of_ne_zero hl
      have key : ∀ r : Fin k, pieceWeight ps l (pSpec (d := d) (k := k) r)
          * ((minAffineInit ps x (pSpec (d := d) (k := k) r) : ℤ))
          = ((ps (r.succ)).const : ℤ) * ((if r = r₀ then 1 else 0)) := by
        intro r
        by_cases h : r = r₀
        · subst h
          rw [hr₀]
          simp [minAffineInit]
        · have hne : r.succ ≠ r₀.succ := fun h' => h (fin_succ_inj h')
          have hnl : l ≠ r.succ := by rw [hr₀]; exact hne.symm
          rw [pieceWeight_p, ite_eq_right hnl, ite_eq_right h]
          simp only [minAffineInit]
          ring
      rw [Finset.sum_congr rfl (fun r _ => key r)]
      rw [sum_mul_ite_single]
      simp [hr₀]
  have heval : ((ps l).eval x : ℤ) = ((ps l).const : ℤ) + ∑ i, ((ps l).coeff i : ℤ) * (x i : ℤ) := by
    rw [Affine.eval]
    exact (cast_add_sum_mul_nat'' (ps l).const (ps l).coeff x).symm
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hZ, hP, heval]
  by_cases hl : l = 0
  · subst hl
    simp; ring
  · simp [hl]; ring

/-- **The invariant of the first piece, in explicit form.**  The weighted sum of a
configuration for the weight of the piece `0` is the sum of the contributions of the
input species plus the number of molecules in the accumulators. -/
theorem configSum_piece_zero (ps : Fin (k+1) → Affine d) (c : Config (Species d k)) :
    configSum (pieceWeight ps 0) c
      = (∑ i, ((ps 0).coeff i : ℤ) * (c (xSpec i) : ℤ))
        + ((zTail (k+1) (fun r => c (zSpec r)) 0) : ℤ) := by
  have hX : (∑ i : Fin d, pieceWeight ps 0 (xSpec i) * ((c (xSpec i) : ℤ)))
      = ∑ i, ((ps 0).coeff i : ℤ) * (c (xSpec i) : ℤ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hZ : (∑ r : Fin (k+1), pieceWeight ps 0 (zSpec r) * ((c (zSpec r) : ℤ)))
      = ((zTail (k+1) (fun r => c (zSpec r)) 0) : ℤ) := by
    have key : ∀ r : Fin (k+1), pieceWeight ps 0 (zSpec r) * ((c (zSpec r) : ℤ))
        = ((if (0 : ℕ) ≤ r.val then c (zSpec r) else 0 : ℕ) : ℤ) := by
      intro r
      rw [pieceWeight_z]
      by_cases h : (0 : Fin (k+1)) ≤ r
      · have h' : (0 : ℕ) ≤ r.val := by
          rw [Fin.le_iff_val_le_val] at h
          simpa only [Fin.val_zero] using h
        rw [ite_eq_left h, ite_eq_left h']
        simp
      · have h' : ¬ ((0 : ℕ) ≤ r.val) := by
          intro hc
          apply h
          rw [Fin.le_iff_val_le_val]
          simpa only [Fin.val_zero] using hc
        rw [ite_eq_right h, ite_eq_right h']
        simp
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [← Nat.cast_sum]
    simp only [zTail]
  have hP : (∑ r : Fin k, pieceWeight ps 0 (pSpec r) * ((c (pSpec r) : ℤ))) = 0 := by
    refine Finset.sum_eq_zero fun r _ => ?_
    rw [pieceWeight_p]
    have hne : (0 : Fin (k+1)) ≠ r.succ := fin_succ_ne_zero' r
    rw [ite_eq_right hne]
    simp
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hZ, hP]
  ring

/-- **The invariant of a piece, in explicit form.**  The weighted sum of a configuration
for the weight of the piece `j+1` is the sum of the contributions of the input species
plus the number of molecules in the accumulators `Z_r` with `r ≥ j+1` plus the number of
molecules in the piece stream `P_j`. -/
theorem configSum_piece_succ (ps : Fin (k+1) → Affine d) (j : Fin k)
    (c : Config (Species d k)) :
    configSum (pieceWeight ps j.succ) c
      = (∑ i, ((ps j.succ).coeff i : ℤ) * (c (xSpec i) : ℤ))
        + ((zTail (k+1) (fun r => c (zSpec r)) (j.val + 1)) : ℤ)
        + (c (pSpec j) : ℤ) := by
  have hX : (∑ i : Fin d, pieceWeight ps j.succ (xSpec i) * ((c (xSpec i) : ℤ)))
      = ∑ i, ((ps j.succ).coeff i : ℤ) * (c (xSpec i) : ℤ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hZ : (∑ r : Fin (k+1), pieceWeight ps j.succ (zSpec r) * ((c (zSpec r) : ℤ)))
      = ((zTail (k+1) (fun r => c (zSpec r)) (j.val + 1)) : ℤ) := by
    have key : ∀ r : Fin (k+1), pieceWeight ps j.succ (zSpec r) * ((c (zSpec r) : ℤ))
        = ((if j.val + 1 ≤ r.val then c (zSpec r) else 0 : ℕ) : ℤ) := by
      intro r
      rw [pieceWeight_z]
      by_cases h : j.succ ≤ r
      · have h' : j.val + 1 ≤ r.val := by
          rw [Fin.le_iff_val_le_val] at h
          simpa using h
        rw [ite_eq_left h, ite_eq_left h']
        simp
      · have h' : ¬ (j.val + 1 ≤ r.val) := by
          intro hc
          apply h
          rw [Fin.le_iff_val_le_val]
          simp only [Fin.val_succ]
          omega
        rw [ite_eq_right h, ite_eq_right h']
        simp
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [← Nat.cast_sum]
    simp only [zTail]
  have hP : (∑ r : Fin k, pieceWeight ps j.succ (pSpec r) * ((c (pSpec r) : ℤ)))
      = (c (pSpec j) : ℤ) := by
    have key : ∀ r : Fin k, pieceWeight ps j.succ (pSpec r) * ((c (pSpec r) : ℤ))
        = ((c (pSpec r) : ℤ)) * ((if r = j then 1 else 0)) := by
      intro r
      rw [pieceWeight_p]
      by_cases h : r = j
      · subst h
        simp
      · have hne : ¬ (j.succ = r.succ) := fun h'' => h (fin_succ_inj h''.symm)
        simp [hne, h]
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [sum_mul_ite_single]
    simp
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hZ, hP]
  ring

/-! ### The chain computes the minimum -/

/-- **The running minimum of the chain is the minimum of the piece totals.**  Suppose
that `S l` is the running minimum after the pieces `0, …, l` (so `S 0` is the total of
the first piece), that it is bounded by the total of the next piece, and that it is
either the previous running minimum or the total of the next piece.  Then `S k` is the
minimum of all the totals `A j`. -/
theorem chain_min {k : ℕ} (A : ℕ → ℕ) (S : ℕ → ℕ)
    (hS0 : S 0 = A 0)
    (hle : ∀ j : ℕ, j < k → S (j + 1) ≤ S j ∧ S (j + 1) ≤ A (j + 1))
    (hmin : ∀ j : ℕ, j < k → S (j + 1) = S j ∨ S (j + 1) = A (j + 1)) :
    (∀ j : ℕ, j ≤ k → S k ≤ A j) ∧ (∃ j : ℕ, j ≤ k ∧ S k = A j) := by
  have key : ∀ l : ℕ, l ≤ k →
      (∀ j : ℕ, j ≤ l → S l ≤ A j) ∧ (∃ j : ℕ, j ≤ l ∧ S l = A j) := by
    intro l
    induction l using Nat.strong_induction_on with
    | _ l ih =>
      intro hl
      by_cases h0 : l = 0
      · subst h0
        refine ⟨?_, ⟨0, by omega, hS0⟩⟩
        intro j hj
        have hj0 : j = 0 := by omega
        subst hj0
        simp only [hS0]
        exact le_rfl
      · obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l - 1, by omega⟩
        have hlk : l' < k := by omega
        have hle' := hle l' hlk
        have hmin' := hmin l' hlk
        have hstep : S (l' + 1) = Nat.min (S l') (A (l' + 1)) := by
          rcases hmin' with h | h
          · have h1 : S l' ≤ A (l' + 1) := by
              rw [← h]
              exact hle'.2
            rw [h]
            exact (Nat.min_eq_left h1).symm
          · have h1 : A (l' + 1) ≤ S l' := by
              rw [← h]
              exact hle'.1
            rw [h]
            exact (Nat.min_eq_right h1).symm
        have hprev := ih l' (by omega) (by omega)
        refine ⟨?_, ?_⟩
        · intro j hj'
          by_cases hjeq : j = l' + 1
          · subst hjeq
            exact hle'.2
          · have hj'' : j ≤ l' := by omega
            have h3 := hprev.1 j hj''
            have h4 : S (l' + 1) ≤ S l' := by rw [hstep]; exact Nat.min_le_left _ _
            omega
        · by_cases hjeq : S (l' + 1) = S l'
          · obtain ⟨j, hj'', hval⟩ := hprev.2
            refine ⟨j, by omega, ?_⟩
            rw [hjeq]
            exact hval
          · have h3 : S (l' + 1) = A (l' + 1) := by
              rcases hmin' with h | h
              · exact absurd h hjeq
              · exact h
            refine ⟨l' + 1, by omega, ?_⟩
            rw [h3]
  have hk := key k (by omega)
  exact ⟨hk.1, hk.2⟩

/-! ### The potential -/

/-- The weight of a species for the potential of the network: an input species weighs
`1 + ∑ l, (ps l).coeff i` (the number of molecules it is worth), and every other species
weighs one. -/
def potentialWeight (ps : Fin (k+1) → Affine d) : Species d k → ℤ := fun s =>
  match s with
  | Sum.inl i => ((1 + ∑ l, (ps l).coeff i : ℕ) : ℤ)
  | Sum.inr _ => 1

@[simp] theorem potentialWeight_x (ps : Fin (k+1) → Affine d) (i : Fin d) :
    potentialWeight ps (xSpec (d := d) (k := k) i) = ((1 + ∑ l, (ps l).coeff i : ℕ) : ℤ) := by
  simp [potentialWeight]

@[simp] theorem potentialWeight_z (ps : Fin (k+1) → Affine d) (r : Fin (k+1)) :
    potentialWeight ps (zSpec (d := d) (k := k) r) = 1 := by
  simp [potentialWeight]

@[simp] theorem potentialWeight_p (ps : Fin (k+1) → Affine d) (r : Fin k) :
    potentialWeight ps (pSpec (d := d) (k := k) r) = 1 := by
  simp [potentialWeight]

/-- The potential of the network: the number of molecules that still have to be
processed, counted with their multiplicity. -/
def minAffinePotential (ps : Fin (k+1) → Affine d) (c : Config (Species d k)) : ℕ :=
  ∑ i, (1 + ∑ l, (ps l).coeff i) * c (xSpec i) + ∑ r, c (zSpec r) + ∑ r, c (pSpec r)

/-- The potential is the weighted sum of the configuration. -/
theorem configSum_potential_eq (ps : Fin (k+1) → Affine d) (c : Config (Species d k)) :
    configSum (potentialWeight ps) c = (minAffinePotential ps c : ℤ) := by
  have hX : (∑ i : Fin d, potentialWeight ps (xSpec (d := d) (k := k) i)
      * ((c (xSpec (d := d) (k := k) i) : ℤ)))
      = ((∑ i, (1 + ∑ l, (ps l).coeff i) * c (xSpec i) : ℕ) : ℤ) := by
    have key : ∀ i : Fin d, potentialWeight ps (xSpec (d := d) (k := k) i)
        * ((c (xSpec (d := d) (k := k) i) : ℤ))
        = (((1 + ∑ l, (ps l).coeff i) * c (xSpec i) : ℕ) : ℤ) := by
      intro i
      simp only [potentialWeight_x]
      exact (Nat.cast_mul _ _).symm
    rw [Finset.sum_congr rfl (fun i _ => key i)]
    rw [← Nat.cast_sum]
  have hZ : (∑ r : Fin (k+1), potentialWeight ps (zSpec (d := d) (k := k) r)
      * ((c (zSpec (d := d) (k := k) r) : ℤ)))
      = ((∑ r, c (zSpec r) : ℕ) : ℤ) := by
    have key : ∀ r : Fin (k+1), potentialWeight ps (zSpec (d := d) (k := k) r)
        * ((c (zSpec (d := d) (k := k) r) : ℤ)) = ((c (zSpec r) : ℕ) : ℤ) := by
      intro r
      simp only [potentialWeight_z]
      simp
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [← Nat.cast_sum]
  have hP : (∑ r : Fin k, potentialWeight ps (pSpec (d := d) (k := k) r)
      * ((c (pSpec (d := d) (k := k) r) : ℤ)))
      = ((∑ r, c (pSpec r) : ℕ) : ℤ) := by
    have key : ∀ r : Fin k, potentialWeight ps (pSpec (d := d) (k := k) r)
        * ((c (pSpec (d := d) (k := k) r) : ℤ)) = ((c (pSpec r) : ℕ) : ℤ) := by
      intro r
      simp only [potentialWeight_p]
      simp
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [← Nat.cast_sum]
  have hcast : ((minAffinePotential ps c : ℕ) : ℤ)
      = ((∑ i, (1 + ∑ l, (ps l).coeff i) * c (xSpec i) : ℕ) : ℤ)
        + ((∑ r, c (zSpec r) : ℕ) : ℤ) + ((∑ r, c (pSpec r) : ℕ) : ℤ) := by
    simp only [minAffinePotential, Nat.cast_add, Nat.cast_sum]
  simp only [configSum, wsum, Fintype.sum_sum_type, Fintype.sum_sum_type]
  rw [hX, hZ, hP, hcast]
  ring

/-- The sum of the coefficients of the pieces, over the successors of a `Fin k`. -/
theorem sum_succ_eq (f : Fin (k+1) → ℤ) : (∑ r : Fin k, f r.succ) = (∑ l : Fin (k+1), f l) - f 0 := by
  have h := Fin.sum_univ_succ (M := ℤ) (f := f)
  rw [show (∑ l : Fin (k+1), f l) = f 0 + ∑ r : Fin k, f r.succ from h]
  rw [add_sub_cancel_left]

/-- **The potential decreases by one at every conversion reaction.** -/
theorem potentialWeight_delta_conv (ps : Fin (k+1) → Affine d) (i : Fin d) :
    wsum (potentialWeight ps) (delta (minAffineCRN ps) (Sum.inl i)) = -1 := by
  have hX : (∑ j : Fin d, potentialWeight ps (xSpec (d := d) (k := k) j)
      * delta (minAffineCRN ps) (Sum.inl i) (xSpec (d := d) (k := k) j))
      = -((1 + ∑ l, (ps l).coeff i : ℕ) : ℤ) := by
    have key : ∀ j : Fin d, potentialWeight ps (xSpec (d := d) (k := k) j)
        * delta (minAffineCRN ps) (Sum.inl i) (xSpec (d := d) (k := k) j)
        = (if j = i then -((1 + ∑ l, (ps l).coeff i : ℕ) : ℤ) else 0) := by
      intro j
      by_cases h : j = i
      · subst h
        simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun j _ => key j)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin d)) i
      (fun _ => -((1 + ∑ l, (ps l).coeff i : ℕ) : ℤ))]
    simp
  have hZ : (∑ r : Fin (k+1), potentialWeight ps (zSpec (d := d) (k := k) r)
      * delta (minAffineCRN ps) (Sum.inl i) (zSpec (d := d) (k := k) r))
      = ((ps 0).coeff i : ℤ) := by
    have key : ∀ r : Fin (k+1), potentialWeight ps (zSpec (d := d) (k := k) r)
        * delta (minAffineCRN ps) (Sum.inl i) (zSpec (d := d) (k := k) r)
        = (if r = 0 then ((ps 0).coeff i : ℤ) else 0) := by
      intro r
      simp only [potentialWeight_z]
      by_cases h : r = 0
      · subst h
        simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin (k+1))) 0
      (fun _ => ((ps 0).coeff i : ℤ))]
    simp
  have hP : (∑ r : Fin k, potentialWeight ps (pSpec (d := d) (k := k) r)
      * delta (minAffineCRN ps) (Sum.inl i) (pSpec (d := d) (k := k) r))
      = (∑ l : Fin (k+1), ((ps l).coeff i : ℤ)) - ((ps 0).coeff i : ℤ) := by
    have key : ∀ r : Fin k, potentialWeight ps (pSpec (d := d) (k := k) r)
        * delta (minAffineCRN ps) (Sum.inl i) (pSpec (d := d) (k := k) r)
        = ((ps (r.succ)).coeff i : ℤ) := by
      intro r
      simp [potentialWeight_p]
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    exact sum_succ_eq (fun l => ((ps l).coeff i : ℤ))
  have hsum : (∑ s : Species d k, potentialWeight ps s
      * delta (minAffineCRN ps) (Sum.inl i) s) = -1 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_sum_type]
    rw [hX, hZ, hP]
    have hcof : (∑ l : Fin (k+1), ((ps l).coeff i : ℤ))
        = ((ps 0).coeff i : ℤ)
          + ((∑ l : Fin (k+1), ((ps l).coeff i : ℤ)) - ((ps 0).coeff i : ℤ)) := by
      ring
    rw [hcof]
    have hcast : ((1 + ∑ l, (ps l).coeff i : ℕ) : ℤ)
        = 1 + (∑ l : Fin (k+1), ((ps l).coeff i : ℤ)) := by
      simp [Nat.cast_add, Nat.cast_sum]
    rw [hcast]
    ring
  exact hsum

/-- **The potential decreases by one at every chain reaction.** -/
theorem potentialWeight_delta_chain (ps : Fin (k+1) → Affine d) (j : Fin k) :
    wsum (potentialWeight ps) (delta (minAffineCRN ps) (Sum.inr j)) = -1 := by
  have hX : (∑ i : Fin d, potentialWeight ps (xSpec (d := d) (k := k) i)
      * delta (minAffineCRN ps) (Sum.inr j) (xSpec (d := d) (k := k) i)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    simp
  have hZ : (∑ r : Fin (k+1), potentialWeight ps (zSpec (d := d) (k := k) r)
      * delta (minAffineCRN ps) (Sum.inr j) (zSpec (d := d) (k := k) r)) = 0 := by
    have key : ∀ r : Fin (k+1), potentialWeight ps (zSpec (d := d) (k := k) r)
        * delta (minAffineCRN ps) (Sum.inr j) (zSpec (d := d) (k := k) r)
        = (if r = j.succ then (1 : ℤ) else 0)
          + (if r = Fin.castSucc j then (-1 : ℤ) else 0) := by
      intro r
      simp only [potentialWeight_z]
      by_cases h1 : r = j.succ
      · subst h1
        have hne : j.succ ≠ Fin.castSucc j := fin_succ_ne_castSucc j
        simp [hne]
      · by_cases h2 : r = Fin.castSucc j
        · subst h2
          have hne : Fin.castSucc j ≠ j.succ := (fin_succ_ne_castSucc j).symm
          simp [hne]
        · simp [h1, h2]
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin (k+1))) j.succ (fun _ => (1 : ℤ))]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin (k+1))) (Fin.castSucc j) (fun _ => (-1 : ℤ))]
    simp
  have hP : (∑ r : Fin k, potentialWeight ps (pSpec (d := d) (k := k) r)
      * delta (minAffineCRN ps) (Sum.inr j) (pSpec (d := d) (k := k) r)) = -1 := by
    have key : ∀ r : Fin k, potentialWeight ps (pSpec (d := d) (k := k) r)
        * delta (minAffineCRN ps) (Sum.inr j) (pSpec (d := d) (k := k) r)
        = (if r = j then (-1 : ℤ) else 0) := by
      intro r
      simp only [potentialWeight_p]
      by_cases h : r = j
      · subst h
        simp
      · simp [h]
    rw [Finset.sum_congr rfl (fun r _ => key r)]
    rw [Finset.sum_ite_eq' (Finset.univ : Finset (Fin k)) j (fun _ => (-1 : ℤ))]
    simp
  have hsum : (∑ s : Species d k, potentialWeight ps s
      * delta (minAffineCRN ps) (Sum.inr j) s) = -1 := by
    simp only [Fintype.sum_sum_type, Fintype.sum_sum_type]
    rw [hX, hZ, hP]
    ring
  exact hsum

/-! ### Applicability of the reactions -/

/-- The conversion reaction for the input `i` is applicable exactly when there is a
molecule of the input species `X_i`. -/
theorem conv_applicable (ps : Fin (k+1) → Affine d) (i : Fin d) (c : Config (Species d k)) :
    Applicable (minAffineCRN ps) (Sum.inl i) c ↔ 1 ≤ c (xSpec (d := d) (k := k) i) := by
  constructor
  · intro h
    have hh : convSource i (xSpec (d := d) (k := k) i) ≤ c (xSpec (d := d) (k := k) i) :=
      h (xSpec (d := d) (k := k) i)
    simp [convSource_x] at hh
    omega
  · intro h s
    have hr : (minAffineCRN ps).reaction (Sum.inl i) = ⟨convSource i, convTarget ps i⟩ := rfl
    rw [hr]
    show (convSource i s : ℕ) ≤ c s
    cases s with
    | inl j =>
      by_cases hj : j = i
      · rw [hj]
        have hz : (convSource i (xSpec (d := d) (k := k) i) : ℕ) = 1 := by
          simp [convSource_x]
        rw [hz]
        exact h
      · have hz : (convSource i (xSpec (d := d) (k := k) j) : ℕ) = 0 := by
          simp [convSource_x, hj]
        rw [hz]
        exact Nat.zero_le _
    | inr sr =>
      cases sr with
      | inl r => simp [convSource_z]
      | inr r => simp [convSource_p]

/-- The chain reaction `j` is applicable exactly when there is a molecule of the
accumulator `Z_j` and a molecule of the piece stream `P_j`. -/
theorem chain_applicable (ps : Fin (k+1) → Affine d) (j : Fin k) (c : Config (Species d k)) :
    Applicable (minAffineCRN ps) (Sum.inr j) c ↔
      1 ≤ c (zSpec (d := d) (k := k) (Fin.castSucc j)) ∧ 1 ≤ c (pSpec (d := d) (k := k) j) := by
  constructor
  · intro h
    have h1 : chainSource j (zSpec (d := d) (k := k) (Fin.castSucc j))
        ≤ c (zSpec (d := d) (k := k) (Fin.castSucc j)) :=
      h (zSpec (d := d) (k := k) (Fin.castSucc j))
    have h2 : chainSource j (pSpec (d := d) (k := k) j) ≤ c (pSpec (d := d) (k := k) j) :=
      h (pSpec (d := d) (k := k) j)
    simp [chainSource_z, chainSource_p] at h1 h2
    exact ⟨h1, h2⟩
  · intro h s
    have hr : (minAffineCRN ps).reaction (Sum.inr j) = ⟨chainSource j, chainTarget j⟩ := rfl
    rw [hr]
    show (chainSource j s : ℕ) ≤ c s
    cases s with
    | inl j' => simp [chainSource_x]
    | inr sr =>
      cases sr with
      | inl r =>
        by_cases hr' : r = Fin.castSucc j
        · rw [hr']
          have hz : (chainSource j (zSpec (d := d) (k := k) (Fin.castSucc j)) : ℕ) = 1 := by
            simp [chainSource_z]
          rw [hz]
          exact h.1
        · have hz : (chainSource j (zSpec (d := d) (k := k) r) : ℕ) = 0 := by
            simp [chainSource_z, hr']
          rw [hz]
          exact Nat.zero_le _
      | inr r =>
        by_cases hr' : r = j
        · rw [hr']
          have hp : (chainSource j (pSpec (d := d) (k := k) j) : ℕ) = 1 := by
            simp [chainSource_p]
          rw [hp]
          exact h.2
        · have hp : (chainSource j (pSpec (d := d) (k := k) r) : ℕ) = 0 := by
            simp [chainSource_p, hr']
          rw [hp]
          exact Nat.zero_le _

/-- The last tail sum consists of the last accumulator only. -/
theorem zTail_top (cz : Fin (k+1) → ℕ) : zTail (k+1) cz k = cz ⟨k, by omega⟩ := by
  have h1 : zTail (k+1) cz k = cz ⟨k, by omega⟩ + zTail (k+1) cz (k + 1) :=
    zTail_succ (n := k+1) (cz := cz) (l := k) (by omega)
  rw [zTail_zero] at h1
  omega

/-- The value of the piece `j` (for `j ≤ k`). -/
def pieceVal {d k : ℕ} (ps : Fin (k+1) → Affine d) (x : Fin d → ℕ) (j : ℕ) : ℕ :=
  if hj : j ≤ k then (ps ⟨j, Nat.lt_succ_of_le hj⟩).eval x else 0

/-! ### The main theorem -/

/-- **The minimum of finitely many affine functions is stably computable.**

The network `minAffineCRN ps` stably computes `minAffineVal ps`, the pointwise minimum
of the affine maps `ps 0, …, ps k`.  The proof has two parts.

* The network *terminates*: the potential `minAffinePotential` decreases by one at every
  reaction (see `potentialWeight_delta_conv` and `potentialWeight_delta_chain`).
* At a terminal configuration, the content of the output species `Z_k` is the minimum of
  the piece totals.  This is where the linear invariants enter: for each piece `l` the
  weight `pieceWeight ps l` is annihilated by every reaction, so the weighted sum of the
  configuration is constant along a run; at a terminal configuration this weighted sum
  says that the running minimum of the chain is the minimum of the piece totals
  (`chain_min`). -/
theorem minAffineCRN_stablyComputes (ps : Fin (k+1) → Affine d) :
    StablyComputes (minAffineCRN ps) (minAffineInit ps) (minAffineOut k) (minAffineVal ps) := by
  refine stablyComputes_of_terminating _ _ _ _ (minAffinePotential ps) ?_ ?_
  · rintro c c' ⟨r, hr, rfl⟩
    cases r with
    | inl i =>
      have hdec := configSum_fire (minAffineCRN ps) (potentialWeight ps) (Sum.inl i) c hr
      have h1 := configSum_potential_eq ps c
      have h2 := configSum_potential_eq ps (fire (minAffineCRN ps) (Sum.inl i) c)
      rw [h1, h2] at hdec
      rw [potentialWeight_delta_conv ps i] at hdec
      have hlt : ((minAffinePotential ps (fire (minAffineCRN ps) (Sum.inl i) c) : ℤ))
          < ((minAffinePotential ps c : ℤ)) := by omega
      exact Int.ofNat_lt.mp hlt
    | inr j =>
      have hdec := configSum_fire (minAffineCRN ps) (potentialWeight ps) (Sum.inr j) c hr
      have h1 := configSum_potential_eq ps c
      have h2 := configSum_potential_eq ps (fire (minAffineCRN ps) (Sum.inr j) c)
      rw [h1, h2] at hdec
      rw [potentialWeight_delta_chain ps j] at hdec
      have hlt : ((minAffinePotential ps (fire (minAffineCRN ps) (Sum.inr j) c) : ℤ))
          < ((minAffinePotential ps c : ℤ)) := by omega
      exact Int.ofNat_lt.mp hlt
  · intro x c hc hterm
    -- (1) at a terminal configuration all the input species are empty
    have hX : ∀ i : Fin d, c (xSpec (d := d) (k := k) i) = 0 := by
      intro i
      have hne : ¬ (1 ≤ c (xSpec (d := d) (k := k) i)) := by
        intro h
        exact hterm (Sum.inl i) ((conv_applicable ps i c).mpr h)
      omega
    -- (2) the invariants of the pieces
    have hInv0 : configSum (pieceWeight ps 0) c = ((ps 0).eval x : ℤ) := by
      rw [configSum_invariant (minAffineCRN ps) (pieceWeight ps 0)
        (fun r => by cases r with
          | inl i => exact pieceWeight_delta_conv ps 0 i
          | inr j => exact pieceWeight_delta_chain ps 0 j) hc]
      exact configSum_pieceInit ps 0 x
    have hInvS : ∀ j : Fin k, configSum (pieceWeight ps j.succ) c = ((ps j.succ).eval x : ℤ) := by
      intro j
      rw [configSum_invariant (minAffineCRN ps) (pieceWeight ps j.succ)
        (fun r => by cases r with
          | inl i => exact pieceWeight_delta_conv ps j.succ i
          | inr j' => exact pieceWeight_delta_chain ps j.succ j') hc]
      exact configSum_pieceInit ps j.succ x
    -- (3) the terminal conditions of the chain reactions
    have hTerm2 : ∀ j : Fin k, c (zSpec (d := d) (k := k) (Fin.castSucc j)) = 0
        ∨ c (pSpec (d := d) (k := k) j) = 0 := by
      intro j
      have hnotapp : ¬ Applicable (minAffineCRN ps) (Sum.inr j) c := hterm (Sum.inr j)
      by_cases h1 : c (zSpec (d := d) (k := k) (Fin.castSucc j)) = 0
      · exact Or.inl h1
      · refine Or.inr ?_
        by_contra h2
        have hp : 1 ≤ c (pSpec (d := d) (k := k) j) := by omega
        have hz1 : 1 ≤ c (zSpec (d := d) (k := k) (Fin.castSucc j)) := by omega
        exact hnotapp ((chain_applicable ps j c).mpr ⟨hz1, hp⟩)
    -- (4) the running minimum of the chain
    have hS0 : zTail (k+1) (fun r => c (zSpec r)) 0 = (ps 0).eval x := by
      have h := configSum_piece_zero ps c
      rw [hInv0] at h
      have hz : (∑ i, ((ps 0).coeff i : ℤ) * (c (xSpec i) : ℤ)) = 0 := by
        simp [hX]
      rw [hz] at h
      omega
    have hSj : ∀ j : Fin k, zTail (k+1) (fun r => c (zSpec r)) (j.val + 1) + c (pSpec j)
        = (ps j.succ).eval x := by
      intro j
      have h := configSum_piece_succ ps j c
      rw [hInvS j] at h
      have hz : (∑ i, ((ps j.succ).coeff i : ℤ) * (c (xSpec i) : ℤ)) = 0 := by
        simp [hX]
      rw [hz] at h
      omega
    have hsplit : ∀ j : Fin k,
        zTail (k+1) (fun r => c (zSpec r)) j.val
          = c (zSpec (d := d) (k := k) (Fin.castSucc j))
            + zTail (k+1) (fun r => c (zSpec r)) (j.val + 1) := by
      intro j
      have hz := zTail_succ (n := k+1) (cz := fun r => c (zSpec r)) (l := j.val) (by omega)
      convert hz using 1 ; rfl
    have hle : ∀ j : Fin k,
        zTail (k+1) (fun r => c (zSpec r)) (j.val + 1) ≤ zTail (k+1) (fun r => c (zSpec r)) j.val
          ∧ zTail (k+1) (fun r => c (zSpec r)) (j.val + 1) ≤ pieceVal ps x (j.val + 1) := by
      intro j
      have hsplit' := hsplit j
      have hbound : zTail (k+1) (fun r => c (zSpec r)) (j.val + 1) ≤ pieceVal ps x (j.val + 1) := by
        have h := hSj j
        have hjle : j.val + 1 ≤ k := by omega
        have hz : pieceVal ps x (j.val + 1) = (ps j.succ).eval x := by
          simp only [pieceVal, dite_eq_left hjle]
          rfl
        rw [hz]
        omega
      refine ⟨by omega, hbound⟩
    have hmin : ∀ j : Fin k,
        zTail (k+1) (fun r => c (zSpec r)) (j.val + 1) = zTail (k+1) (fun r => c (zSpec r)) j.val
          ∨ zTail (k+1) (fun r => c (zSpec r)) (j.val + 1) = pieceVal ps x (j.val + 1) := by
      intro j
      rcases hTerm2 j with h1 | h2
      · left
        have hsplit' := hsplit j
        omega
      · right
        have h := hSj j
        have hjle : j.val + 1 ≤ k := by omega
        have hz : pieceVal ps x (j.val + 1) = (ps j.succ).eval x := by
          simp only [pieceVal, dite_eq_left hjle]
          rfl
        rw [hz]
        omega
    have hle' : ∀ j : ℕ, j < k →
        zTail (k+1) (fun r => c (zSpec r)) (j + 1) ≤ zTail (k+1) (fun r => c (zSpec r)) j
          ∧ zTail (k+1) (fun r => c (zSpec r)) (j + 1) ≤ pieceVal ps x (j + 1) := by
      intro j hj
      exact hle ⟨j, hj⟩
    have hmin' : ∀ j : ℕ, j < k →
        zTail (k+1) (fun r => c (zSpec r)) (j + 1) = zTail (k+1) (fun r => c (zSpec r)) j
          ∨ zTail (k+1) (fun r => c (zSpec r)) (j + 1) = pieceVal ps x (j + 1) := by
      intro j hj
      exact hmin ⟨j, hj⟩
    have hchain := chain_min (k := k) (pieceVal ps x)
      (fun l => zTail (k+1) (fun r => c (zSpec r)) l)
      (by simpa [pieceVal] using hS0) hle' hmin'
    -- (5) the output of the terminal configuration
    have hout : c (minAffineOut k) = zTail (k+1) (fun r => c (zSpec r)) k := by
      simp only [minAffineOut]
      rw [zTail_top (cz := fun r => c (zSpec r))]
    rw [hout]
    -- (6) the running minimum is the minimum of the piece totals
    have hval : zTail (k+1) (fun r => c (zSpec r)) k = minAffineVal ps x := by
      apply eq_finsetMin_of_le_and_mem
      · intro l
        have h := hchain.1 l.val (by omega)
        have hjle : l.val ≤ k := by omega
        simp only [pieceVal, dite_eq_left hjle] at h
        exact h
      · obtain ⟨j, hj, hval⟩ := hchain.2
        refine ⟨⟨j, by omega⟩, ?_⟩
        have hjle : j ≤ k := by omega
        simp only [pieceVal, dite_eq_left hjle] at hval
        exact hval
    exact hval

/-! ### Corollaries -/

/-- **The minimum of two affine functions is stably computable.**  This is the case of two
pieces (`k = 1`) of the main theorem: the pointwise minimum of two affine maps
`ℕ^d → ℕ` is computed by a stable computation. -/
theorem minTwoAffineCRN_stablyComputes {d : ℕ} (p q : Affine d) :
    StablyComputes (minAffineCRN (d := d) (k := 1) (fun | 0 => p | 1 => q))
      (minAffineInit (d := d) (k := 1) (fun | 0 => p | 1 => q))
      (minAffineOut (d := d) 1)
      (minAffineVal (d := d) (k := 1) (fun | 0 => p | 1 => q)) := by
  exact minAffineCRN_stablyComputes (d := d) (k := 1) (fun | 0 => p | 1 => q)

/-- The minimum of a list of natural numbers. -/
def listMin : List ℕ → ℕ
  | [] => 0
  | x :: xs => Nat.min x (listMin xs)

/-- **The minimum of a list of affine functions is piecewiseNatAffine.**  Together with the main
theorem this says that the functions realized here are exactly of the piecewiseNatAffine kind
expected in leaf C2: they are minima of affine maps, hence piecewiseNatAffine in the sense of
`CRNT.Computation.PiecewiseNatAffine`, and they are stably computable. -/
theorem minList_piecewiseNatAffine {d : ℕ} : ∀ (ps : List (Affine d)),
    PiecewiseNatAffine (fun x => listMin (ps.map (fun A => A.eval x))) := by
  intro ps
  induction ps with
  | nil =>
    have h : (fun x => listMin (([] : List (Affine d)).map (fun A => A.eval x))) = (fun _ => 0) := by
      funext x
      rfl
    rw [h]
    simpa using (piecewiseNatAffine_of_affine 0 (fun _ => 0))
  | cons A ps ih =>
    have h1 : PiecewiseNatAffine (fun x => A.eval x) := piecewiseNatAffine_of_affine A.const A.coeff
    have h2 : PiecewiseNatAffine (fun x => listMin (ps.map (fun B => B.eval x))) := ih
    have h3 : PiecewiseNatAffine (fun x => Nat.min (A.eval x) (listMin (ps.map (fun B => B.eval x)))) :=
      PiecewiseNatAffine.min h1 h2
    simpa only [List.map_cons, listMin] using h3

end MinAffine

end Computation

end CRNT
