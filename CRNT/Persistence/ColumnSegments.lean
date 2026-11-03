import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.List.Chain
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Column segments of a blueprint

One column of the blueprint over a base point: a *section* segment `[v - w, v + w]` around each
section value `v` (the first one is the wall value), the gaps between them cut into *band*
pieces of length at most `ℓ`, and a final unbounded *top* segment starting at `T⋆`.

`colSegs w ℓ T vs` builds the list; `chain_colSegs` proves the consecutive segments abut
(`hi = lo'`) with strictly increasing basepoints, and the membership lemmas record what each
kind of segment satisfies.  Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

inductive SegKind | sec | band | top
  deriving DecidableEq

structure Seg where
  lo : ℝ
  β : ℝ
  hi : ℝ
  kind : SegKind

/-- Equal pieces of `[a, b]`, each of length at most `ℓ`. -/
noncomputable def piece (a h : ℝ) (k : ℕ) : Seg :=
  ⟨a + (k : ℝ) * h, a + ((k : ℝ) + 1 / 2) * h, a + ((k : ℝ) + 1) * h, SegKind.band⟩

/-- Equal pieces of `[a, b]`, each of length at most `ℓ`. -/
noncomputable def bandSegs (a b ℓ : ℝ) : List Seg :=
  (List.range ⌈(b - a) / ℓ⌉₊).map (piece a ((b - a) / ⌈(b - a) / ℓ⌉₊))

/-- The column, given the increasing list of section values (head = wall value). -/
noncomputable def colSegs (w ℓ T : ℝ) : List ℝ → List Seg
  | [] => [⟨T, T + 1, T + 2, SegKind.top⟩]
  | [v] => ⟨v - w, v, v + w, SegKind.sec⟩ :: (bandSegs (v + w) T ℓ ++
      [⟨T, T + 1, T + 2, SegKind.top⟩])
  | v :: v' :: vs => ⟨v - w, v, v + w, SegKind.sec⟩ :: (bandSegs (v + w) (v' - w) ℓ ++
      colSegs w ℓ T (v' :: vs))

/-- The relation between consecutive segments. -/
def SegRel (s s' : Seg) : Prop := s.hi = s'.lo ∧ s.β ≤ s.hi ∧ s.hi ≤ s'.β ∧ s.β < s'.β

/-- The properties of the band pieces of `[a, b]` with `a ≤ b`. -/
theorem bandSegs_mem {a b ℓ : ℝ} (hab : a ≤ b) (hℓ : 0 < ℓ) :
    ∀ s ∈ bandSegs a b ℓ, s.kind = SegKind.band ∧ a ≤ s.lo ∧ s.lo < s.β ∧ s.β < s.hi ∧
      s.hi ≤ b ∧ s.hi - s.lo ≤ ℓ ∧ 2 * s.β = s.lo + s.hi := by
  intro s hs
  simp only [bandSegs, List.mem_map, List.mem_range] at hs
  obtain ⟨k, hk, rfl⟩ := hs
  set N := ⌈(b - a) / ℓ⌉₊ with hNdef
  have hNpos : 0 < N := lt_of_le_of_lt (Nat.zero_le k) hk
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hab' : a < b := by
    rcases hab.lt_or_eq with h | h
    · exact h
    · exfalso; rw [hNdef, h, sub_self, zero_div, Nat.ceil_zero] at hNpos; omega
  set h := (b - a) / N with hhdef
  have hh : 0 < h := div_pos (by linarith) hNr
  have hkN : (k : ℝ) + 1 ≤ N := by exact_mod_cast hk
  have hNge : (b - a) / ℓ ≤ N := Nat.le_ceil _
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
  have hNh : (N : ℝ) * h = b - a := by rw [hhdef]; field_simp
  simp only [piece]
  refine ⟨by simp, by nlinarith, by nlinarith, by nlinarith, by nlinarith, ?_, by ring⟩
  have e : a + ((k : ℝ) + 1) * h - (a + (k : ℝ) * h) = h := by ring
  rw [e, hhdef, div_le_iff₀ hNr]; rw [div_le_iff₀ hℓ] at hNge; linarith

theorem bandSegs_chain (a b ℓ : ℝ) (hab : a ≤ b) (hℓ : 0 < ℓ) :
    List.IsChain SegRel (bandSegs a b ℓ) := by
  rw [List.isChain_iff_getElem]
  intro i hi
  have hmem := bandSegs_mem hab hℓ
  simp only [bandSegs, List.length_map, List.length_range] at hi
  set N := ⌈(b - a) / ℓ⌉₊ with hNdef
  have hNpos : 0 < N := by omega
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hab' : a < b := by
    rcases hab.lt_or_eq with h | h
    · exact h
    · exfalso; rw [hNdef, h, sub_self, zero_div, Nat.ceil_zero] at hNpos; omega
  have hh : 0 < (b - a) / N := div_pos (by linarith) hNr
  simp only [bandSegs, List.getElem_map, List.getElem_range, SegRel, piece]
  push_cast
  refine ⟨by ring, by nlinarith, by nlinarith, by nlinarith⟩

theorem bandSegs_head {a b ℓ : ℝ} : ∀ s ∈ (bandSegs a b ℓ).head?, s.lo = a := by
  intro s hs
  rw [bandSegs, List.head?_map, List.head?_range] at hs
  by_cases h0 : ⌈(b - a) / ℓ⌉₊ = 0
  · simp [h0] at hs
  · simp only [h0, if_false, Option.map_some, Option.mem_def, Option.some.injEq] at hs
    subst hs; simp [piece]

theorem bandSegs_last {a b ℓ : ℝ} : ∀ s ∈ (bandSegs a b ℓ).getLast?, s.hi = b := by
  intro s hs
  rw [bandSegs, List.getLast?_map, List.getLast?_range] at hs
  by_cases h0 : ⌈(b - a) / ℓ⌉₊ = 0
  · simp [h0] at hs
  · simp only [h0, if_false, Option.map_some, Option.mem_def, Option.some.injEq] at hs
    subst hs
    have hNr : (⌈(b - a) / ℓ⌉₊ : ℝ) ≠ 0 := by exact_mod_cast h0
    simp only [piece]
    rw [Nat.cast_sub (by omega)]; push_cast; field_simp; ring

theorem bandSegs_ne_nil {a b ℓ : ℝ} (hab : a < b) (hℓ : 0 < ℓ) : bandSegs a b ℓ ≠ [] := by
  simp only [bandSegs, ne_eq, List.map_eq_nil_iff, List.range_eq_nil]
  exact (Nat.ceil_pos.mpr (div_pos (by linarith) hℓ)).ne'

theorem bandSegs_eq_nil {a ℓ : ℝ} : bandSegs a a ℓ = [] := by simp [bandSegs]

/-- The top segment. -/
def topSeg (T : ℝ) : Seg := ⟨T, T + 1, T + 2, SegKind.top⟩

/-- A section segment. -/
def secSeg (w v : ℝ) : Seg := ⟨v - w, v, v + w, SegKind.sec⟩

theorem colSegs_cons (w ℓ T v : ℝ) (vs : List ℝ) :
    colSegs w ℓ T (v :: vs) = secSeg w v :: (match vs with
      | [] => bandSegs (v + w) T ℓ ++ [topSeg T]
      | v' :: _ => bandSegs (v + w) (v' - w) ℓ ++ colSegs w ℓ T vs) := by
  cases vs <;> rfl

/-- The column is a section segment, followed by a chain, ending in the top segment. -/
theorem colSegs_props (w ℓ T : ℝ) (hw : 0 < w) (hℓ : 0 < ℓ) :
    ∀ (v : ℝ) (vs : List ℝ), List.IsChain (fun a b => a + 4 * w ≤ b) (v :: vs) →
      (v :: vs).getLast (by simp) + w ≤ T →
      List.IsChain SegRel (colSegs w ℓ T (v :: vs)) ∧
      (colSegs w ℓ T (v :: vs)).head? = some (secSeg w v) ∧
      (∃ L, colSegs w ℓ T (v :: vs) = L ++ [topSeg T] ∧ ∀ s ∈ L, s.kind ≠ SegKind.top) ∧
      (∀ s ∈ colSegs w ℓ T (v :: vs), s.kind = SegKind.sec →
        s.β ∈ v :: vs ∧ s.lo = s.β - w ∧ s.hi = s.β + w) ∧
      (∀ s ∈ colSegs w ℓ T (v :: vs), s.kind = SegKind.band →
        v + w ≤ s.lo ∧ s.lo < s.β ∧ s.β < s.hi ∧ s.hi ≤ T ∧ s.hi - s.lo ≤ ℓ ∧
        2 * s.β = s.lo + s.hi ∧ (∀ z ∈ v :: vs, w ≤ |s.β - z|) ∧
        (s.hi + w ≤ (v :: vs).getLast (by simp) ∨ (v :: vs).getLast (by simp) + w ≤ s.lo)) ∧
      (∀ s ∈ colSegs w ℓ T (v :: vs), v ≤ s.β) := by
  intro v vs
  induction vs generalizing v with
  | nil =>
      intro _ hlast
      simp only [List.getLast_singleton] at hlast
      have hab : v + w ≤ T := hlast
      rw [colSegs_cons]
      simp only
      have hbm := bandSegs_mem hab hℓ
      refine ⟨?_, rfl, ⟨secSeg w v :: bandSegs (v + w) T ℓ, by simp, ?_⟩, ?_, ?_, ?_⟩
      · -- chain
        refine List.IsChain.cons ?_ ?_
        · refine List.IsChain.append (bandSegs_chain _ _ _ hab hℓ) (List.isChain_singleton _) ?_
          intro x hx y hy
          simp at hy; subst hy
          have hxm := hbm x (List.mem_of_getLast? hx)
          have hxhi := bandSegs_last x hx
          simp only [SegRel, topSeg]; refine ⟨hxhi, by linarith, by linarith, by linarith⟩
        · intro y hy
          rcases hab.lt_or_eq with hlt | heq
          · have hne := bandSegs_ne_nil hlt hℓ
            rw [List.head?_append_of_ne_nil _ hne] at hy
            have hylo := bandSegs_head y hy
            have hym := hbm y (List.mem_of_mem_head? hy)
            simp only [SegRel, secSeg]; refine ⟨hylo.symm, by linarith, by linarith, by linarith⟩
          · subst heq
            rw [bandSegs_eq_nil] at hy; simp at hy; subst hy
            simp only [SegRel, secSeg, topSeg]; refine ⟨trivial, by linarith, by linarith, by linarith⟩
      · intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · simp [secSeg]
        · rw [(hbm s hs).1]; simp
      · intro s hs hk
        simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | hs | rfl
        · simp [secSeg]
        · rw [(hbm s hs).1] at hk; cases hk
        · simp [topSeg] at hk
      · intro s hs hk
        simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | hs | rfl
        · simp [secSeg] at hk
        · obtain ⟨_, h1, h2, h3, h4, h5, h6⟩ := hbm s hs
          refine ⟨h1, h2, h3, h4, h5, h6, ?_, Or.inr (by simpa using h1)⟩
          intro z hz; simp at hz; subst hz
          rw [abs_of_nonneg (by linarith)]; linarith
        · simp [topSeg] at hk
      · intro s hs
        simp only [List.mem_cons, List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | hs | rfl
        · simp [secSeg]
        · obtain ⟨_, h1, h2, _⟩ := hbm s hs; linarith
        · simp [topSeg]; linarith
  | cons v' vs ih =>
      intro hch hlast
      rw [List.isChain_cons_cons] at hch
      obtain ⟨hvv', hch'⟩ := hch
      have hlast' : (v' :: vs).getLast (by simp) + w ≤ T := by
        simpa [List.getLast_cons] using hlast
      obtain ⟨ihc, ihh, ⟨L, hL, hLtop⟩, ihsec, ihband, ihβ⟩ := ih v' hch' hlast'
      have hab : v + w ≤ v' - w := by linarith
      have hab' : v + w < v' - w := by linarith
      have hbm := bandSegs_mem hab hℓ
      rw [colSegs_cons]; simp only
      refine ⟨?_, rfl, ⟨secSeg w v :: (bandSegs (v + w) (v' - w) ℓ ++ L), by rw [hL]; simp, ?_⟩,
        ?_, ?_, ?_⟩
      · refine List.IsChain.cons ?_ ?_
        · refine List.IsChain.append (bandSegs_chain _ _ _ hab hℓ) ihc ?_
          intro x hx y hy
          rw [ihh] at hy; simp at hy; subst hy
          have hxm := hbm x (List.mem_of_getLast? hx)
          have hxhi := bandSegs_last x hx
          simp only [SegRel, secSeg]; refine ⟨hxhi, by linarith, by linarith, by linarith⟩
        · intro y hy
          have hne := bandSegs_ne_nil hab' hℓ
          rw [List.head?_append_of_ne_nil _ hne] at hy
          have hylo := bandSegs_head y hy
          have hym := hbm y (List.mem_of_mem_head? hy)
          simp only [SegRel, secSeg]; refine ⟨hylo.symm, by linarith, by linarith, by linarith⟩
      · intro s hs
        simp only [List.mem_cons, List.mem_append] at hs
        rcases hs with rfl | hs | hs
        · simp [secSeg]
        · rw [(hbm s hs).1]; simp
        · exact hLtop s hs
      · intro s hs hk
        simp only [List.mem_cons, List.mem_append] at hs
        rcases hs with rfl | hs | hs
        · simp [secSeg]
        · rw [(hbm s hs).1] at hk; cases hk
        · obtain ⟨h1, h2, h3⟩ := ihsec s hs hk
          exact ⟨List.mem_cons_of_mem _ h1, h2, h3⟩
      · -- every value of the tail is at least `v'`
        have htail : ∀ z ∈ v' :: vs, v' ≤ z := by
          have hle : List.IsChain (· ≤ ·) (v' :: vs) := hch'.imp (fun a b h => by linarith)
          have hp : List.Pairwise (· ≤ ·) (v' :: vs) := List.isChain_iff_pairwise.mp hle
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · exact le_rfl
          · exact List.rel_of_pairwise_cons hp hz
        intro s hs hk
        simp only [List.mem_cons, List.mem_append] at hs
        rcases hs with rfl | hs | hs
        · simp [secSeg] at hk
        · obtain ⟨_, h1, h2, h3, h4, h5, h6⟩ := hbm s hs
          have hlt := htail _ (List.getLast_mem (l := v' :: vs) (by simp))
          have hgl : (v :: v' :: vs).getLast (by simp) = (v' :: vs).getLast (by simp) :=
            List.getLast_cons (by simp)
          refine ⟨h1, h2, h3, by linarith, h5, h6, ?_, Or.inl (by rw [hgl]; linarith)⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · rw [abs_of_nonneg (by linarith)]; linarith
          · have := htail z hz
            rw [abs_of_nonpos (by linarith)]; linarith
        · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ihband s hs hk
          have hgl : (v :: v' :: vs).getLast (by simp) = (v' :: vs).getLast (by simp) :=
            List.getLast_cons (by simp)
          refine ⟨by linarith, h2, h3, h4, h5, h6, ?_, by rw [hgl]; exact h8⟩
          intro z hz
          rcases List.mem_cons.mp hz with rfl | hz
          · rw [abs_of_nonneg (by linarith)]; linarith [h7 v' (by simp)]
          · exact h7 z hz
      · intro s hs
        simp only [List.mem_cons, List.mem_append] at hs
        rcases hs with rfl | hs | hs
        · simp [secSeg]
        · obtain ⟨_, h1, h2, _⟩ := hbm s hs; linarith
        · linarith [ihβ s hs]

end Persistence
end CRNT
