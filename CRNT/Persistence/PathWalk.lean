import CRNT.Persistence.Blueprint

/-!
# Walking a minimizing path through the blueprint

`walk` combines the envelope localization (`Realized`), well-formedness, properness and the leaf
property along a single full path: given conversion rules from tail sums to log-ratio coordinates
`p`, every node on the path is non-top, the leaf property holds for the accumulated basepoint and
radius, and every coordinate `p l` is within `radius + η₁` of the basepoint.

Also: the enumeration `paths` of all full paths, the accumulated basepoint `leafB`, radius
`leafR` and constant `pathD`, and the affine form of `val`.  Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset BTree

/-- All full paths. -/
def paths : {m : ℕ} → BTree m → List (List ℕ)
  | _, .leaf => [[]]
  | _, .node n _ _ _ sub => (List.range n).flatMap fun i => (paths (sub i)).map (i :: ·)

theorem mem_paths_iff : ∀ {m : ℕ} (t : BTree m) (P : List ℕ), P ∈ paths t ↔ IsPath t P
  | _, .leaf, P => by simp [paths, IsPath]
  | _, .node n β lo hi sub, P => by
      simp only [paths, List.mem_flatMap, List.mem_range, List.mem_map, IsPath]
      constructor
      · rintro ⟨i, hi', rest, hrest, rfl⟩
        exact ⟨i, rest, rfl, hi', (mem_paths_iff (sub i) rest).mp hrest⟩
      · rintro ⟨i, rest, rfl, hi', hrest⟩
        exact ⟨i, hi', rest, (mem_paths_iff (sub i) rest).mpr hrest, rfl⟩

/-- Accumulated basepoint (positions `j, j+1, …` are overwritten along the path). -/
def leafB : {d : ℕ} → BTree d → ℕ → (ℕ → ℝ) → List ℕ → (ℕ → ℝ)
  | _, .leaf, _, b, _ => b
  | _, .node _ _ _ _ _, _, b, [] => b
  | _, .node _ β _ _ sub, j, b, i :: rest => leafB (sub i) (j + 1) (Function.update b j (β i)) rest

/-- Accumulated radius. -/
noncomputable def leafR : {d : ℕ} → BTree d → ℝ → List ℕ → ℝ
  | _, .leaf, ρ, _ => ρ
  | _, .node _ _ _ _ _, ρ, [] => ρ
  | _, .node n β _ hi sub, ρ, i :: rest => leafR (sub i) (nodeRad ρ n β hi i) rest

/-- Sum of the column constants along a path. -/
noncomputable def pathD (ε : ℝ) : {d : ℕ} → BTree d → List ℕ → ℝ
  | _, .leaf, _ => 0
  | _, .node _ _ _ _ _, [] => 0
  | _, .node _ β _ hi sub, i :: rest => colD ε β hi i + pathD ε (sub i) rest

theorem leafB_apply_lt : ∀ {d : ℕ} (t : BTree d) (j : ℕ) (b : ℕ → ℝ) (P : List ℕ) (l : ℕ),
    l < j → leafB t j b P l = b l
  | _, .leaf, _, _, _, _, _ => rfl
  | _, .node _ _ _ _ _, _, _, [], _, _ => rfl
  | _, .node _ β _ _ sub, j, b, i :: rest, l, hl => by
      simp only [leafB]
      rw [leafB_apply_lt (sub i) (j + 1) _ rest l (by omega), Function.update_of_ne (by omega)]

theorem leafB_apply_self {d : ℕ} (n : ℕ) (β lo hi : ℕ → ℝ) (sub : ℕ → BTree d) (j : ℕ)
    (b : ℕ → ℝ) (i : ℕ) (rest : List ℕ) :
    leafB (BTree.node n β lo hi sub) j b (i :: rest) j = β i := by
  simp only [leafB]
  rw [leafB_apply_lt (sub i) (j + 1) _ rest j (by omega), Function.update_self]

/-- `val` is affine: constants plus basepoint coordinates times `y`. -/
theorem val_eq (ε : ℝ) : ∀ {d : ℕ} (t : BTree d) (j : ℕ) (b : ℕ → ℝ) (P : List ℕ),
    IsPath t P → ∀ y : ℕ → ℝ,
    BTree.val ε t P y = pathD ε t P + ∑ l ∈ range d, leafB t j b P (j + l) * y l
  | _, .leaf, _, _, _, _, y => by simp [BTree.val, pathD]
  | d + 1, .node n β lo hi sub, j, b, P, hP, y => by
      obtain ⟨i, rest, rfl, _, hrest⟩ := hP
      simp only [BTree.val, pathD]
      rw [val_eq ε (sub i) (j + 1) (Function.update b j (β i)) rest hrest, sum_range_succ']
      have h0 : leafB (BTree.node n β lo hi sub) j b (i :: rest) (j + 0) = β i := by
        exact leafB_apply_self n β lo hi sub j b i rest
      have hs : ∀ l ∈ range d, leafB (BTree.node n β lo hi sub) j b (i :: rest) (j + (l + 1)) *
          y (l + 1) = leafB (sub i) (j + 1) (Function.update b j (β i)) rest (j + 1 + l) *
          y (l + 1) := by
        intro l _; simp only [leafB]; congr 2; ring
      rw [h0, sum_congr rfl hs]; ring

theorem colD_nonpos {ε : ℝ} (hε : 0 ≤ ε) {n : ℕ} {β hi : ℕ → ℝ}
    (hmono : ∀ i, i + 1 < n → β i ≤ hi i ∧ hi i ≤ β (i + 1)) {i : ℕ} (hi' : i < n) :
    colD ε β hi i ≤ 0 := by
  unfold colD
  rw [neg_nonpos]
  refine sum_nonneg fun i' hi'' => mul_nonneg ?_ (Real.rpow_nonneg hε _)
  have := hmono i' (by simp at hi''; omega)
  linarith [this.1, this.2]

theorem pathD_nonpos {ε : ℝ} (hε : 0 ≤ ε) : ∀ {d : ℕ} (t : BTree d) (βp ρp : ℝ),
    WF t βp ρp → ∀ P, IsPath t P → pathD ε t P ≤ 0
  | _, .leaf, _, _, _, _, _ => le_rfl
  | _, .node n β lo hi sub, βp, ρp, h, P, hP => by
      obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
      simp only [pathD]
      have := pathD_nonpos hε (sub i) _ _ (h.2.2.2.2 i hin) rest hrest
      have := colD_nonpos hε h.2.2.1 hin
      linarith

theorem neg_absD_le_pathD (ε : ℝ) : ∀ {d : ℕ} (t : BTree d) (P : List ℕ),
    -absD ε t P ≤ pathD ε t P
  | _, .leaf, _ => by simp [absD, pathD]
  | _, .node _ _ _ _ _, [] => by simp [absD, pathD]
  | _, .node n β lo hi sub, i :: rest => by
      simp only [absD, pathD]
      have := neg_absD_le_pathD ε (sub i) rest
      have := neg_abs_le (colD ε β hi i)
      linarith

/-- Basepoint coordinates along a path are at least the parent value and nondecreasing. -/
theorem leafB_mono : ∀ {d : ℕ} (t : BTree d) (j : ℕ) (b : ℕ → ℝ) (βp ρp : ℝ),
    WF t βp ρp → ∀ P, IsPath t P →
    (d ≠ 0 → βp ≤ leafB t j b P j) ∧
    ∀ l, j ≤ l → l + 1 < j + d → leafB t j b P l ≤ leafB t j b P (l + 1)
  | _, .leaf, _, _, _, _, _, _, _ => ⟨fun h => absurd rfl h, fun l h1 h2 => by omega⟩
  | d + 1, .node n β lo hi sub, j, b, βp, ρp, h, P, hP => by
      obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
      have hβi : βp ≤ β i := by
        have : ∀ k, k < n → βp ≤ β k := by
          intro k hk
          induction k with
          | zero => exact h.2.1.symm.le
          | succ k ihk =>
              have := h.2.2.1 k (by omega)
              exact le_trans (ihk (by omega)) (le_trans this.1 this.2)
        exact this i hin
      have ih := leafB_mono (sub i) (j + 1) (Function.update b j (β i)) _ _ (h.2.2.2.2 i hin)
        rest hrest
      refine ⟨fun _ => by rw [leafB_apply_self]; exact hβi, fun l hl1 hl2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hl1 with rfl | hlt
      · rw [leafB_apply_self]
        have hd : d ≠ 0 := by omega
        have := ih.1 hd
        simpa only [leafB] using this
      · simp only [leafB]
        exact ih.2 l (by omega) (by omega)

/-- On the wall path, the constants vanish and every basepoint coordinate is the parent value. -/
theorem wallPath_facts (ε : ℝ) : ∀ {d : ℕ} (t : BTree d) (j : ℕ) (b : ℕ → ℝ) (βp ρp : ℝ),
    WF t βp ρp → pathD ε t (wallPath t) = 0 ∧
    ∀ l, j ≤ l → l < j + d → leafB t j b (wallPath t) l = βp
  | _, .leaf, _, _, _, _, _ => ⟨rfl, fun l h1 h2 => by omega⟩
  | d + 1, .node n β lo hi sub, j, b, βp, ρp, h => by
      have ih := wallPath_facts ε (sub 0) (j + 1) (Function.update b j (β 0)) _ _ (h.2.2.2.2 0 h.1)
      refine ⟨?_, fun l hl1 hl2 => ?_⟩
      · simp only [wallPath, pathD, colD_zero, ih.1, add_zero]
      · rcases Nat.eq_or_lt_of_le hl1 with rfl | hlt
        · simp only [wallPath]; rw [leafB_apply_self, h.2.1]
        · simp only [wallPath, leafB]; rw [ih.2 l (by omega) (by omega), h.2.1]

/-! ### The walk -/

theorem walk {ε η1 B : ℝ} (hη1 : η1 < 1 / 2) {p : ℕ → ℝ} {Q : (ℕ → ℝ) → ℝ → Prop} {M : ℕ}
    {Y : ℕ → ℝ}
    (hup : ∀ l h, l < M → 0 ≤ h → h ≤ B + 3 →
      ε ^ h ≤ 2 * ysum (M - l) (fun i => Y (l + i)) → p l ≤ h + η1)
    (hdown : ∀ l h, l < M → 0 ≤ h → h ≤ B + 3 →
      ysum (M - l) (fun i => Y (l + i)) ≤ 2 * ε ^ h → h - η1 ≤ p l)
    (hch : ∀ l, l + 1 < M → p l ≤ p (l + 1))
    (hbox : ∀ l, l < M → p l ≤ B) :
    ∀ {d : ℕ} (t : BTree d) (j : ℕ) (b : ℕ → ℝ) (βp ρp : ℝ) (P : List ℕ),
    j + d = M → WF t βp ρp → Proper B t → GapsPos (B + 3) t → LeafProp Q j b ρp t →
    IsPath t P → Realized ε t P (fun i => Y (j + i)) →
    (d ≠ 0 → βp - ρp - η1 ≤ p j) →
    Q (leafB t j b P) (leafR t ρp P) ∧ ρp ≤ leafR t ρp P ∧
    ∀ l, j ≤ l → l < M → |p l - leafB t j b P l| ≤ leafR t ρp P + η1
  | _, .leaf, j, b, βp, ρp, P, hjM, _, _, _, hQ, hP, _, _ => by
      have hP' : P = [] := hP
      subst hP'
      exact ⟨hQ, le_rfl, fun l h1 h2 => by omega⟩
  | d + 1, .node n β lo hi sub, j, b, βp, ρp, P, hjM, hWF, hpr, hgp, hQ, hP, hR, hprev => by
      obtain ⟨i, rest, rfl, hin, hrest⟩ := hP
      obtain ⟨hRup, hRdown, hRsub⟩ := hR
      have hjlt : j < M := by omega
      have hMj : M - j = d + 1 := by omega
      set ρi := nodeRad ρp n β hi i with hρi
      have hβr : ∀ k, k < n → 0 ≤ β k ∧ β k ≤ B + 3 := hgp.1
      -- the node is not the last one
      have hnotlast : i + 1 < n := by
        by_contra hcon
        have hilast : i = n - 1 := by omega
        have h2 : 2 ≤ n := hpr.1
        have hipos : 0 < i := by omega
        have hu := hRdown hipos
        rw [← hMj] at hu
        have hord := hWF.2.2.1 (i - 1) (by omega)
        have hi1 : i - 1 + 1 = i := by omega
        rw [hi1] at hord
        have hb := hβr (i - 1) (by omega)
        have hb' := hβr i hin
        have := hdown j (hi (i - 1)) hjlt (by linarith [hord.1]) (by linarith [hord.2]) hu
        have hpr2 : B + 1 / 2 ≤ hi (n - 2) := hpr.2.1
        rw [show n - 2 = i - 1 by omega] at hpr2
        linarith [hbox j hjlt]
      -- the two-sided bound at level `j`
      have hupper : p j ≤ β i + ρi + η1 := by
        have hu := hRup hnotlast
        rw [← hMj] at hu
        have hord := hWF.2.2.1 i hnotlast
        have hb := hβr i hin
        have hb' := hβr (i + 1) hnotlast
        have := hup j (hi i) hjlt (by linarith [hord.1]) (by linarith [hord.2]) hu
        have := nodeRad_ge_hi (ρp := ρp) (β := β) (hi := hi) hnotlast
        linarith
      have hlower : β i - ρi - η1 ≤ p j := by
        rcases Nat.eq_zero_or_pos i with h0 | hpos
        · subst h0
          have := hprev (by omega)
          rw [← hWF.2.1] at this
          have := le_nodeRad ρp n β hi 0
          linarith
        · have hu := hRdown hpos
          rw [← hMj] at hu
          have hord := hWF.2.2.1 (i - 1) (by omega)
          have hi1 : i - 1 + 1 = i := by omega
          rw [hi1] at hord
          have hb := hβr (i - 1) (by omega)
          have hb' := hβr i hin
          have := hdown j (hi (i - 1)) hjlt (by linarith [hord.1]) (by linarith [hord.2]) hu
          have := nodeRad_ge_lo (ρp := ρp) (n := n) (β := β) (hi := hi) hpos
          linarith
      -- recurse
      have hRsub' : Realized ε (sub i) rest (fun i' => Y (j + 1 + i')) := by
        have : (fun i' => (fun i => Y (j + i)) (i' + 1)) = fun i' => Y (j + 1 + i') := by
          funext i'; congr 1; ring
        rw [← this]; exact hRsub
      have ih := walk hη1 hup hdown hch hbox (sub i) (j + 1) (Function.update b j (β i)) (β i) ρi
        rest (by omega) (hWF.2.2.2.2 i hin) (hpr.2.2 i hnotlast) (hgp.2.2 i hin)
        (hQ i hnotlast) hrest hRsub' (fun hd => by
          have := hch j (by omega); linarith)
      refine ⟨ih.1, le_trans (le_nodeRad _ _ _ _ _) ih.2.1, fun l hl1 hl2 => ?_⟩
      rcases Nat.eq_or_lt_of_le hl1 with rfl | hlt
      · rw [leafB_apply_self]
        have hlr : leafR (BTree.node n β lo hi sub) ρp (i :: rest) = leafR (sub i) ρi rest := rfl
        rw [hlr, abs_le]; constructor <;> linarith [ih.2.1]
      · exact ih.2.2 l (by omega) hl2

end Persistence
end CRNT
