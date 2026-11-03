import CRNT.Persistence.LevelValidity
import CRNT.Persistence.SortReduction

/-!
# Level packages and tail-block bookkeeping

`LevelPack m Hk B` bundles the output of `level_validity`.  For a point `x : Fin n → ℝ`, the
level-`m` block is the tail `x (n-1-m), …, x (n-1)`, read as `tailZ n m x : ℕ → ℝ` (padded by
`1`).  `levelNormal` is the facet normal of a path placed on that block; `fdot_levelNormal`
expresses its dot product through `val`, and `sum_split_tail` splits a sum over `Fin n` into the
head and the block.

Nothing here is an axiom or a `sorry`.
-/

namespace CRNT
namespace Persistence

open Finset BTree Real

/-- The output of `level_validity`, as data. -/
structure LevelPack (m : ℕ) (Hk : List (ℕ → ℝ)) (B : ℝ) where
  t : BTree m
  ρ0 : ℝ
  κ : ℝ
  s₀ : ℝ
  hρ0 : 0 < ρ0
  hWF : WF t 1 ρ0
  hGP : GapsPos (B + 3) t
  hκ : 0 < κ
  hs₀ : 0 < s₀
  hs₀' : s₀ < 1 / 4
  hpD : ∀ s, 0 < s → s < s₀ → ∀ P, IsPath t P → -s ≤ pathD s t P
  hvalid : ∀ s, 0 < s → s < s₀ → ∀ c, s / 2 ≤ c → c ≤ s →
    ∀ z : ℕ → ℝ, (∀ i, 0 < z i) → (∀ i, i < m → z (i + 1) ≤ z i) → z 0 ^ B ≤ z m →
    (∀ P', IsPath t P' → c ≤ z 0 + BTree.val s t P' (fun l => z (l + 1))) →
    ∀ P, IsPath t P → z 0 + BTree.val s t P (fun l => z (l + 1)) = c →
    z 0 ≤ 2 * s ∧ ∀ h ∈ Hk, normalDot m t P h < 0 →
      κ * (-log (z 0)) ≤ ∑ i ∈ range (m + 1), h i * log (z i)

theorem exists_levelPack (m : ℕ) (Hk : List (ℕ → ℝ)) (B : ℝ) (hB : 1 ≤ B) :
    Nonempty (LevelPack m Hk B) := by
  obtain ⟨t, ρ0, hρ0, hWF, hGP, κ, hκ, s₀, hs₀, hs₀', hpD, hvalid⟩ := level_validity m Hk B hB
  exact ⟨⟨t, ρ0, κ, s₀, hρ0, hWF, hGP, hκ, hs₀, hs₀', hpD, hvalid⟩⟩

/-- A chosen package for a box at least `1`. -/
noncomputable def thePack (m : ℕ) (Hk : List (ℕ → ℝ)) (B : ℝ) : LevelPack m Hk (max B 1) :=
  Classical.choice (exists_levelPack m Hk (max B 1) (le_max_right _ _))

variable {n : ℕ}

/-- Extension of a `Fin n`-indexed vector by zero. -/
noncomputable def extZ (f : Fin n → ℝ) (q : ℕ) : ℝ := if h : q < n then f ⟨q, h⟩ else 0

/-- The level-`m` block of `x`, padded by `1`. -/
noncomputable def tailZ (n m : ℕ) (x : Fin n → ℝ) (i : ℕ) : ℝ :=
  if h : n - 1 - m + i < n then x ⟨n - 1 - m + i, h⟩ else 1

/-- The restriction of a vector to the level-`m` block, padded by `0`. -/
noncomputable def restr (n m : ℕ) (h : Fin n → ℝ) (i : ℕ) : ℝ :=
  if hi : n - 1 - m + i < n then h ⟨n - 1 - m + i, hi⟩ else 0

/-- The facet normal of a path on the level-`m` block. -/
noncomputable def levelNormal (n m : ℕ) {d : ℕ} (t : BTree d) (P : List ℕ) : Fin n → ℝ :=
  fun q => if q.val < n - 1 - m then 0 else if q.val = n - 1 - m then 1
    else leafB t 0 (fun _ => 1) P (q.val - (n - 1 - m) - 1)

theorem sum_fin_eq_range (f : Fin n → ℝ) : ∑ q, f q = ∑ q ∈ range n, extZ f q := by
  rw [← Fin.sum_univ_eq_sum_range (fun q => extZ f q)]
  refine Fintype.sum_congr _ _ fun q => ?_
  simp [extZ, q.isLt]

theorem sum_split_tail (m : ℕ) (hm : m < n) (f : Fin n → ℝ) :
    ∑ q, f q = ∑ q ∈ range (n - 1 - m), extZ f q + ∑ i ∈ range (m + 1), extZ f (n - 1 - m + i) := by
  rw [sum_fin_eq_range, show range n = range ((n - 1 - m) + (m + 1)) from by congr 1; omega,
    Finset.sum_range_add]

theorem extZ_tail (m : ℕ) (x : Fin n → ℝ) (i : ℕ) (hi : i ≤ m) (hm : m < n) :
    extZ x (n - 1 - m + i) = tailZ n m x i := by
  simp [extZ, tailZ, show n - 1 - m + i < n by omega]

/-- The dot product of a level normal. -/
theorem fdot_levelNormal (m : ℕ) (hm : m < n) {d : ℕ} (t : BTree d) (hd : d = m) (P : List ℕ)
    (x : Fin n → ℝ) :
    fdot (levelNormal n m t P) x =
      tailZ n m x 0 + ∑ l ∈ range m, leafB t 0 (fun _ => 1) P l * tailZ n m x (l + 1) := by
  unfold fdot
  rw [sum_split_tail m hm]
  have h1 : ∑ q ∈ range (n - 1 - m), extZ (fun q => levelNormal n m t P q * x q) q = 0 := by
    refine sum_eq_zero fun q hq => ?_
    simp at hq
    simp [extZ, levelNormal, show q < n by omega, hq]
  rw [h1, zero_add, sum_range_succ']
  have h2 : extZ (fun q => levelNormal n m t P q * x q) (n - 1 - m + 0) = tailZ n m x 0 := by
    simp [extZ, levelNormal, tailZ, show n - 1 - m < n by omega]
  rw [h2, add_comm]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  simp at hl
  have hlt : n - 1 - m + (l + 1) < n := by omega
  simp only [extZ, levelNormal, tailZ, dif_pos hlt]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2; omega

theorem fdot_levelNormal_h (m : ℕ) (hm : m < n) {d : ℕ} (t : BTree d) (hd : d = m) (P : List ℕ)
    (h : Fin n → ℝ) :
    fdot (levelNormal n m t P) h = normalDot m t P (restr n m h) := by
  unfold fdot normalDot
  rw [sum_split_tail m hm]
  have h1 : ∑ q ∈ range (n - 1 - m), extZ (fun q => levelNormal n m t P q * h q) q = 0 := by
    refine sum_eq_zero fun q hq => ?_
    simp at hq
    simp [extZ, levelNormal, show q < n by omega, hq]
  rw [h1, zero_add, sum_range_succ']
  have h2 : extZ (fun q => levelNormal n m t P q * h q) (n - 1 - m + 0) = restr n m h 0 := by
    simp [extZ, levelNormal, restr, show n - 1 - m < n by omega]
  rw [h2, add_comm]
  congr 1
  refine sum_congr rfl fun l hl => ?_
  simp at hl
  have hlt : n - 1 - m + (l + 1) < n := by omega
  simp only [extZ, levelNormal, restr, dif_pos hlt]
  rw [if_neg (by omega), if_neg (by omega)]
  congr 2; omega

theorem sum_log_split (m : ℕ) (hm : m < n) (h x : Fin n → ℝ) :
    ∑ q, h q * log (x q) = ∑ q ∈ range (n - 1 - m), extZ (fun q => h q * log (x q)) q +
      ∑ i ∈ range (m + 1), restr n m h i * log (tailZ n m x i) := by
  rw [sum_split_tail m hm]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  simp at hi
  have hlt : n - 1 - m + i < n := by omega
  simp [extZ, restr, tailZ, hlt]

end Persistence
end CRNT
