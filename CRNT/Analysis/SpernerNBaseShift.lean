import CRNT.Analysis.SpernerNIncidence

/-!
# Base-change facet adjacency (the extreme-index Kuhn neighbour)

`SpernerNIncidence` handles facets dropping an *interior-chain* vertex (`0 < m < n`) via the
adjacent-transposition `flipCell`, which keeps the base and swaps two permutation entries. The
*extreme* facets — dropping vertex `0` — are different: dropping vertex `0` of a cell yields the same
facet as dropping the *last* vertex of a neighbouring cell with a **shifted base**. This module
builds that neighbour, the `shiftCell`.

For a cell `c : Cell (n+1) N` with base `b` and permutation `σ`, the neighbour across the facet
`facetVerts c 0` (which drops `v₀ = b`, leaving `{v₁, …, v_{n+1}}`) is `shiftCell c`:

* base `b' = v₁ = b + d(σ 0)` (one step along the first simple root; this lowers the weighted sum by
  one);
* permutation `σ' = σ ∘ finRotate (n+1)` (the left-rotation `j ↦ σ(j+1)`, wrapping `σ(last) ↦ σ 0`).

Then `shiftCell c` shares its non-last vertices with `c.vertex 1, …, c.vertex (n+1)`, and its single
new vertex is `v₁ + e₀ − e_last` (the reflection of the dropped corner). It exists exactly when that
new vertex stays in the nonnegative orthant — the honest interior condition `ShiftValid`. The
neighbour shares the facet (`shiftCell_facet`) and is distinct (`shiftCell_ne`).

Depends on: `CRNT.Analysis.SpernerNIncidence`.
-/

namespace CRNT.Analysis.SpernerN

open scoped BigOperators
open Finset

variable {n N : ℕ}

/-! ### The all-roots vector -/

/-- **The sum of all simple roots telescopes to `e₀ − e_last`.** -/
theorem sum_root (i : Fin (n + 2)) :
    ∑ j : Fin (n + 1), root j i
      = (if i = 0 then (1 : ℤ) else 0) - (if i = Fin.last (n + 1) then 1 else 0) := by
  have hfun : ∀ j : Fin (n + 1), root j i
      = (fun t : ℕ => if (i : ℕ) = t then (1 : ℤ) else 0) (j : ℕ)
        - (fun t : ℕ => if (i : ℕ) = t then (1 : ℤ) else 0) ((j : ℕ) + 1) := by
    intro j
    simp only [root, Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]
  rw [Finset.sum_congr rfl (fun j _ => hfun j),
    Fin.sum_univ_eq_sum_range (fun t => (if (i : ℕ) = t then (1 : ℤ) else 0)
      - (if (i : ℕ) = t + 1 then (1 : ℤ) else 0)) (n + 1),
    Finset.sum_range_sub' (fun t => if (i : ℕ) = t then (1 : ℤ) else 0) (n + 1)]
  simp only [Fin.ext_iff, Fin.val_zero, Fin.val_last]

/-! ### The shift permutation -/

/-- The **shift permutation**: the left-rotation `σ' = σ ∘ finRotate (n+1)`, i.e. `σ'(j) = σ(j+1)`
(wrapping `σ(last) ↦ σ 0`). -/
def shiftPerm (σ : Equiv.Perm (Fin (n + 1))) : Equiv.Perm (Fin (n + 1)) :=
  σ * finRotate (n + 1)

theorem shiftPerm_apply (σ : Equiv.Perm (Fin (n + 1))) (l : Fin (n + 1)) :
    shiftPerm σ l = σ (l + 1) := by
  simp only [shiftPerm, Equiv.Perm.mul_apply, finRotate_apply]

/-- `voff σ 1` is the first simple root `d(σ 0)`. -/
theorem voff_one (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2)) :
    voff σ 1 i = root (σ 0) i := by
  have hfilter : (univ.filter (fun l : Fin (n + 1) => (l : ℕ) < ((1 : Fin (n + 2)) : ℕ)))
      = {(0 : Fin (n + 1))} := by
    ext l
    simp [Nat.lt_one_iff]
  simp only [voff, hfilter, Finset.sum_singleton]

/-- `· + 1` on `Fin (n+1)` is injective (it is `finRotate (n+1)`). -/
theorem add_one_injective : Function.Injective (fun l : Fin (n + 1) => l + 1) := by
  have h : (fun l : Fin (n + 1) => l + 1) = ⇑(finRotate (n + 1)) := by
    funext l; exact (finRotate_apply l).symm
  rw [h]; exact (finRotate (n + 1)).injective

/-! ### The shift-permutation offset identities -/

/-- **Last vertex.** The offset at the last vertex is the sum of all roots, for *any* permutation
(the full prefix reindexes by the permutation). -/
theorem voff_last_eq_sum_root (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 2)) :
    voff σ (Fin.last (n + 1)) i = ∑ j : Fin (n + 1), root j i := by
  rw [voff]
  have huniv : (univ.filter (fun l : Fin (n + 1) => (l : ℕ) < ((Fin.last (n + 1)) : ℕ))) = univ := by
    ext l
    simp only [mem_filter, mem_univ, true_and, Fin.val_last, iff_true]
    exact l.isLt
  rw [huniv]
  simpa using Equiv.sum_comp σ (fun m => root m i)

/-- **Non-last vertices.** For `k ≠ last` the shifted offset is the original offset of the next
vertex, less the first root. -/
theorem voff_shiftPerm_lt (σ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1)) (i : Fin (n + 2)) :
    voff (shiftPerm σ) k i = voff σ (k + 1) i - root (σ 0) i := by
  have hkn : (k : ℕ) ≤ n := by
    have h1 := k.isLt
    have h2 : (k : ℕ) ≠ n + 1 := fun hc => hk (Fin.ext (by rw [Fin.val_last]; exact hc))
    omega
  have hkval : ((k + 1 : Fin (n + 2)) : ℕ) = (k : ℕ) + 1 := by
    rw [Fin.val_add_one, if_neg hk]
  have hL : voff (shiftPerm σ) k i
      = ∑ l ∈ univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ)), root (σ (l + 1)) i := by
    simp only [voff]
    exact Finset.sum_congr rfl (fun l _ => by rw [shiftPerm_apply])
  have hsplit : (univ.filter (fun l' : Fin (n + 1) => (l' : ℕ) < ((k + 1 : Fin (n + 2)) : ℕ)))
      = insert (0 : Fin (n + 1))
          ((univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ))).image (· + 1)) := by
    rw [hkval]
    ext l'
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_image]
    constructor
    · intro hl'
      rcases Nat.eq_zero_or_pos (l' : ℕ) with h0 | hpos
      · exact Or.inl (Fin.ext (by rw [h0, Fin.val_zero]))
      · refine Or.inr ⟨⟨(l' : ℕ) - 1, by omega⟩, by simp only; omega, ?_⟩
        apply Fin.ext
        have hlne : (⟨(l' : ℕ) - 1, by omega⟩ : Fin (n + 1)) ≠ Fin.last n := by
          intro hc
          have hv : ((⟨(l' : ℕ) - 1, by omega⟩ : Fin (n + 1)) : ℕ) = n := by rw [hc, Fin.val_last]
          simp only at hv; omega
        rw [Fin.val_add_one, if_neg hlne]
        simp only; omega
    · rintro (rfl | ⟨l, hl, rfl⟩)
      · simp only [Fin.val_zero]; omega
      · have hlne : l ≠ Fin.last n := by
          intro hc; rw [hc, Fin.val_last] at hl; omega
        rw [Fin.val_add_one, if_neg hlne]; omega
  have h0notin : (0 : Fin (n + 1))
      ∉ (univ.filter (fun l : Fin (n + 1) => (l : ℕ) < (k : ℕ))).image (· + 1) := by
    simp only [mem_image, mem_filter, mem_univ, true_and, not_exists, not_and]
    intro l hl hc
    have hlne : l ≠ Fin.last n := by
      intro h; rw [h, Fin.val_last] at hl; omega
    have h1 : ((l + 1 : Fin (n + 1)) : ℕ) = (l : ℕ) + 1 := by rw [Fin.val_add_one, if_neg hlne]
    have h2 : ((l + 1 : Fin (n + 1)) : ℕ) = 0 := by rw [hc, Fin.val_zero]
    omega
  rw [hL]
  simp only [voff]
  rw [hsplit, Finset.sum_insert h0notin,
    Finset.sum_image (fun a _ b _ h => add_one_injective h)]
  ring

/-! ### The shifted cell -/

/-- **Interior condition.** The reflected new vertex `v₁ + e₀ − e_last` stays in the nonnegative
orthant. -/
def ShiftValid (c : Cell (n + 1) N) : Prop :=
  ∀ i : Fin (n + 2),
    0 ≤ ((c.vertex 1).1 i : ℤ)
      + ((if i = 0 then (1 : ℤ) else 0) - (if i = Fin.last (n + 1) then 1 else 0))

/-- **The base-change neighbour** of `c` across the facet dropping vertex `0`. Same facet, shifted
base `v₁` and rotated permutation. -/
def shiftCell (c : Cell (n + 1) N) (h : ShiftValid c) : Cell (n + 1) N where
  base := (c.vertex 1).1
  perm := shiftPerm c.perm
  sum_base := (c.vertex 1).2
  valid := by
    intro k i
    by_cases hk : k = Fin.last (n + 1)
    · subst hk
      rw [voff_last_eq_sum_root, sum_root]
      exact h i
    · rw [voff_shiftPerm_lt c.perm k hk i]
      have hb : ((c.vertex 1).1 i : ℤ) = (c.base i : ℤ) + root (c.perm 0) i := by
        rw [Cell.vertex_val, voff_one]
      rw [hb]
      have hval := c.valid (k + 1) i
      have heq : (c.base i : ℤ) + root (c.perm 0) i + (voff c.perm (k + 1) i - root (c.perm 0) i)
          = (c.base i : ℤ) + voff c.perm (k + 1) i := by ring
      rw [heq]; exact hval

/-- **Non-last vertices of the shift agree with `c.vertex (k+1)`.** -/
theorem shiftCell_vertex (c : Cell (n + 1) N) (h : ShiftValid c) (k : Fin (n + 2))
    (hk : k ≠ Fin.last (n + 1)) :
    (shiftCell c h).vertex k = c.vertex (k + 1) := by
  apply Pt.ext
  funext i
  have hint : (((shiftCell c h).vertex k).1 i : ℤ) = ((c.vertex (k + 1)).1 i : ℤ) := by
    rw [Cell.vertex_val, Cell.vertex_val]
    show ((c.vertex 1).1 i : ℤ) + voff (shiftPerm c.perm) k i = (c.base i : ℤ) + voff c.perm (k + 1) i
    rw [voff_shiftPerm_lt c.perm k hk i, Cell.vertex_val, voff_one]
    ring
  exact_mod_cast hint

/-- **The shift shares the facet** dropping vertex `0` (it appears there as the facet dropping the
last vertex). -/
theorem shiftCell_facet (c : Cell (n + 1) N) (h : ShiftValid c) :
    facetVerts (shiftCell c h) (Fin.last (n + 1)) = facetVerts c 0 := by
  unfold facetVerts
  have hkey : (univ.erase (Fin.last (n + 1))).image (shiftCell c h).vertex
      = (univ.erase (Fin.last (n + 1))).image (fun k => c.vertex (k + 1)) := by
    apply Finset.image_congr
    intro k hk
    rw [Finset.mem_coe, mem_erase] at hk
    exact shiftCell_vertex c h k hk.1
  rw [hkey, show (fun k : Fin (n + 2) => c.vertex (k + 1)) = c.vertex ∘ (fun k => k + 1) from rfl,
    ← Finset.image_image]
  congr 1
  ext l
  simp only [mem_image, mem_erase, mem_univ, and_true]
  constructor
  · rintro ⟨k, hkne, rfl⟩
    have h1 : ((k + 1 : Fin (n + 2)) : ℕ) = (k : ℕ) + 1 := by rw [Fin.val_add_one, if_neg hkne]
    intro hc
    have h2 : ((k + 1 : Fin (n + 2)) : ℕ) = 0 := by rw [hc, Fin.val_zero]
    omega
  · intro hl
    refine ⟨l - 1, ?_, sub_add_cancel l 1⟩
    intro hc
    have hv : ((l - 1 : Fin (n + 2)) : ℕ) = n + 1 := by rw [hc, Fin.val_last]
    rw [Fin.coe_sub_one, if_neg hl] at hv
    have := l.isLt
    omega

/-- **The shift is a distinct cell.** -/
theorem shiftCell_ne (c : Cell (n + 1) N) (h : ShiftValid c) : shiftCell c h ≠ c := by
  intro heq
  have hbase : ((c.vertex 1).1) = c.base := congrArg Cell.base heq
  have hb := congrFun hbase ((c.perm 0).castSucc)
  have hbi : ((c.vertex 1).1 ((c.perm 0).castSucc) : ℤ) = (c.base ((c.perm 0).castSucc) : ℤ) := by
    exact_mod_cast hb
  rw [Cell.vertex_val, voff_one] at hbi
  have hroot : root (c.perm 0) ((c.perm 0).castSucc) = 0 := by linarith
  have hne : ¬ ((c.perm 0).castSucc = (c.perm 0).succ) := by
    rw [Fin.ext_iff, Fin.val_castSucc, Fin.val_succ]; omega
  rw [root, if_pos rfl, if_neg hne] at hroot
  norm_num at hroot

/-! ### Index rigidity for the extreme facet -/

/-- **Extreme index dichotomy.** A cell `c'` sharing the facet `facetVerts c 0` either also drops
vertex `0` (with the same weighted sum, forcing `c' = c`) or drops the *last* vertex (with weighted
sum one lower, the `shiftCell`). The weighted-sum argument generalizes `facet_eq_index`: here
`(n+1)·(Wb c − Wb c') = m'`, so `m' ∈ {0, last}`. -/
theorem facet0_eq_index (c c' : Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : facetVerts c 0 = facetVerts c' m') :
    (m' = 0 ∧ Wb c = Wb c') ∨ (m' = Fin.last (n + 1) ∧ Wb c' = Wb c - 1) := by
  have hs : (∑ k ∈ univ.erase (0 : Fin (n + 2)), (Wb c - (k : ℕ)))
      = ∑ k ∈ univ.erase m', (Wb c' - (k : ℕ)) := by
    rw [← facetWsum_image, ← facetWsum_image, heq]
  rw [Finset.sum_erase_eq_sub (mem_univ (0 : Fin (n + 2))), Finset.sum_erase_eq_sub (mem_univ m'),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin] at hs
  simp only [nsmul_eq_mul, Fin.val_zero, Nat.cast_zero, sub_zero] at hs
  have key : ((n : ℤ) + 1) * (Wb c - Wb c') = (m' : ℕ) := by
    push_cast at hs ⊢; ring_nf at hs ⊢; linarith
  have hpos : (0 : ℤ) < (n : ℤ) + 1 := by positivity
  have hm'lt : ((m' : ℕ) : ℤ) < (n : ℤ) + 2 := by exact_mod_cast m'.isLt
  have hm'nn : (0 : ℤ) ≤ ((m' : ℕ) : ℤ) := Int.natCast_nonneg _
  have hDnn : 0 ≤ Wb c - Wb c' := by nlinarith [key, hpos, hm'nn]
  have hDle : Wb c - Wb c' ≤ 1 := by nlinarith [key, hpos, hm'lt]
  have hcases : Wb c - Wb c' = 0 ∨ Wb c - Wb c' = 1 := by omega
  rcases hcases with hD | hD
  · left
    refine ⟨?_, by linarith [hD]⟩
    have hv : ((m' : ℕ) : ℤ) = 0 := by rw [← key, hD]; ring
    exact Fin.ext (by rw [Fin.val_zero]; exact_mod_cast hv)
  · right
    refine ⟨?_, by linarith [hD]⟩
    have hv : ((m' : ℕ) : ℤ) = (n : ℤ) + 1 := by rw [← key, hD]; ring
    exact Fin.ext (by rw [Fin.val_last]; exact_mod_cast hv)

/-- **Two permutations agreeing off a single point are equal** (the value at that point is forced as
the unique remaining image). -/
theorem perm_eq_of_eq_off_one {α : Type*} [DecidableEq α] [Fintype α]
    (σ σ' : Equiv.Perm α) (p₀ : α) (h : ∀ p, p ≠ p₀ → σ' p = σ p) : σ' = σ := by
  have hp0 : σ' p₀ = σ p₀ := by
    by_contra hne
    obtain ⟨q, hq⟩ := σ.surjective (σ' p₀)
    have hqne : q ≠ p₀ := by rintro rfl; exact hne hq.symm
    have : σ' q = σ' p₀ := by rw [h q hqne, hq]
    exact hqne (σ'.injective this)
  exact Equiv.ext (fun p => by
    by_cases hp : p = p₀
    · subst hp; exact hp0
    · exact h p hp)

/-! ### Facet rigidity for the extreme facet -/

/-- **Extreme facet incidence rigidity.** Any cell sharing the facet `facetVerts c 0` is either `c`
itself (dropping vertex `0`) or its base-change neighbour `shiftCell c` (dropping the last vertex). -/
theorem facet0_eq_imp (c c' : Cell (n + 1) N) (m' : Fin (n + 2))
    (heq : facetVerts c 0 = facetVerts c' m') :
    c' = c ∨ ∃ h : ShiftValid c, c' = shiftCell c h := by
  rcases facet0_eq_index c c' m' heq with ⟨hm', hWb⟩ | ⟨hm', hWb'⟩
  · -- `m' = 0`, same weighted sum: `c' = c`
    subst hm'
    left
    -- non-dropped vertices agree
    have halign : ∀ k : Fin (n + 2), k ≠ 0 → c'.vertex k = c.vertex k :=
      fun k hk => facet_eq_vertex_align c c' 0 heq hWb k hk
    -- permutation agrees off position `0`
    have hperm : ∀ p : Fin (n + 1), p ≠ 0 → c'.perm p = c.perm p := by
      intro p hp
      apply root_injective; funext i
      have hcs : (p.castSucc : Fin (n + 2)) ≠ 0 := by
        intro hc; apply hp
        apply Fin.ext
        have := congrArg Fin.val hc; rwa [Fin.val_castSucc, Fin.val_zero] at this
      have hsc : (p.succ : Fin (n + 2)) ≠ 0 := Fin.succ_ne_zero p
      have e := vertex_step c p i
      have e' := vertex_step c' p i
      rw [halign p.succ hsc, halign p.castSucc hcs] at e'
      linarith [e, e']
    have hpermeq : c'.perm = c.perm := perm_eq_of_eq_off_one c.perm c'.perm 0 hperm
    have hbaseeq : c'.base = c.base := by
      funext i
      have h1 : ((c'.vertex 1).1 i : ℤ) = ((c.vertex 1).1 i : ℤ) := by rw [halign 1 one_ne_zero]
      rw [Cell.vertex_val, Cell.vertex_val, voff_one, voff_one, hpermeq] at h1
      have : (c'.base i : ℤ) = (c.base i : ℤ) := by linarith
      exact_mod_cast this
    exact Cell.eq_of_base_perm hbaseeq hpermeq
  · -- `m' = last`, weighted sum one lower: `c' = shiftCell c`
    subst hm'
    -- cross-index vertex matching: `c'.vertex j = c.vertex (j+1)` for `j ≠ last`
    have hvtx : ∀ j : Fin (n + 2), j ≠ Fin.last (n + 1) → c'.vertex j = c.vertex (j + 1) := by
      intro j hj
      have hmem : c'.vertex j ∈ facetVerts c' (Fin.last (n + 1)) := by
        rw [facetVerts]; exact Finset.mem_image_of_mem _ (mem_erase.mpr ⟨hj, mem_univ j⟩)
      rw [← heq, facetVerts, mem_image] at hmem
      obtain ⟨k, hk, hkv⟩ := hmem
      have hwk : Wb c - ((k : ℕ) : ℤ) = Wb c' - ((j : ℕ) : ℤ) := by
        rw [← wsumPt_vertex, ← wsumPt_vertex, hkv]
      have hkj : (k : ℕ) = (j : ℕ) + 1 := by rw [hWb'] at hwk; omega
      have hjadd : ((j + 1 : Fin (n + 2)) : ℕ) = (j : ℕ) + 1 := by rw [Fin.val_add_one, if_neg hj]
      rw [← hkv]
      congr 1
      exact Fin.ext (by rw [hjadd]; exact hkj)
    -- the shifted base is recovered from vertex `0`
    have hbase' : ∀ i, c'.base i = (c.vertex 1).1 i := by
      intro i
      rw [← vertex_zero c' i, hvtx 0 (by
        intro hc
        have := congrArg Fin.val hc; rw [Fin.val_last, Fin.val_zero] at this; omega)]
      congr 1
    -- the new vertex is `v₁ + (e₀ − e_last)`, so `ShiftValid` holds
    have hSV : ShiftValid c := by
      intro i
      have hv := c'.valid (Fin.last (n + 1)) i
      rw [hbase' i, voff_last_eq_sum_root, sum_root] at hv
      exact hv
    refine Or.inr ⟨hSV, ?_⟩
    apply Cell.ext_of_vertex_eq
    intro k
    by_cases hk : k = Fin.last (n + 1)
    · subst hk
      apply Pt.ext; funext i
      have hc' : (((c'.vertex (Fin.last (n + 1))).1 i : ℤ))
          = ((c.vertex 1).1 i : ℤ) + ∑ j : Fin (n + 1), root j i := by
        rw [Cell.vertex_val, hbase' i, voff_last_eq_sum_root]
      have hsh : ((((shiftCell c hSV).vertex (Fin.last (n + 1))).1 i : ℤ))
          = ((c.vertex 1).1 i : ℤ) + ∑ j : Fin (n + 1), root j i := by
        rw [Cell.vertex_val]
        show ((c.vertex 1).1 i : ℤ) + voff (shiftPerm c.perm) (Fin.last (n + 1)) i = _
        rw [voff_last_eq_sum_root]
      have : (((c'.vertex (Fin.last (n + 1))).1 i : ℤ))
          = (((shiftCell c hSV).vertex (Fin.last (n + 1))).1 i : ℤ) := by rw [hc', hsh]
      exact_mod_cast this
    · rw [shiftCell_vertex c hSV k hk, hvtx k hk]

end CRNT.Analysis.SpernerN
